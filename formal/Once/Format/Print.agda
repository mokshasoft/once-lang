-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Format.Print — a module in the one canonical layout (plan 0.124 step 3).
--
-- The printer reads the parser's `Module` (the Spec's syntax: no second tree)
-- and the comments the lexer kept (`Format.Lex`). One function per syntactic
-- category; a parenthesis only where the grammar would otherwise read the text
-- differently (`Spec.Surface.Grammar`'s precedences).
--
-- Comments are anchored to WORD AND LITERAL tokens (`TWord` but `compose`,
-- `TInt`, `TFloat`): the one token sequence every canonical spelling of a
-- module keeps (plan 0.124 §6). A comment on its own line before a line that
-- starts a declaration goes before that declaration; one before an indented
-- line goes before the next anchor, in place; one after code on a line goes at
-- the end of the line of the anchor before it in its declaration (before
-- the declaration's first anchor, it goes before the declaration). Blank
-- lines are kept between declarations, at most one.
--
-- The canonical spellings (D341): parameters for leading lambdas (`f x = e`),
-- `f . g` for `compose f g`, integers in decimal, floats as written.
------------------------------------------------------------------------

module Once.Format.Print where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.Char using (Char)
import Data.Char as Ch
open import Data.Integer using (ℤ; +_; -[1+_])
import Data.Integer.Show as ℤS
open import Data.List using (List; []; _∷_; _++_; reverse; foldr; length; replicate; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≡ᵇ_; _<ᵇ_)
import Data.Nat.Show as ℕS
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; fromList; toList; _==_) renaming (_++_ to _++ˢ_)
import Data.String as Str
open import Relation.Nullary using (does)

open import Once.Spec.Grade using (Quantity; Zero; One; Many; Finite; pureᶠ; actᶠ; Purity; fin; eff; mk-kind)
open import Once.Spec.Type using (Ty; Fun; Type; Unit; Void; Int; Float; _⇒[_]_; μ; ν; K; Id; _⊕_; _⊗_)
import Once.Spec.Type as T
open import Once.Spec.Surface.Syntax using (PolyType; PolyFunctor; PUnit; PVoid; PInt; PFloat; _P*_; _P+_;
  _P⇒[_]_; PAct; PEff; Pμ; Pν; PTVar; PK; PId; _P⊕_; _P⊗_; BinOp; OpAdd; OpSub; OpMul; OpDiv; OpMod;
  OpLt; OpLe; OpGt; OpGe; OpEq; OpNe; Expr; RVar; RQualified; RResolved; RApp; RLam; RLet; RPair; RDestruct;
  RUnit; RInt; RFloat; RAnnot; RBinOp; RNeg; Decl; DTypeSig; DFunDef; DSignature; DTypeAlias; DImport;
  Import; mkImport; Module; mkModule)
open import Once.Spec.Name using (CanonicalName; canonical)
open import Once.Parser.Token using (Token; TWord; TInt; TFloat; TNewline; TEOF)
open import Once.Format.Lex using (Item; tok; comment; cont)
open import Once.Format.Doc
open import Once.Format.Comment using (commentRun; eolText)
import Once.Spec.Surface.Lexing as S

------------------------------------------------------------------------
-- The comments, anchored
------------------------------------------------------------------------

-- What stands before an anchor: comments on lines of their own, and blank lines.
data Note : Set where
  note-comment : String → Note
  note-blank   : Note

record Notes : Set where
  constructor notes
  field
    top    : List Note      -- before the declaration the anchor is in
    inner  : List String    -- before the anchor, in place
    after  : List String    -- at the end of the anchor's line

noNotes : Notes
noNotes = notes [] [] []

-- The trivia: notes per anchor index (in order), and the notes after the last
-- anchor.
Trivia : Set
Trivia = List (ℕ × Notes)

-- Words and literals; `compose` is not one (`f . g` spells it without).
isAnchor : Token → Bool
isAnchor (TWord w)          = not (w == "compose")
isAnchor (TInt _ _)         = true
isAnchor (TFloat _ _ _ _)   = true
{-# CATCHALL #-}
isAnchor _                  = false

-- A comment's text without trailing blanks.
trimEnd : String → String
trimEnd s = fromList (reverse (dropBlanks (reverse (toList s))))
  where
    dropBlanks : List Char → List Char
    dropBlanks []       = []
    dropBlanks (c ∷ cs) = if does (c Ch.≟ ' ') ∨ does (c Ch.≟ '\t') ∨ does (c Ch.≟ '\r')
                          then dropBlanks cs else c ∷ cs

-- Add to the notes of anchor `k`.
addTo : ℕ → (Notes → Notes) → Trivia → Trivia
addTo k f []              = (k , f noNotes) ∷ []
addTo k f ((j , n) ∷ ts) = if k ≡ᵇ j then (j , f n) ∷ ts else (j , n) ∷ addTo k f ts

addTop : Note → Notes → Notes
addTop x (notes t i a) = notes (t ++ (x ∷ [])) i a
addInner : String → Notes → Notes
addInner x (notes t i a) = notes t (i ++ (x ∷ [])) a
addAfter : String → Notes → Notes
addAfter x (notes t i a) = notes t i (a ++ (x ∷ []))

-- A comment on its own line waits for its line end: a token `TNewline` after
-- it (the next line starts a declaration) makes it a top note, a swallowed
-- one (`cont`, the next line is indented) an inner note.
data Line : Set where
  line-empty  : Line          -- nothing on the line yet
  line-code   : Line          -- a token on it
  line-text   : List String → Line -- only comments on it (in order)

-- What waits for its line end: a comment (and whether it is a top note), or
-- a blank line.
data Held : Set where
  held-comment : String → Bool → Held
  held-blank   : Held

record W : Set where
  constructor walker
  field
    k        : ℕ              -- the next anchor's index
    here     : Bool           -- an anchor since the last line that starts a declaration
    ln       : Line           -- the current line
    held     : List Held      -- in order
    breaks   : ℕ              -- line ends since the last thing on a line
    acc      : Trivia

-- What is held before something held for the declaration stands before
-- the declaration too (so the comments keep their order).
-- (read last first: `seen`, something held for the declaration came after)
promoteR : List Held → Bool → List Held
promoteR []                       _     = []
promoteR (held-comment h b ∷ hs)  false = held-comment h b ∷ promoteR hs b
promoteR (held-comment h _ ∷ hs)  true  = held-comment h true ∷ promoteR hs true
promoteR (held-blank ∷ hs)        _     = held-blank ∷ promoteR hs true

promote : List Held → List Held
promote hs = reverse (promoteR (reverse hs) false)

-- The held things, at anchor `k`, in order.
settleAt : ℕ → List Held → Trivia → Trivia
settleAt k []                         t = t
settleAt k (held-comment h true ∷ hs)  t = settleAt k hs (addTo k (addTop (note-comment h)) t)
settleAt k (held-comment h false ∷ hs) t = settleAt k hs (addTo k (addInner h) t)
settleAt k (held-blank ∷ hs)           t = settleAt k hs (addTo k (addTop note-blank) t)

-- Settle what is held at the next anchor, in order.
settle : W → W
settle (walker k h ln hs b t) = walker k h ln [] b (settleAt k (promote hs) t)

-- A blank line before what comes next (two line ends since the last thing).
blankBefore : ℕ → List Held → List Held
blankBefore b hs = if 2 <ᵇ suc b then hs ++ (held-blank ∷ []) else hs

lineEnd : Bool → W → W
lineEnd top (walker k h (line-text cs) hs b t) = walker k h line-empty (hs ++ map (λ c → held-comment c top) cs) 1 t
lineEnd top (walker k h line-empty hs b t)    = walker k h line-empty hs (suc b) t
lineEnd top (walker k h line-code hs b t)     = walker k h line-empty hs (suc b) t

-- A line end (`TNewline`, and the end of the text), or another token.
isLineEnd : Token → Bool
isLineEnd TNewline = true
isLineEnd TEOF     = true
{-# CATCHALL #-}
isLineEnd _        = false

-- Comments before code on their line (block comments) stand before it, in place.
pending : Line → List Held → List Held
pending (line-text cs) hs = hs ++ map (λ c → held-comment c false) cs
pending line-empty    hs = hs
pending line-code     hs = hs

-- (a line end `TNewline` starts a declaration)
stepTok : W → Token → Bool → W
stepTok (walker k _ ln hs b t) x true = lineEnd true (walker k false ln hs b t)
stepTok (walker k h ln hs b t) x false = next (settle (walker k h ln (pending ln (blankBefore b hs)) b t))
  where
    next : W → W
    next (walker k′ h′ _ _ _ t′) =
      walker (if isAnchor x then suc k′ else k′) (h′ ∨ isAnchor x) line-code [] 0 t′

-- A comment after code ends the line of the last anchor; before the
-- declaration's first anchor, it stands before the declaration.
stepComment : W → String → W
stepComment (walker k h line-code hs b t) c =
  walker k h line-code hs b (if h then addTo (k ∸ 1) (addAfter c) t else addTo k (addTop (note-comment c)) t)
stepComment (walker k h line-empty hs b t) c = walker k h (line-text (c ∷ [])) (blankBefore b hs) 0 t
stepComment (walker k h (line-text cs) hs b t) c = walker k h (line-text (cs ++ (c ∷ []))) hs b t

step : W → Item → W
step σ (tok x)     = stepTok σ x (isLineEnd x)
step σ cont        = lineEnd false σ
step σ (comment c) = stepComment σ (trimEnd c)

-- The walk over the items.
walkItems : W → List Item → W
walkItems a []       = a
walkItems a (x ∷ xs) = walkItems (step a x) xs

-- What is left over goes before the end.
finish : W → Trivia
finish σ = W.acc (settle (lineEnd true σ))

-- | The trivia of a text's items.
trivia : List Item → Trivia
trivia is = finish (walkItems (walker 0 false line-empty [] 0 []) is)


lookupNotes : ℕ → Trivia → Notes
lookupNotes k []              = noNotes
lookupNotes k ((j , n) ∷ ts) = if k ≡ᵇ j then n else lookupNotes k ts

------------------------------------------------------------------------
-- Printing with the anchors counted
------------------------------------------------------------------------

-- A printer reads the trivia and the next anchor's index.
P : Set → Set
P A = Trivia → ℕ → A × ℕ

pure′ : ∀ {A} → A → P A
pure′ a _ k = a , k

_>>=′_ : ∀ {A B} → P A → (A → P B) → P B
(m >>=′ f) tv k = next (m tv k)
  where
    next : _ → _
    next (a , k′) = f a tv k′

infixl 1 _>>=′_

-- Documents in sequence.
_⊕ᵈ_ : P Doc → P Doc → P Doc
a ⊕ᵈ b = a >>=′ λ x → b >>=′ λ y → pure′ (x <> y)
infixr 6 _⊕ᵈ_

-- One token, a blank.
t : S.Token → P Doc
t x = pure′ (tk x)

␣ : P Doc
␣ = pure′ sp

-- An anchor: its inner comments before it, its end-of-line comments after.
inners : List String → Doc
inners []         = empty
inners cs@(_ ∷ _) = newline <> commentRun cs

eols : List String → Doc
eols []       = empty
eols (c ∷ cs) = eol (eolText c) <> eols cs

anchor : S.Token → P Doc
anchor x tv k = (inners (Notes.inner (lookupNotes k tv)) <> tk x <> eols (Notes.after (lookupNotes k tv))) , suc k

-- A word; `compose` is not an anchor.
word : String → P Doc
word s = if s == "compose" then t (S.TWord s) else anchor (S.TWord s)

-- The top notes of the anchors in [k, k′), in order: before a declaration.
tops : Trivia → ℕ → ℕ → List Note
tops tv j zero    = []
tops tv j (suc n) = Notes.top (lookupNotes j tv) ++ tops tv (suc j) n

topList : ℕ → ℕ → Trivia → List Note
topList k k′ tv = tops tv k (k′ ∸ k)

-- Comment runs, one blank line between two (a blank line inside a run of
-- comments separates its paragraphs; any other blank line is the code's).
-- `acc`: the current run; `sepd`: a blank line seen since it.
runs : List Note → List String → Bool → Doc
runs []                    []         _     = empty
runs []                    acc@(_ ∷ _) _    = commentRun acc
runs (note-blank ∷ ns)     acc        _     = runs ns acc true
runs (note-comment c ∷ ns) []         _     = runs ns (c ∷ []) false
runs (note-comment c ∷ ns) acc@(_ ∷ _) false = runs ns (acc ++ (c ∷ [])) false
runs (note-comment c ∷ ns) acc@(_ ∷ _) true  = commentRun acc <> blank <> runs ns (c ∷ []) false

topDoc : List Note → Doc
topDoc ns = runs ns [] false

hasComment : List Note → Bool
hasComment []                    = false
hasComment (note-comment _ ∷ _)  = true
hasComment (note-blank ∷ ns)     = hasComment ns

------------------------------------------------------------------------
-- Names and literals
------------------------------------------------------------------------

-- The token of an operator character.
opToken : Char → Maybe S.Token
opToken c =
  if does (c Ch.≟ '.') then just S.TDot else
  if does (c Ch.≟ '+') then just S.TPlus else
  if does (c Ch.≟ '-') then just S.TMinus else
  if does (c Ch.≟ '*') then just S.TStar else
  if does (c Ch.≟ '/') then just S.TSlash else
  if does (c Ch.≟ '%') then just S.TPercent else
  if does (c Ch.≟ '<') then just S.TLt else
  if does (c Ch.≟ '>') then just S.TGt else
  if does (c Ch.≟ '|') then just S.TPipe else
  if does (c Ch.≟ '&') then just S.TAmpersand else
  if does (c Ch.≟ '@') then just S.TAt else nothing

isOpChar : Char → Bool
isOpChar c with opToken c
... | just _  = true
... | nothing = false

allOp : List Char → Bool
allOp []       = false
allOp (c ∷ []) = isOpChar c
allOp (c ∷ cs@(_ ∷ _)) = isOpChar c ∧ allOp cs

-- An operator character's token.
opTok1 : Maybe S.Token → P Doc
opTok1 (just x)  = t x
opTok1 nothing   = pure′ empty

-- An operator's characters as tokens, a blank where two would lex as
-- something else (`--` a comment, `->` an arrow).
opToks : List Char → P Doc
opToks []             = pure′ empty
opToks (c ∷ [])       = opTok1 (opToken c)
opToks (c ∷ d ∷ cs)   =
  opTok1 (opToken c) ⊕ᵈ pure′ (if does (c Ch.≟ '-') ∧ (does (d Ch.≟ '-') ∨ does (d Ch.≟ '>')) then sp else empty)
    ⊕ᵈ opToks (d ∷ cs)

isOperator : String → Bool
isOperator s = allOp (toList s)

-- A name: a word, or an operator in parentheses (its characters are not anchors).
name : String → P Doc
name x = if isOperator x then t S.TLParen ⊕ᵈ opToks (toList x) ⊕ᵈ t S.TRParen else word x

------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------

-- Levels: 0 an arrow, 1 a sum, 2 a product, 3 an atom. `t`: no `*` or `+`
-- follows (a `Mu`/`Nu` would read it into its functor).
paren : Bool → P Doc → P Doc
paren true  d = t S.TLParen ⊕ᵈ d ⊕ᵈ t S.TRParen
paren false d = d

grade : Quantity → P Doc
grade Zero = ␣ ⊕ᵈ t S.TCaret0 ⊕ᵈ ␣ ⊕ᵈ t S.TArrow
grade One  = ␣ ⊕ᵈ t S.TCaret1 ⊕ᵈ ␣ ⊕ᵈ t S.TArrow
grade Many = ␣ ⊕ᵈ t S.TArrow

-- ` op `
infixOp : S.Token → P Doc
infixOp x = ␣ ⊕ᵈ t x ⊕ᵈ ␣

mutual
  pty : ℕ → Bool → PolyType → P Doc
  pty l b PUnit         = word "Unit"
  pty l b PVoid         = word "Void"
  pty l b PInt          = word "Int"
  pty l b PFloat        = word "Float"
  pty l b (PTVar x)     = word x
  pty l b (A P⇒[ q ] B) = paren (0 <ᵇ l) (pty 1 true A ⊕ᵈ grade q ⊕ᵈ ␣ ⊕ᵈ pty 0 (b ∨ (0 <ᵇ l)) B)
  pty l b (A P+ B)      = paren (1 <ᵇ l) (pty 1 false A ⊕ᵈ infixOp S.TPlus ⊕ᵈ pty 2 (b ∨ (1 <ᵇ l)) B)
  pty l b (A P* B)      = paren (2 <ᵇ l) (pty 2 false A ⊕ᵈ infixOp S.TStar ⊕ᵈ pty 3 (b ∨ (2 <ᵇ l)) B)
  pty l b (PEff A B)    = paren (3 <ᵇ l) (word "Eff" ⊕ᵈ ␣ ⊕ᵈ pty 3 false A ⊕ᵈ ␣ ⊕ᵈ pty 3 false B)
  pty l b (PAct A B)    = paren (3 <ᵇ l) (word "Act" ⊕ᵈ ␣ ⊕ᵈ pty 3 false A ⊕ᵈ ␣ ⊕ᵈ pty 3 false B)
  pty l b (Pμ F)        = paren (not b) (word "Mu" ⊕ᵈ ␣ ⊕ᵈ pfunArg F)
  pty l b (Pν F pureᶠ)  = paren (not b) (word "Nu" ⊕ᵈ ␣ ⊕ᵈ pfunArg F)
  pty l b (Pν F actᶠ)   = paren (not b) (word "Nu" ⊕ᵈ ␣ ⊕ᵈ t S.TLParen ⊕ᵈ word "Act" ⊕ᵈ ␣ ⊕ᵈ pfun 0 F ⊕ᵈ t S.TRParen)

  -- A `Mu`/`Nu` functor: parenthesized unless it is `Id` (D341).
  pfunArg : PolyFunctor → P Doc
  pfunArg PId = word "Id"
  {-# CATCHALL #-}
  pfunArg F   = t S.TLParen ⊕ᵈ pfun 0 F ⊕ᵈ t S.TRParen

  -- Functors: 0 a sum, 1 a product, 2 an atom.
  pfun : ℕ → PolyFunctor → P Doc
  pfun l PId       = word "Id"
  pfun l (PK A)    = paren (1 <ᵇ l) (word "K" ⊕ᵈ ␣ ⊕ᵈ pty 3 false A)
  pfun l (F P⊕ G)  = paren (0 <ᵇ l) (pfun 0 F ⊕ᵈ infixOp S.TPlus ⊕ᵈ pfun 1 G)
  pfun l (F P⊗ G)  = paren (1 <ᵇ l) (pfun 1 F ⊕ᵈ infixOp S.TStar ⊕ᵈ pfun 2 G)

-- An annotation's (ground) type, as it is written: a pure arrow with its
-- grade, `Eff`/`Act` for the effectful ones.
mutual
  toPoly : Ty 0 → PolyType
  toPoly Unit  = PUnit
  toPoly Void  = PVoid
  toPoly Int   = PInt
  toPoly Float = PFloat
  toPoly (A ⇒[ mk-kind q (fin pureᶠ) ] B) = toPoly A P⇒[ q ] toPoly B
  toPoly (A ⇒[ mk-kind q (fin actᶠ) ] B)  = PAct (toPoly A) (toPoly B)
  toPoly (A ⇒[ mk-kind q eff ] B)         = PEff (toPoly A) (toPoly B)
  toPoly (A T.+ B) = toPoly A P+ toPoly B
  toPoly (A T.* B) = toPoly A P* toPoly B
  toPoly (μ F)     = Pμ (toPolyF F)
  toPoly (ν F φ)   = Pν (toPolyF F) φ

  toPolyF : Fun 0 → PolyFunctor
  toPolyF Id      = PId
  toPolyF (K A)   = PK (toPoly A)
  toPolyF (F ⊕ G) = toPolyF F P⊕ toPolyF G
  toPolyF (F ⊗ G) = toPolyF F P⊗ toPolyF G

gty : ℕ → Bool → Ty 0 → P Doc
gty l b T = pty l b (toPoly T)

------------------------------------------------------------------------
-- Expressions
------------------------------------------------------------------------

-- Levels, loosest first: 0 a composition, 1 a comparison, 2 `+`/`-`, 3
-- `*`/`/`/`%`, 4 a prefix `-`, 5 an application, 6 an atom. A lambda, `let` or
-- `destruct` reads as far as it can, so it stands bare only where nothing of
-- the expression follows it (`w`, a whole expression).

opTok : BinOp → S.Token
opTok OpAdd = S.TPlus
opTok OpSub = S.TMinus
opTok OpMul = S.TStar
opTok OpDiv = S.TSlash
opTok OpMod = S.TPercent
opTok OpLt  = S.TLt
opTok OpLe  = S.TLe
opTok OpGt  = S.TGt
opTok OpGe  = S.TGe
opTok OpEq  = S.TEqEq
opTok OpNe  = S.TNeq

opLevel : BinOp → ℕ
opLevel OpAdd = 2
opLevel OpSub = 2
opLevel OpMul = 3
opLevel OpDiv = 3
opLevel OpMod = 3
opLevel OpLt  = 1
opLevel OpLe  = 1
opLevel OpGt  = 1
opLevel OpGe  = 1
opLevel OpEq  = 1
opLevel OpNe  = 1

-- The parameters of leading lambdas, and the body.
lams : Expr → List String × Expr
lams (RLam x e) = x ∷ proj₁ (lams e) , proj₂ (lams e)
{-# CATCHALL #-}
lams e = [] , e

startsNeg : Expr → Bool
startsNeg (RNeg _) = true
{-# CATCHALL #-}
startsNeg _        = false

isCompose : Expr → Bool
isCompose (RVar x) = x == "compose"
{-# CATCHALL #-}
isCompose _        = false

-- `compose g` applied once: the `compose` (a composition is `compose g h`).
headOf : Expr → Expr
headOf (RApp c g) = c
{-# CATCHALL #-}
headOf e          = RUnit

leftLevel : ℕ → ℕ
leftLevel 1 = 2
{-# CATCHALL #-}
leftLevel l = l

-- A resolved name's path, dotted.
dotted : List String → P Doc
dotted []               = pure′ empty
dotted (x ∷ [])         = word x
dotted (x ∷ xs@(_ ∷ _)) = word x ⊕ᵈ t S.TDot ⊕ᵈ dotted xs

mutual
  -- `l` the level the position asks for, `w` whether the expression is whole.
  pex : ℕ → Bool → Expr → P Doc
  pex l wh (RApp f a)         = pcomp l (isCompose (headOf f)) f a
  pex l wh (RBinOp op a b)    =
    paren (opLevel op <ᵇ l) (pbin (opLevel op) op a b) >>=′ λ d → pure′ (group (nest indent d))
  pex l wh (RNeg e)           = paren (4 <ᵇ l) (t S.TMinus ⊕ᵈ pure′ (if startsNeg e then sp else empty) ⊕ᵈ pex 4 false e)
  pex l wh RUnit              = t S.TLParen ⊕ᵈ t S.TRParen
  pex l wh (RInt n)           = anchor (S.TInt n)
  pex l wh (RFloat i f n)     = anchor (S.TFloat i f n)
  pex l wh (RVar x)           = name x
  pex l wh (RQualified x a)   = word x ⊕ᵈ t S.TAt ⊕ᵈ word a
  pex l wh (RResolved (canonical xs)) = dotted xs
  pex l wh (RPair a b)        =
    (t S.TLParen ⊕ᵈ pex 0 true a ⊕ᵈ t S.TComma ⊕ᵈ pure′ line ⊕ᵈ pex 0 true b ⊕ᵈ t S.TRParen)
      >>=′ λ d → pure′ (group (nest indent d))
  pex l wh (RAnnot e T)       = t S.TLParen ⊕ᵈ pex 0 true e ⊕ᵈ infixOp S.TColon ⊕ᵈ gty 0 true T ⊕ᵈ t S.TRParen
  pex l wh (RLam x e)         = paren (not wh) (plam x e)
  pex l wh (RLet x v b)       = paren (not wh) (plet x v b)
  pex l wh (RDestruct s x el y er) = paren (not wh) (pdes s x el y er)

  -- `compose g h`, written `g . h`; any other application as one: the head,
  -- then the arguments, broken one per line when they do not fit.
  pcomp : ℕ → Bool → Expr → Expr → P Doc
  pcomp l true (RApp c g) h = pcompose l g h
  {-# CATCHALL #-}
  pcomp l _ f a             = paren (5 <ᵇ l) (pspine f ⊕ᵈ pure′ line ⊕ᵈ pex 6 false a)
                                >>=′ λ d → pure′ (group (nest indent d))

  -- The head and the arguments before the last; a `compose g h` inside a
  -- spine is an argument-less head, so it is parenthesized.
  pcompose : ℕ → Expr → Expr → P Doc
  pcompose l g h = paren (0 <ᵇ l) (pchainC g ⊕ᵈ (pure′ line ⊕ᵈ t S.TDot ⊕ᵈ ␣) ⊕ᵈ pex 1 false h)
                     >>=′ λ d → pure′ (group (nest indent d))

  -- A left-nested chain is one group, broken before each operator: the left
  -- operand of `.`, while it is a composition.
  pchainC : Expr → P Doc
  pchainC (RApp f h) = pchainC′ (isCompose (headOf f)) f h
  {-# CATCHALL #-}
  pchainC e          = pex 1 false e

  pchainC′ : Bool → Expr → Expr → P Doc
  pchainC′ true (RApp c g) h = pchainC g ⊕ᵈ (pure′ line ⊕ᵈ t S.TDot ⊕ᵈ ␣) ⊕ᵈ pex 1 false h
  {-# CATCHALL #-}
  pchainC′ _ f a             = pcomp 0 false f a

  -- …and of an operator, while its left operand is one of the same precedence
  -- (`+`/`-`, `*`/`/`/`%`; a comparison takes no chain).
  pbin : ℕ → BinOp → Expr → Expr → P Doc
  pbin lv op a b = pleft lv a ⊕ᵈ pure′ line ⊕ᵈ t (opTok op) ⊕ᵈ ␣ ⊕ᵈ pex (suc lv) false b

  -- (a comparison's left operand is a sum: `(a < b) < c` keeps its parentheses)
  pleft : ℕ → Expr → P Doc
  pleft lv (RBinOp op a b) = if (lv ≡ᵇ opLevel op) ∧ (1 <ᵇ lv) then pbin lv op a b
                             else pex (leftLevel lv) false (RBinOp op a b)
  {-# CATCHALL #-}
  pleft lv e               = pex (leftLevel lv) false e

  pspine : Expr → P Doc
  pspine (RApp f a) = pspine′ (isCompose (headOf f)) f a
  {-# CATCHALL #-}
  pspine e          = pex 6 false e

  pspine′ : Bool → Expr → Expr → P Doc
  pspine′ true (RApp c g) h = pcompose 6 g h
  {-# CATCHALL #-}
  pspine′ _ f a             = pspine f ⊕ᵈ pure′ line ⊕ᵈ pex 6 false a

  -- `\x y -> b`: the parameters of the leading lambdas, then the body.
  plam : String → Expr → P Doc
  plam x e = (t S.TLambda ⊕ᵈ word x ⊕ᵈ plam′ e) >>=′ λ d → pure′ (group d)

  plam′ : Expr → P Doc
  plam′ (RLam y e) = ␣ ⊕ᵈ word y ⊕ᵈ plam′ e
  {-# CATCHALL #-}
  plam′ b          = ␣ ⊕ᵈ t S.TArrow ⊕ᵈ (pure′ line ⊕ᵈ pex 0 true b >>=′ λ d → pure′ (nest indent d))

  -- A chain of `let`s is one group: flat when it fits, else each `in` starts a
  -- line; each value is a group of its own, so it stays after its `=` when it fits.
  plet : String → Expr → Expr → P Doc
  plet x v b = plet′ x v b >>=′ λ d → pure′ (group d)

  plet′ : String → Expr → Expr → P Doc
  plet′ x v (RLet y v′ c) = lhead x v ⊕ᵈ pure′ line ⊕ᵈ word "in" ⊕ᵈ ␣ ⊕ᵈ plet′ y v′ c
  {-# CATCHALL #-}
  plet′ x v b            = lhead x v ⊕ᵈ pure′ line ⊕ᵈ word "in" ⊕ᵈ ␣ ⊕ᵈ pex 0 true b

  lhead : String → Expr → P Doc
  lhead x v = word "let" ⊕ᵈ ␣ ⊕ᵈ word x ⊕ᵈ ␣ ⊕ᵈ t S.TEquals
                ⊕ᵈ (pure′ line ⊕ᵈ pex 0 true v >>=′ λ d → pure′ (group (nest indent d)))

  pdes : Expr → String → Expr → String → Expr → P Doc
  pdes s x el y er =
    (word "destruct" ⊕ᵈ ␣ ⊕ᵈ pex 0 true s ⊕ᵈ ␣ ⊕ᵈ word "of"
      ⊕ᵈ (pure′ line ⊕ᵈ t S.TLBrace ⊕ᵈ ␣ ⊕ᵈ word "Left" ⊕ᵈ ␣ ⊕ᵈ word x ⊕ᵈ infixOp S.TArrow ⊕ᵈ pex 0 true el
          ⊕ᵈ pure′ line ⊕ᵈ t S.TSemicolon ⊕ᵈ ␣ ⊕ᵈ word "Right" ⊕ᵈ ␣ ⊕ᵈ word y ⊕ᵈ infixOp S.TArrow ⊕ᵈ pex 0 true er
          ⊕ᵈ pure′ line ⊕ᵈ t S.TRBrace >>=′ λ d → pure′ (nest indent d)))
      >>=′ λ d → pure′ (group d)

------------------------------------------------------------------------
-- Declarations and the module
------------------------------------------------------------------------

path : List String → P Doc
path []           = pure′ empty
path (x ∷ [])     = word x
path (x ∷ xs@(_ ∷ _)) = word x ⊕ᵈ t S.TDot ⊕ᵈ path xs

spaced : List String → P Doc
spaced []       = pure′ empty
spaced (x ∷ xs) = ␣ ⊕ᵈ word x ⊕ᵈ spaced xs

-- A declaration's text.
pbody : Decl → P Doc
pbody (DImport (mkImport p nothing))  = word "import" ⊕ᵈ ␣ ⊕ᵈ path p
pbody (DImport (mkImport p (just a))) = word "import" ⊕ᵈ ␣ ⊕ᵈ path p ⊕ᵈ ␣ ⊕ᵈ word "as" ⊕ᵈ ␣ ⊕ᵈ word a
pbody (DTypeAlias x ps A) =
  word "type" ⊕ᵈ ␣ ⊕ᵈ word x ⊕ᵈ spaced ps ⊕ᵈ ␣ ⊕ᵈ t S.TEquals ⊕ᵈ pure′ line ⊕ᵈ pty 0 true A
pbody (DSignature x A) =
  word "signature" ⊕ᵈ ␣ ⊕ᵈ word x ⊕ᵈ ␣ ⊕ᵈ t S.TColon ⊕ᵈ pure′ line ⊕ᵈ pty 0 true A
pbody (DTypeSig x A) = name x ⊕ᵈ ␣ ⊕ᵈ t S.TColon ⊕ᵈ pure′ line ⊕ᵈ pty 0 true A
pbody (DFunDef x e) =
  name x ⊕ᵈ spaced (proj₁ (lams e)) ⊕ᵈ ␣ ⊕ᵈ t S.TEquals ⊕ᵈ pure′ line ⊕ᵈ pex 0 true (proj₂ (lams e))

-- A declaration; every line it breaks is indented (an unindented line would
-- start the next declaration).
pdecl : Decl → P Doc
pdecl d = pbody d >>=′ λ x → pure′ (group (nest indent x))

-- No blank line between a type signature and its definition, or between two
-- imports; one between any other two declarations (D341).
together : Decl → Decl → Bool
together (DTypeSig x _) (DFunDef y _) = x == y
together (DImport _)    (DImport _)   = true
{-# CATCHALL #-}
together _              _             = false

-- What stands before a declaration's first anchor stands before the
-- declaration: its inner notes join its top notes.
hoist : ℕ → Trivia → Trivia
hoist k []              = []
hoist k ((j , n) ∷ ts) = if k ≡ᵇ j then (j , up n) ∷ ts else (j , n) ∷ hoist k ts
  where
    up : Notes → Notes
    up (notes t i a) = notes (t ++ map note-comment i) [] a

gap : Maybe Decl → Decl → Doc
gap nothing  d = empty
gap (just p) d = if together p d then empty else blank

gapEnd : Maybe Decl → Doc
gapEnd nothing  = empty
gapEnd (just _) = blank

-- The comments before the first declaration are the file's: a blank line
-- between them and it.
lead : Maybe Decl → List Note → Doc
lead nothing  ns = if hasComment ns then topDoc ns <> blank else empty
lead (just _) ns = topDoc ns

ending : Maybe Decl → List Note → Doc
ending prev ns = if hasComment ns then gapEnd prev <> topDoc ns else empty

-- | Declarations, one per line, each under the comments that stand before
-- it; the comments after the last anchor at the end (with those before no
-- anchor, as before a declaration).
pdecls : Maybe Decl → List Decl → P Doc
pdecls prev [] tv k = ending prev (topList k (suc k) (hoist k tv)) , k
pdecls prev (d ∷ ds) tv k = at (hoist k tv)
  where
    at : Trivia → Doc × ℕ
    at tv′ = decl (pdecl d tv′ k)
      where
        decl : Doc × ℕ → Doc × ℕ
        decl (dd , k′) = rest (pdecls (just d) ds tv′ k′)
          where
            rest : Doc × ℕ → Doc × ℕ
            rest (r , k″) = (gap prev d <> lead prev (topList k k′ tv′) <> dd <> newline <> r) , k″

-- | A module.
pmodule : Module → P Doc
pmodule (mkModule ds) = pdecls nothing ds

-- | A module in the canonical layout, with the comments of `items`.
format : Module → List Item → String
format m is = render (proj₁ (pmodule m (trivia is) 0))
