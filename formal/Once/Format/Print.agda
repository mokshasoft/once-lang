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
-- the end of the line of the anchor before it. Blank lines are kept between
-- declarations, at most one.
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

private
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
    line-text   : String → Line -- only a comment on it

  -- What waits for its line end: a comment (and whether it is a top note), or
  -- a blank line.
  data Held : Set where
    held-comment : String → Bool → Held
    held-blank   : Held

  record W : Set where
    constructor w
    field
      k        : ℕ              -- the next anchor's index
      ln       : Line           -- the current line
      held     : List Held      -- in order
      breaks   : ℕ              -- line ends since the last thing on a line
      acc      : Trivia

  -- Settle what is held at the next anchor, in order.
  settle : W → W
  settle (w k ln hs b t) = w k ln [] b (go hs t)
    where
      go : List Held → Trivia → Trivia
      go []                         t = t
      go (held-comment h true ∷ hs)  t = go hs (addTo k (addTop (note-comment h)) t)
      go (held-comment h false ∷ hs) t = go hs (addTo k (addInner h) t)
      go (held-blank ∷ hs)           t = go hs (addTo k (addTop note-blank) t)

  -- A blank line before what comes next (two line ends since the last thing).
  blankBefore : ℕ → List Held → List Held
  blankBefore b hs = if 2 <ᵇ suc b then hs ++ (held-blank ∷ []) else hs

  lineEnd : Bool → W → W
  lineEnd top (w k (line-text c) hs b t) = w k line-empty (hs ++ (held-comment c top ∷ [])) 1 t
  lineEnd top (w k line-empty hs b t)    = w k line-empty hs (suc b) t
  lineEnd top (w k line-code hs b t)     = w k line-empty hs (suc b) t

  -- A line end (`TNewline`, and the end of the text), or another token.
  isLineEnd : Token → Bool
  isLineEnd TNewline = true
  isLineEnd TEOF     = true
  {-# CATCHALL #-}
  isLineEnd _        = false

  -- A comment before code on its line (a block comment) stands before it, in place.
  pending : Line → List Held → List Held
  pending (line-text c) hs = hs ++ (held-comment c false ∷ [])
  pending line-empty    hs = hs
  pending line-code     hs = hs

  stepTok : W → Token → Bool → W
  stepTok σ x true = lineEnd true σ
  stepTok (w k ln hs b t) x false with settle (w k ln (pending ln (blankBefore b hs)) b t)
  ... | w k′ _ _ _ t′ = w (if isAnchor x then suc k′ else k′) line-code [] 0 t′

  stepComment : W → String → W
  stepComment (w k line-code hs b t) c =
    w k line-code hs b (if k ≡ᵇ 0 then addTo 0 (addTop (note-comment c)) t else addTo (k ∸ 1) (addAfter c) t)
  stepComment (w k line-empty hs b t) c = w k (line-text c) (blankBefore b hs) 0 t
  stepComment (w k (line-text c′) hs b t) c = w k (line-text (c′ ++ˢ " " ++ˢ c)) hs b t

  step : W → Item → W
  step σ (tok x)     = stepTok σ x (isLineEnd x)
  step σ cont        = lineEnd false σ
  step σ (comment c) = stepComment σ (trimEnd c)

-- | The trivia of a text's items.
trivia : List Item → Trivia
trivia is = finish (foldl′ step (w 0 line-empty [] 0 []) is)
  where
    foldl′ : (W → Item → W) → W → List Item → W
    foldl′ f a []       = a
    foldl′ f a (x ∷ xs) = foldl′ f (f a x) xs
    -- what is left over goes before the end
    finish : W → Trivia
    finish σ with settle (lineEnd true σ)
    ... | w _ _ _ _ t = t

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
(m >>=′ f) tv k with m tv k
... | a , k′ = f a tv k′

infixl 1 _>>=′_

-- Documents in sequence.
_⊕ᵈ_ : P Doc → P Doc → P Doc
a ⊕ᵈ b = a >>=′ λ x → b >>=′ λ y → pure′ (x <> y)
infixr 6 _⊕ᵈ_

txt : String → P Doc
txt s = pure′ (text s)

-- An anchor: its inner comments before it, its end-of-line comments after.
anchor : String → P Doc
anchor s tv k with lookupNotes k tv
... | notes _ inner after =
      (foldr (λ c d → newline <> text c <> newline <> d) empty inner
        <> text s <> foldr (λ c d → eol c <> d) empty after) , suc k

-- A word that is not an anchor (`compose`).
word : String → P Doc
word s = if s == "compose" then txt s else anchor s

-- The top notes of the anchors in [k, k′): before a declaration.
topNotes : ℕ → ℕ → Trivia → Doc
topNotes k k′ tv = go k (k′ ∸ k)
  where
    one : Note → Doc
    one (note-comment c) = text c <> newline
    one note-blank       = blank
    go : ℕ → ℕ → Doc
    go j zero    = empty
    go j (suc n) = foldr (λ x d → one x <> d) empty (Notes.top (lookupNotes j tv)) <> go (suc j) n

------------------------------------------------------------------------
-- Names and literals
------------------------------------------------------------------------

private
  opChars : List Char
  opChars = '.' ∷ '+' ∷ '-' ∷ '*' ∷ '/' ∷ '%' ∷ '<' ∷ '>' ∷ '|' ∷ '&' ∷ '@' ∷ []

  isOpChar : Char → Bool
  isOpChar c = go opChars
    where
      go : List Char → Bool
      go []       = false
      go (x ∷ xs) = does (c Ch.≟ x) ∨ go xs

  allOp : List Char → Bool
  allOp []       = false
  allOp (c ∷ []) = isOpChar c
  allOp (c ∷ cs@(_ ∷ _)) = isOpChar c ∧ allOp cs

  -- An operator's characters, spaced where they would lex as something else
  -- (`--` a comment, `->` an arrow).
  spaceOp : List Char → List Char
  spaceOp []                = []
  spaceOp (c ∷ [])          = c ∷ []
  spaceOp (c ∷ d ∷ cs)      =
    if does (c Ch.≟ '-') ∧ (does (d Ch.≟ '-') ∨ does (d Ch.≟ '>'))
    then c ∷ ' ' ∷ spaceOp (d ∷ cs) else c ∷ spaceOp (d ∷ cs)

isOperator : String → Bool
isOperator s = allOp (toList s)

-- A name: a word, or an operator in parentheses (its characters are not anchors).
name : String → P Doc
name x = if isOperator x then txt ("(" ++ˢ fromList (spaceOp (toList x)) ++ˢ ")") else word x

showInt : ℤ → String
showInt (+ n)    = ℕS.show n
showInt -[1+ n ] = "-" ++ˢ ℕS.show (suc n)

showFloat : ℕ → ℕ → ℕ → String
showFloat i f l = ℕS.show i ++ˢ "." ++ˢ fromList (replicate (l ∸ Str.length (ℕS.show f)) '0') ++ˢ ℕS.show f

------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------

-- Levels: 0 an arrow, 1 a sum, 2 a product, 3 an atom. `t`: no `*` or `+`
-- follows (a `Mu`/`Nu` would read it into its functor).
paren : Bool → P Doc → P Doc
paren true  d = txt "(" ⊕ᵈ d ⊕ᵈ txt ")"
paren false d = d

grade : Quantity → P Doc
grade Zero = txt " ^0 ->"
grade One  = txt " ^1 ->"
grade Many = txt " ->"

mutual
  pty : ℕ → Bool → PolyType → P Doc
  pty l t PUnit         = word "Unit"
  pty l t PVoid         = word "Void"
  pty l t PInt          = word "Int"
  pty l t PFloat        = word "Float"
  pty l t (PTVar x)     = word x
  pty l t (A P⇒[ q ] B) = paren (0 <ᵇ l) (pty 1 true A ⊕ᵈ grade q ⊕ᵈ txt " " ⊕ᵈ pty 0 (t ∨ (0 <ᵇ l)) B)
  pty l t (A P+ B)      = paren (1 <ᵇ l) (pty 1 false A ⊕ᵈ txt " + " ⊕ᵈ pty 2 (t ∨ (1 <ᵇ l)) B)
  pty l t (A P* B)      = paren (2 <ᵇ l) (pty 2 false A ⊕ᵈ txt " * " ⊕ᵈ pty 3 (t ∨ (2 <ᵇ l)) B)
  pty l t (PEff A B)    = paren (3 <ᵇ l) (word "Eff" ⊕ᵈ txt " " ⊕ᵈ pty 3 false A ⊕ᵈ txt " " ⊕ᵈ pty 3 false B)
  pty l t (PAct A B)    = paren (3 <ᵇ l) (word "Act" ⊕ᵈ txt " " ⊕ᵈ pty 3 false A ⊕ᵈ txt " " ⊕ᵈ pty 3 false B)
  pty l t (Pμ F)        = paren (not t) (word "Mu" ⊕ᵈ txt " " ⊕ᵈ pfunArg F)
  pty l t (Pν F pureᶠ)  = paren (not t) (word "Nu" ⊕ᵈ txt " " ⊕ᵈ pfunArg F)
  pty l t (Pν F actᶠ)   = paren (not t) (word "Nu" ⊕ᵈ txt " (" ⊕ᵈ word "Act" ⊕ᵈ txt " " ⊕ᵈ pfun 0 F ⊕ᵈ txt ")")

  -- A `Mu`/`Nu` functor: parenthesized unless it is `Id` (D341).
  pfunArg : PolyFunctor → P Doc
  pfunArg PId = word "Id"
  {-# CATCHALL #-}
  pfunArg F   = txt "(" ⊕ᵈ pfun 0 F ⊕ᵈ txt ")"

  -- Functors: 0 a sum, 1 a product, 2 an atom.
  pfun : ℕ → PolyFunctor → P Doc
  pfun l PId       = word "Id"
  pfun l (PK A)    = paren (1 <ᵇ l) (word "K" ⊕ᵈ txt " " ⊕ᵈ pty 3 false A)
  pfun l (F P⊕ G)  = paren (0 <ᵇ l) (pfun 0 F ⊕ᵈ txt " + " ⊕ᵈ pfun 1 G)
  pfun l (F P⊗ G)  = paren (1 <ᵇ l) (pfun 1 F ⊕ᵈ txt " * " ⊕ᵈ pfun 2 G)

-- An annotation's (ground) type, by the same rules.
mutual
  gty : ℕ → Bool → Ty 0 → P Doc
  gty l t Unit       = word "Unit"
  gty l t Void       = word "Void"
  gty l t Int        = word "Int"
  gty l t Float      = word "Float"
  gty l t (A ⇒[ mk-kind q (fin pureᶠ) ] B) = paren (0 <ᵇ l) (gty 1 true A ⊕ᵈ grade q ⊕ᵈ txt " " ⊕ᵈ gty 0 (t ∨ (0 <ᵇ l)) B)
  gty l t (A ⇒[ mk-kind q (fin actᶠ) ] B)  = paren (3 <ᵇ l) (word "Act" ⊕ᵈ txt " " ⊕ᵈ gty 3 false A ⊕ᵈ txt " " ⊕ᵈ gty 3 false B)
  gty l t (A ⇒[ mk-kind q eff ] B)         = paren (3 <ᵇ l) (word "Eff" ⊕ᵈ txt " " ⊕ᵈ gty 3 false A ⊕ᵈ txt " " ⊕ᵈ gty 3 false B)
  gty l t (A T.+ B)  = paren (1 <ᵇ l) (gty 1 false A ⊕ᵈ txt " + " ⊕ᵈ gty 2 (t ∨ (1 <ᵇ l)) B)
  gty l t (A T.* B)  = paren (2 <ᵇ l) (gty 2 false A ⊕ᵈ txt " * " ⊕ᵈ gty 3 (t ∨ (2 <ᵇ l)) B)
  gty l t (μ F)      = paren (not t) (word "Mu" ⊕ᵈ txt " " ⊕ᵈ gfunArg F)
  gty l t (ν F pureᶠ) = paren (not t) (word "Nu" ⊕ᵈ txt " " ⊕ᵈ gfunArg F)
  gty l t (ν F actᶠ)  = paren (not t) (word "Nu" ⊕ᵈ txt " (" ⊕ᵈ word "Act" ⊕ᵈ txt " " ⊕ᵈ gfun 0 F ⊕ᵈ txt ")")

  gfunArg : Fun 0 → P Doc
  gfunArg Id = word "Id"
  {-# CATCHALL #-}
  gfunArg F  = txt "(" ⊕ᵈ gfun 0 F ⊕ᵈ txt ")"

  gfun : ℕ → Fun 0 → P Doc
  gfun l Id      = word "Id"
  gfun l (K A)   = paren (1 <ᵇ l) (word "K" ⊕ᵈ txt " " ⊕ᵈ gty 3 false A)
  gfun l (F ⊕ G) = paren (0 <ᵇ l) (gfun 0 F ⊕ᵈ txt " + " ⊕ᵈ gfun 1 G)
  gfun l (F ⊗ G) = paren (1 <ᵇ l) (gfun 1 F ⊕ᵈ txt " * " ⊕ᵈ gfun 2 G)

------------------------------------------------------------------------
-- Expressions
------------------------------------------------------------------------

-- Levels, loosest first: 0 a composition, 1 a comparison, 2 `+`/`-`, 3
-- `*`/`/`/`%`, 4 a prefix `-`, 5 an application, 6 an atom. A lambda, `let` or
-- `destruct` reads as far as it can, so it stands bare only where nothing of
-- the expression follows it (`t`, a whole expression).

opText : BinOp → String
opText OpAdd = "+"
opText OpSub = "-"
opText OpMul = "*"
opText OpDiv = "/"
opText OpMod = "%"
opText OpLt  = "<"
opText OpLe  = "<="
opText OpGt  = ">"
opText OpGe  = ">="
opText OpEq  = "=="
opText OpNe  = "!="

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

-- The arguments of an application spine, and its head.
spine : Expr → Expr × List Expr
spine (RApp f a) with spine f
... | h , as = h , as ++ (a ∷ [])
{-# CATCHALL #-}
spine e = e , []

-- The parameters of leading lambdas, and the body.
lams : Expr → List String × Expr
lams (RLam x e) with lams e
... | xs , b = x ∷ xs , b
{-# CATCHALL #-}
lams e = [] , e

private
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

mutual
  -- `l` the level the position asks for, `t` whether the expression is whole.
  pex : ℕ → Bool → Expr → P Doc
  pex l t (RApp f a)         = pcomp l f a (isCompose (headOf f))
  pex l t (RBinOp op a b)    =
    paren (opLevel op <ᵇ l) (pbin (opLevel op) op a b) >>=′ λ d → pure′ (group (nest indent d))
  pex l t (RNeg e)           = paren (4 <ᵇ l) (txt (if startsNeg e then "- " else "-") ⊕ᵈ pex 4 false e)
  pex l t RUnit              = txt "()"
  pex l t (RInt n)           = anchor (showInt n)
  pex l t (RFloat i f n)     = anchor (showFloat i f n)
  pex l t (RVar x)           = name x
  pex l t (RQualified x a)   = word x ⊕ᵈ txt "@" ⊕ᵈ word a
  pex l t (RResolved (canonical xs)) = word (Str.intersperse "." xs)
  pex l t (RPair a b)        =
    (txt "(" ⊕ᵈ pex 0 true a ⊕ᵈ txt "," ⊕ᵈ pure′ line ⊕ᵈ pex 0 true b ⊕ᵈ txt ")")
      >>=′ λ d → pure′ (group (nest indent d))
  pex l t (RAnnot e T)       = txt "(" ⊕ᵈ pex 0 true e ⊕ᵈ txt " : " ⊕ᵈ gty 0 true T ⊕ᵈ txt ")"
  pex l t (RLam x e)         = paren (not t) (plam x e)
  pex l t (RLet x v b)       = paren (not t) (plet x v b)
  pex l t (RDestruct s x el y er) = paren (not t) (pdes s x el y er)

  -- `compose g h`, written `g . h`; any other application as one: the head,
  -- then the arguments, broken one per line when they do not fit.
  pcomp : ℕ → Expr → Expr → Bool → P Doc
  pcomp l (RApp c g) h true = pcompose l g h
  {-# CATCHALL #-}
  pcomp l f a _             = paren (5 <ᵇ l) (pspine f ⊕ᵈ pure′ line ⊕ᵈ pex 6 false a)
                                >>=′ λ d → pure′ (group (nest indent d))

  -- The head and the arguments before the last; a `compose g h` inside a
  -- spine is an argument-less head, so it is parenthesized.
  pcompose : ℕ → Expr → Expr → P Doc
  pcompose l g h = paren (0 <ᵇ l) (pchainC g ⊕ᵈ (pure′ line ⊕ᵈ txt ". ") ⊕ᵈ pex 1 false h)
                     >>=′ λ d → pure′ (group (nest indent d))

  -- A left-nested chain is one group, broken before each operator: the left
  -- operand of `.`, while it is a composition.
  pchainC : Expr → P Doc
  pchainC (RApp f h) = pchainC′ f h (isCompose (headOf f))
  {-# CATCHALL #-}
  pchainC e          = pex 0 false e

  pchainC′ : Expr → Expr → Bool → P Doc
  pchainC′ (RApp c g) h true = pchainC g ⊕ᵈ (pure′ line ⊕ᵈ txt ". ") ⊕ᵈ pex 1 false h
  {-# CATCHALL #-}
  pchainC′ f a _             = pcomp 0 f a false

  -- …and of an operator, while its left operand is one of the same precedence
  -- (`+`/`-`, `*`/`/`/`%`; a comparison takes no chain).
  pbin : ℕ → BinOp → Expr → Expr → P Doc
  pbin lv op a b = pleft lv a ⊕ᵈ pure′ line ⊕ᵈ txt (opText op ++ˢ " ") ⊕ᵈ pex (suc lv) false b

  pleft : ℕ → Expr → P Doc
  pleft lv (RBinOp op a b) = if (lv ≡ᵇ opLevel op) ∧ (1 <ᵇ lv) then pbin lv op a b
                             else pex lv false (RBinOp op a b)
  {-# CATCHALL #-}
  pleft lv e               = pex lv false e

  pspine : Expr → P Doc
  pspine (RApp f a) = pspine′ f a (isCompose (headOf f))
  {-# CATCHALL #-}
  pspine e          = pex 6 false e

  pspine′ : Expr → Expr → Bool → P Doc
  pspine′ (RApp c g) h true = pcompose 6 g h
  {-# CATCHALL #-}
  pspine′ f a _             = pspine f ⊕ᵈ pure′ line ⊕ᵈ pex 6 false a

  -- `\x y -> b`: the parameters of the leading lambdas, then the body.
  plam : String → Expr → P Doc
  plam x e = (txt "\\" ⊕ᵈ word x ⊕ᵈ plam′ e) >>=′ λ d → pure′ (group d)

  plam′ : Expr → P Doc
  plam′ (RLam y e) = txt " " ⊕ᵈ word y ⊕ᵈ plam′ e
  {-# CATCHALL #-}
  plam′ b          = txt " ->" ⊕ᵈ (pure′ line ⊕ᵈ pex 0 true b >>=′ λ d → pure′ (nest indent d))

  -- A chain of `let`s is one group: flat when it fits, else each `in` starts a
  -- line; each value is a group of its own, so it stays after its `=` when it fits.
  plet : String → Expr → Expr → P Doc
  plet x v b = plet′ x v b >>=′ λ d → pure′ (group d)

  plet′ : String → Expr → Expr → P Doc
  plet′ x v (RLet y v′ c) = lhead x v ⊕ᵈ pure′ line ⊕ᵈ word "in" ⊕ᵈ txt " " ⊕ᵈ plet′ y v′ c
  {-# CATCHALL #-}
  plet′ x v b            = lhead x v ⊕ᵈ pure′ line ⊕ᵈ word "in" ⊕ᵈ txt " " ⊕ᵈ pex 0 true b

  lhead : String → Expr → P Doc
  lhead x v = word "let" ⊕ᵈ txt " " ⊕ᵈ word x ⊕ᵈ txt " ="
                ⊕ᵈ (pure′ line ⊕ᵈ pex 0 true v >>=′ λ d → pure′ (group (nest indent d)))

  pdes : Expr → String → Expr → String → Expr → P Doc
  pdes s x el y er =
    (word "destruct" ⊕ᵈ txt " " ⊕ᵈ pex 0 true s ⊕ᵈ txt " " ⊕ᵈ word "of"
      ⊕ᵈ (pure′ line ⊕ᵈ txt "{ " ⊕ᵈ word "Left" ⊕ᵈ txt " " ⊕ᵈ word x ⊕ᵈ txt " -> " ⊕ᵈ pex 0 true el
          ⊕ᵈ pure′ line ⊕ᵈ txt "; " ⊕ᵈ word "Right" ⊕ᵈ txt " " ⊕ᵈ word y ⊕ᵈ txt " -> " ⊕ᵈ pex 0 true er
          ⊕ᵈ pure′ line ⊕ᵈ txt "}" >>=′ λ d → pure′ (nest indent d)))
      >>=′ λ d → pure′ (group d)

------------------------------------------------------------------------
-- Declarations and the module
------------------------------------------------------------------------

private
  path : List String → P Doc
  path []           = pure′ empty
  path (x ∷ [])     = word x
  path (x ∷ xs@(_ ∷ _)) = word x ⊕ᵈ txt "." ⊕ᵈ path xs

  spaced : List String → P Doc
  spaced []       = pure′ empty
  spaced (x ∷ xs) = txt " " ⊕ᵈ word x ⊕ᵈ spaced xs

-- A declaration; every line it breaks is indented (an unindented line would
-- start the next declaration).
pdecl : Decl → P Doc
pdecl (DImport (mkImport p nothing))  = word "import" ⊕ᵈ txt " " ⊕ᵈ path p
pdecl (DImport (mkImport p (just a))) = word "import" ⊕ᵈ txt " " ⊕ᵈ path p ⊕ᵈ txt " " ⊕ᵈ word "as" ⊕ᵈ txt " " ⊕ᵈ word a
pdecl (DTypeAlias x ps A) =
  (word "type" ⊕ᵈ txt " " ⊕ᵈ word x ⊕ᵈ spaced ps ⊕ᵈ txt " =" ⊕ᵈ pure′ line ⊕ᵈ pty 0 true A)
    >>=′ λ d → pure′ (group (nest indent d))
pdecl (DSignature x A) =
  (word "signature" ⊕ᵈ txt " " ⊕ᵈ word x ⊕ᵈ txt " :" ⊕ᵈ pure′ line ⊕ᵈ pty 0 true A)
    >>=′ λ d → pure′ (group (nest indent d))
pdecl (DTypeSig x A) =
  (name x ⊕ᵈ txt " :" ⊕ᵈ pure′ line ⊕ᵈ pty 0 true A) >>=′ λ d → pure′ (group (nest indent d))
pdecl (DFunDef x e) with lams e
... | ps , b = (name x ⊕ᵈ spaced ps ⊕ᵈ txt " =" ⊕ᵈ pure′ line ⊕ᵈ pex 0 true b)
                 >>=′ λ d → pure′ (group (nest indent d))

-- | A module: its declarations, one per line, each after the notes that
-- stand before it; the notes after the last anchor at the end.
pmodule : Module → P Doc
pmodule (mkModule ds) = go ds
  where
    go : List Decl → P Doc
    go [] tv k = topNotes k (suc k) tv , k
    go (d ∷ ds) tv k with pdecl d tv k
    ... | dd , k′ with go ds tv k′
    ...   | rest , k″ = (topNotes k k′ tv <> dd <> newline <> rest) , k″

-- | A module in the canonical layout, with the comments of `items`.
format : Module → List Item → String
format m is = render (proj₁ (pmodule m (trivia is) 0))
