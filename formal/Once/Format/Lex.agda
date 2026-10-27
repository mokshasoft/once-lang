-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Format.Lex — the lexer, keeping what it skips (plan 0.124 step 1).
--
-- `lexItems` reads a text as the lexer does (`Parser.Lexer.tokenize`) and also
-- returns what the lexer drops, in place: each comment with its text, and each
-- line break the lexer swallows (a newline followed by an indented line, which
-- continues the line). Dropping those again gives exactly the lexer's tokens
-- (`tokens-lexItems`), so the formatter reads the same token stream the parser
-- does, and the comments ride beside it without a second syntax.
--
-- The worker mirrors `tokenize-WF` clause for clause, through the same
-- helpers and the same accessibility proofs, which is what makes the theorem
-- an induction with nothing to compute.
------------------------------------------------------------------------

module Once.Format.Lex where

open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char; isDigit)
open import Data.List using (List; []; _∷_; length; take)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _<_; _∸_; s≤s)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n<1+n; m≤n⇒m≤1+n; <⇒≤)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax)
open import Data.String using (String; fromList; toList)
open import Data.Integer using (+_)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Once.Parser.Token using (Token; TWord; TInt; TFloat; TString; TLParen; TRParen; TLBrace; TRBrace;
  TColon; TEquals; TArrow; TCaret1; TCaret0; TCaretW; TLambda; TComma; TSemicolon; TAt; TPipe; TDot;
  TPlus; TMinus; TStar; TSlash; TPercent; TAmpersand; TLt; TLe; TGt; TGe; TEqEq; TNeq; TBang; TNewline; TEOF)
open import Once.Parser.Lexer using (HeadK; hkWS; hkNL; hkCaret; hkDash; hkLBrace; hkLt; hkGt; hkEq; hkBang;
  hkLParen; hkRParen; hkRBrace; hkColon; hkLambda; hkComma; hkSemi; hkAt; hkPipe; hkPlus; hkStar; hkSlash;
  hkPct; hkAmp; hkDot; hkStr; hkGen; headK; Dash3; d-comment; d-arrow; d-minus; Caret4; c-1; c-0; c-w; c-gen;
  nlIndent; isEqHead; isDashHead; dashClass; caretClass; drop1; drop1-≤; adv; collectStringB; collectIdentB;
  collectDigitsB; collectFracB; skipLineB; skipBlockB; digitsToNat; isIdentStart; tokenize-WF; tokenize;
  tok-head; tok-str; tok-gen; tok-num; tok-nl; tok-op2; tok-lbrace; tok-minus; tok-caret)

------------------------------------------------------------------------
-- What the lexer reads: tokens, and what it skips
------------------------------------------------------------------------

data Item : Set where
  tok     : Token → Item     -- a token, as the lexer returns it
  comment : String → Item    -- a comment's text, `--`/`{-` included, its line end excluded
  cont    : Item             -- a line break the lexer swallows (the next line is indented)

-- The tokens of an item stream.
tokensOf : List Item → List Token
tokensOf []                = []
tokensOf (tok t ∷ is)      = t ∷ tokensOf is
tokensOf (comment _ ∷ is)  = tokensOf is
tokensOf (cont ∷ is)       = tokensOf is

-- The characters a skip consumed: the input up to what it left.
consumed : List Char → List Char → List Char
consumed cs rest = take (length cs ∸ length rest) cs

------------------------------------------------------------------------
-- The worker, `tokenize-WF` clause for clause
------------------------------------------------------------------------

items-WF : (cs : List Char) (off : ℕ) → Acc _<_ (length cs) → List Item
it-head  : (c : Char) (cs : List Char) (off : ℕ) → (∀ {y} → y < suc (length cs) → Acc _<_ y) → HeadK → List Item
it-str   : (cs : List Char) (off : ℕ) → (∀ {y} → y < suc (length cs) → Acc _<_ y) →
           Maybe (Σ[ s ∈ List Char ] Σ[ rest ∈ List Char ] length rest < length cs) → List Item
it-gen   : (c : Char) (cs : List Char) (off : ℕ) → (∀ {y} → y < suc (length cs) → Acc _<_ y) →
           Bool → Bool → List Item
it-num   : (c : Char) (cs : List Char) (off : ℕ) → (∀ {y} → y < suc (length cs) → Acc _<_ y) →
           (digits rest : List Char) → Data.Nat._≤_ (length rest) (length cs) →
           Maybe (Σ[ f ∈ List Char ] Σ[ r ∈ List Char ] length r < length rest) → List Item
it-nl    : (cs : List Char) (off : ℕ) → (∀ {y} → y < suc (length cs) → Acc _<_ y) → Bool → List Item
it-op2   : (cs : List Char) (off : ℕ) → (∀ {y} → y < suc (length cs) → Acc _<_ y) →
           Token → Token → Bool → List Item
it-lbrace : (cs : List Char) (off : ℕ) → (∀ {y} → y < suc (length cs) → Acc _<_ y) → Bool → List Item
it-minus : (cs : List Char) (off : ℕ) → (∀ {y} → y < suc (length cs) → Acc _<_ y) → Dash3 → List Item
it-caret : (cs : List Char) (off : ℕ) → (∀ {y} → y < suc (length cs) → Acc _<_ y) → Caret4 → List Item

items-WF [] off _ = tok TEOF ∷ []
items-WF (c ∷ cs) off (acc rec) = it-head c cs off rec (headK c)

it-head c cs off rec hkWS     = items-WF cs (adv cs cs off) (rec (s≤s ≤-refl))
it-head c cs off rec hkNL     = it-nl cs off rec (nlIndent cs)
it-head c cs off rec hkCaret  = it-caret cs off rec (caretClass cs)
it-head c cs off rec hkDash   = it-minus cs off rec (dashClass cs)
it-head c cs off rec hkLBrace = it-lbrace cs off rec (isDashHead cs)
it-head c cs off rec hkLt     = it-op2 cs off rec TLe TLt (isEqHead cs)
it-head c cs off rec hkGt     = it-op2 cs off rec TGe TGt (isEqHead cs)
it-head c cs off rec hkEq     = it-op2 cs off rec TEqEq TEquals (isEqHead cs)
it-head c cs off rec hkBang   = it-op2 cs off rec TNeq TBang (isEqHead cs)
it-head c cs off rec hkLParen = tok TLParen    ∷ items-WF cs (adv cs cs off) (rec (s≤s ≤-refl))
it-head c cs off rec hkRParen = tok TRParen    ∷ items-WF cs (adv cs cs off) (rec (s≤s ≤-refl))
it-head c cs off rec hkRBrace = tok TRBrace    ∷ items-WF cs (adv cs cs off) (rec (s≤s ≤-refl))
it-head c cs off rec hkColon  = tok TColon     ∷ items-WF cs (adv cs cs off) (rec (s≤s ≤-refl))
it-head c cs off rec hkLambda = tok TLambda    ∷ items-WF cs (adv cs cs off) (rec (s≤s ≤-refl))
it-head c cs off rec hkComma  = tok TComma     ∷ items-WF cs (adv cs cs off) (rec (s≤s ≤-refl))
it-head c cs off rec hkSemi   = tok TSemicolon ∷ items-WF cs (adv cs cs off) (rec (s≤s ≤-refl))
it-head c cs off rec hkAt     = tok TAt        ∷ items-WF cs (adv cs cs off) (rec (s≤s ≤-refl))
it-head c cs off rec hkPipe   = tok TPipe      ∷ items-WF cs (adv cs cs off) (rec (s≤s ≤-refl))
it-head c cs off rec hkPlus   = tok TPlus      ∷ items-WF cs (adv cs cs off) (rec (s≤s ≤-refl))
it-head c cs off rec hkStar   = tok TStar      ∷ items-WF cs (adv cs cs off) (rec (s≤s ≤-refl))
it-head c cs off rec hkSlash  = tok TSlash     ∷ items-WF cs (adv cs cs off) (rec (s≤s ≤-refl))
it-head c cs off rec hkPct    = tok TPercent   ∷ items-WF cs (adv cs cs off) (rec (s≤s ≤-refl))
it-head c cs off rec hkAmp    = tok TAmpersand ∷ items-WF cs (adv cs cs off) (rec (s≤s ≤-refl))
it-head c cs off rec hkDot    = tok TDot       ∷ items-WF cs (adv cs cs off) (rec (s≤s ≤-refl))
it-head c cs off rec hkStr    = it-str cs off rec (collectStringB cs)
it-head c cs off rec hkGen    = it-gen c cs off rec (isDigit c) (isIdentStart c)

it-str cs off rec (just (s , rest , bnd)) =
  tok (TString (fromList s)) ∷ items-WF rest (adv cs rest off) (rec (m≤n⇒m≤1+n bnd))
it-str cs off rec nothing = []
it-gen c cs off rec true  _     =
  let (digits , rest , bnd) = collectDigitsB cs
  in  it-num c cs off rec digits rest bnd (collectFracB rest)
it-gen c cs off rec false true  =
  let (ident , rest , bnd) = collectIdentB cs
  in  tok (TWord (fromList (c ∷ ident))) ∷ items-WF rest (adv cs rest off) (rec (s≤s bnd))
it-gen c cs off rec false false = []

it-num c cs off rec digits rest bnd (just (frac , rest' , fbnd)) =
  tok (TFloat (digitsToNat (c ∷ digits)) (digitsToNat frac) (length frac) off)
    ∷ items-WF rest' (adv cs rest' off) (rec (s≤s (≤-trans (<⇒≤ fbnd) bnd)))
it-num c cs off rec digits rest bnd nothing =
  tok (TInt (+ digitsToNat (c ∷ digits)) off) ∷ items-WF rest (adv cs rest off) (rec (s≤s bnd))

it-nl cs off rec true  = cont ∷ items-WF cs (adv cs cs off) (rec (n<1+n _))
it-nl cs off rec false = tok TNewline ∷ items-WF cs (adv cs cs off) (rec (n<1+n _))

it-op2 cs off rec t2 t1 true  = tok t2 ∷ items-WF (drop1 cs) (adv cs (drop1 cs) off) (rec (s≤s (drop1-≤ cs)))
it-op2 cs off rec t2 t1 false = tok t1 ∷ items-WF cs (adv cs cs off) (rec (n<1+n _))

it-lbrace cs off rec true  =
  comment (fromList ('{' ∷ consumed cs (proj₁ (skipBlockB 1 (drop1 cs)))))
    ∷ items-WF (proj₁ (skipBlockB 1 (drop1 cs))) (adv cs (proj₁ (skipBlockB 1 (drop1 cs))) off)
               (rec (s≤s (≤-trans (proj₂ (skipBlockB 1 (drop1 cs))) (drop1-≤ cs))))
it-lbrace cs off rec false = tok TLBrace ∷ items-WF cs (adv cs cs off) (rec (n<1+n _))

it-minus cs off rec d-comment =
  comment (fromList ('-' ∷ consumed cs (proj₁ (skipLineB (drop1 cs)))))
    ∷ items-WF (proj₁ (skipLineB (drop1 cs))) (adv cs (proj₁ (skipLineB (drop1 cs))) off)
               (rec (s≤s (≤-trans (proj₂ (skipLineB (drop1 cs))) (drop1-≤ cs))))
it-minus cs off rec d-arrow   = tok TArrow ∷ items-WF (drop1 cs) (adv cs (drop1 cs) off) (rec (s≤s (drop1-≤ cs)))
it-minus cs off rec d-minus   = tok TMinus ∷ items-WF cs (adv cs cs off) (rec (n<1+n _))

it-caret cs off rec c-1   = tok TCaret1 ∷ items-WF (drop1 cs) (adv cs (drop1 cs) off) (rec (s≤s (drop1-≤ cs)))
it-caret cs off rec c-0   = tok TCaret0 ∷ items-WF (drop1 cs) (adv cs (drop1 cs) off) (rec (s≤s (drop1-≤ cs)))
it-caret cs off rec c-w   = tok TCaretW ∷ items-WF (drop1 cs) (adv cs (drop1 cs) off) (rec (s≤s (drop1-≤ cs)))
it-caret cs off rec c-gen = []

-- | A text's items.
lexItems : List Char → List Item
lexItems cs = items-WF cs 0 (<-wellFounded (length cs))

------------------------------------------------------------------------
-- Dropping what the lexer skips gives the lexer's tokens
------------------------------------------------------------------------

tokens-WF  : ∀ cs off a → tokensOf (items-WF cs off a) ≡ tokenize-WF cs off a
tokens-head : ∀ c cs off (rec : ∀ {y} → y < suc (length cs) → Acc _<_ y) k → tokensOf (it-head c cs off rec k) ≡ tok-head c cs off rec k
tokens-str : ∀ cs off (rec : ∀ {y} → y < suc (length cs) → Acc _<_ y) m → tokensOf (it-str cs off rec m) ≡ tok-str cs off rec m
tokens-gen : ∀ c cs off (rec : ∀ {y} → y < suc (length cs) → Acc _<_ y) b₁ b₂ → tokensOf (it-gen c cs off rec b₁ b₂) ≡ tok-gen c cs off rec b₁ b₂
tokens-num : ∀ c cs off (rec : ∀ {y} → y < suc (length cs) → Acc _<_ y) ds rest bnd m → tokensOf (it-num c cs off rec ds rest bnd m) ≡ tok-num c cs off rec ds rest bnd m
tokens-nl  : ∀ cs off (rec : ∀ {y} → y < suc (length cs) → Acc _<_ y) b → tokensOf (it-nl cs off rec b) ≡ tok-nl cs off rec b
tokens-op2 : ∀ cs off (rec : ∀ {y} → y < suc (length cs) → Acc _<_ y) t2 t1 b → tokensOf (it-op2 cs off rec t2 t1 b) ≡ tok-op2 cs off rec t2 t1 b
tokens-lbrace : ∀ cs off (rec : ∀ {y} → y < suc (length cs) → Acc _<_ y) b → tokensOf (it-lbrace cs off rec b) ≡ tok-lbrace cs off rec b
tokens-minus : ∀ cs off (rec : ∀ {y} → y < suc (length cs) → Acc _<_ y) d → tokensOf (it-minus cs off rec d) ≡ tok-minus cs off rec d
tokens-caret : ∀ cs off (rec : ∀ {y} → y < suc (length cs) → Acc _<_ y) k → tokensOf (it-caret cs off rec k) ≡ tok-caret cs off rec k

tokens-WF [] off _ = refl
tokens-WF (c ∷ cs) off (acc rec) = tokens-head c cs off rec (headK c)

tokens-head c cs off rec hkWS     = tokens-WF cs _ _
tokens-head c cs off rec hkNL     = tokens-nl cs off rec (nlIndent cs)
tokens-head c cs off rec hkCaret  = tokens-caret cs off rec (caretClass cs)
tokens-head c cs off rec hkDash   = tokens-minus cs off rec (dashClass cs)
tokens-head c cs off rec hkLBrace = tokens-lbrace cs off rec (isDashHead cs)
tokens-head c cs off rec hkLt     = tokens-op2 cs off rec TLe TLt (isEqHead cs)
tokens-head c cs off rec hkGt     = tokens-op2 cs off rec TGe TGt (isEqHead cs)
tokens-head c cs off rec hkEq     = tokens-op2 cs off rec TEqEq TEquals (isEqHead cs)
tokens-head c cs off rec hkBang   = tokens-op2 cs off rec TNeq TBang (isEqHead cs)
tokens-head c cs off rec hkLParen = cong (TLParen ∷_) (tokens-WF cs _ _)
tokens-head c cs off rec hkRParen = cong (TRParen ∷_) (tokens-WF cs _ _)
tokens-head c cs off rec hkRBrace = cong (TRBrace ∷_) (tokens-WF cs _ _)
tokens-head c cs off rec hkColon  = cong (TColon ∷_) (tokens-WF cs _ _)
tokens-head c cs off rec hkLambda = cong (TLambda ∷_) (tokens-WF cs _ _)
tokens-head c cs off rec hkComma  = cong (TComma ∷_) (tokens-WF cs _ _)
tokens-head c cs off rec hkSemi   = cong (TSemicolon ∷_) (tokens-WF cs _ _)
tokens-head c cs off rec hkAt     = cong (TAt ∷_) (tokens-WF cs _ _)
tokens-head c cs off rec hkPipe   = cong (TPipe ∷_) (tokens-WF cs _ _)
tokens-head c cs off rec hkPlus   = cong (TPlus ∷_) (tokens-WF cs _ _)
tokens-head c cs off rec hkStar   = cong (TStar ∷_) (tokens-WF cs _ _)
tokens-head c cs off rec hkSlash  = cong (TSlash ∷_) (tokens-WF cs _ _)
tokens-head c cs off rec hkPct    = cong (TPercent ∷_) (tokens-WF cs _ _)
tokens-head c cs off rec hkAmp    = cong (TAmpersand ∷_) (tokens-WF cs _ _)
tokens-head c cs off rec hkDot    = cong (TDot ∷_) (tokens-WF cs _ _)
tokens-head c cs off rec hkStr    = tokens-str cs off rec (collectStringB cs)
tokens-head c cs off rec hkGen    = tokens-gen c cs off rec (isDigit c) (isIdentStart c)

tokens-str cs off rec (just (s , rest , bnd)) = cong (TString (fromList s) ∷_) (tokens-WF rest _ _)
tokens-str cs off rec nothing = refl
tokens-gen c cs off rec true _ =
  tokens-num c cs off rec (proj₁ (collectDigitsB cs)) (proj₁ (proj₂ (collectDigitsB cs)))
    (proj₂ (proj₂ (collectDigitsB cs))) (collectFracB (proj₁ (proj₂ (collectDigitsB cs))))
tokens-gen c cs off rec false true =
  cong (TWord (fromList (c ∷ proj₁ (collectIdentB cs))) ∷_) (tokens-WF (proj₁ (proj₂ (collectIdentB cs))) _ _)
tokens-gen c cs off rec false false = refl

tokens-num c cs off rec ds rest bnd (just (frac , rest' , fbnd)) = cong (_ ∷_) (tokens-WF rest' _ _)
tokens-num c cs off rec ds rest bnd nothing = cong (_ ∷_) (tokens-WF rest _ _)

tokens-nl cs off rec true  = tokens-WF cs _ _
tokens-nl cs off rec false = cong (TNewline ∷_) (tokens-WF cs _ _)

tokens-op2 cs off rec t2 t1 true  = cong (t2 ∷_) (tokens-WF (drop1 cs) _ _)
tokens-op2 cs off rec t2 t1 false = cong (t1 ∷_) (tokens-WF cs _ _)

tokens-lbrace cs off rec true  = tokens-WF (proj₁ (skipBlockB 1 (drop1 cs))) _ _
tokens-lbrace cs off rec false = cong (TLBrace ∷_) (tokens-WF cs _ _)

tokens-minus cs off rec d-comment = tokens-WF (proj₁ (skipLineB (drop1 cs))) _ _
tokens-minus cs off rec d-arrow   = cong (TArrow ∷_) (tokens-WF (drop1 cs) _ _)
tokens-minus cs off rec d-minus   = cong (TMinus ∷_) (tokens-WF cs _ _)

tokens-caret cs off rec c-1   = cong (TCaret1 ∷_) (tokens-WF (drop1 cs) _ _)
tokens-caret cs off rec c-0   = cong (TCaret0 ∷_) (tokens-WF (drop1 cs) _ _)
tokens-caret cs off rec c-w   = cong (TCaretW ∷_) (tokens-WF (drop1 cs) _ _)
tokens-caret cs off rec c-gen = refl

-- | The formatter reads the parser's tokens.
tokens-lexItems : ∀ cs → tokensOf (lexItems cs) ≡ tokenize cs
tokens-lexItems cs = tokens-WF cs 0 (<-wellFounded (length cs))
