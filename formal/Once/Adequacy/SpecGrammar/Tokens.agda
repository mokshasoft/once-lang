-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecGrammar.Tokens — the compiler's tokens against the
-- Spec's: `forget` (from `Once.Adequacy.SpecLexing`) read backwards.
--
-- A grammar bridge runs a Spec derivation over `map forget toks` back to the
-- compiler's relation over `toks`; these are the inversions it needs: a
-- forgotten list that is a cons was a cons, and a forgotten token that is
-- not a literal was that very token.
------------------------------------------------------------------------

module Once.Adequacy.SpecGrammar.Tokens where

open import Data.List using (List; []; _∷_; map; _++_)
open import Data.Nat using (ℕ)
open import Data.Integer using (ℤ)
open import Data.String using (String)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Once.Spec.Surface.Lexing using (Token)
open Token
import Once.Parser.Token as P
open import Once.Adequacy.SpecLexing using (forget)

-- A forgotten list that is a cons.
data ConsView (u : Token) (us : List Token) : List P.Token → Set where
  cv : ∀ {t toks} → forget t ≡ u → map forget toks ≡ us → ConsView u us (t ∷ toks)

uncons : ∀ {toks u us} → map forget toks ≡ u ∷ us → ConsView u us toks
uncons {t ∷ toks} refl = cv refl refl

unnil : ∀ {toks} → map forget toks ≡ [] → toks ≡ []
unnil {[]} refl = refl

-- A forgotten token, read back.
data TokView : P.Token → Token → Set where
  tv-word   : ∀ {s} → TokView (P.TWord s) (TWord s)
  tv-int    : ∀ {n p} → TokView (P.TInt n p) (TInt n)
  tv-float  : ∀ {i f l p} → TokView (P.TFloat i f l p) (TFloat i f l)
  tv-string : ∀ {s} → TokView (P.TString s) (TString s)
  tv-lparen : TokView P.TLParen TLParen
  tv-rparen : TokView P.TRParen TRParen
  tv-lbrace : TokView P.TLBrace TLBrace
  tv-rbrace : TokView P.TRBrace TRBrace
  tv-colon : TokView P.TColon TColon
  tv-equals : TokView P.TEquals TEquals
  tv-arrow : TokView P.TArrow TArrow
  tv-caret1 : TokView P.TCaret1 TCaret1
  tv-caret0 : TokView P.TCaret0 TCaret0
  tv-caretw : TokView P.TCaretW TCaretW
  tv-lambda : TokView P.TLambda TLambda
  tv-comma : TokView P.TComma TComma
  tv-semicolon : TokView P.TSemicolon TSemicolon
  tv-at : TokView P.TAt TAt
  tv-pipe : TokView P.TPipe TPipe
  tv-dot : TokView P.TDot TDot
  tv-plus : TokView P.TPlus TPlus
  tv-minus : TokView P.TMinus TMinus
  tv-star : TokView P.TStar TStar
  tv-slash : TokView P.TSlash TSlash
  tv-percent : TokView P.TPercent TPercent
  tv-ampersand : TokView P.TAmpersand TAmpersand
  tv-lt : TokView P.TLt TLt
  tv-le : TokView P.TLe TLe
  tv-gt : TokView P.TGt TGt
  tv-ge : TokView P.TGe TGe
  tv-eqeq : TokView P.TEqEq TEqEq
  tv-neq : TokView P.TNeq TNeq
  tv-bang : TokView P.TBang TBang
  tv-newline : TokView P.TNewline TNewline
  tv-eof : TokView P.TEOF TEOF

tok-view : ∀ t → TokView t (forget t)
tok-view (P.TWord s)        = tv-word
tok-view (P.TInt n p)       = tv-int
tok-view (P.TFloat i f l p) = tv-float
tok-view (P.TString s)      = tv-string
tok-view P.TLParen = tv-lparen
tok-view P.TRParen = tv-rparen
tok-view P.TLBrace = tv-lbrace
tok-view P.TRBrace = tv-rbrace
tok-view P.TColon = tv-colon
tok-view P.TEquals = tv-equals
tok-view P.TArrow = tv-arrow
tok-view P.TCaret1 = tv-caret1
tok-view P.TCaret0 = tv-caret0
tok-view P.TCaretW = tv-caretw
tok-view P.TLambda = tv-lambda
tok-view P.TComma = tv-comma
tok-view P.TSemicolon = tv-semicolon
tok-view P.TAt = tv-at
tok-view P.TPipe = tv-pipe
tok-view P.TDot = tv-dot
tok-view P.TPlus = tv-plus
tok-view P.TMinus = tv-minus
tok-view P.TStar = tv-star
tok-view P.TSlash = tv-slash
tok-view P.TPercent = tv-percent
tok-view P.TAmpersand = tv-ampersand
tok-view P.TLt = tv-lt
tok-view P.TLe = tv-le
tok-view P.TGt = tv-gt
tok-view P.TGe = tv-ge
tok-view P.TEqEq = tv-eqeq
tok-view P.TNeq = tv-neq
tok-view P.TBang = tv-bang
tok-view P.TNewline = tv-newline
tok-view P.TEOF = tv-eof

tview : ∀ {t u} → forget t ≡ u → TokView t u
tview {t} refl = tok-view t


-- A literal carries what `forget` drops; every other token is read back as itself.
isLit : Token → Bool
isLit (TInt _)       = true
isLit (TFloat _ _ _) = true
{-# CATCHALL #-}
isLit _              = false

back : Token → P.Token
back (TWord s)        = P.TWord s
back (TInt n)         = P.TInt n 0
back (TFloat i f l)   = P.TFloat i f l 0
back (TString s)      = P.TString s
back TLParen = P.TLParen
back TRParen = P.TRParen
back TLBrace = P.TLBrace
back TRBrace = P.TRBrace
back TColon = P.TColon
back TEquals = P.TEquals
back TArrow = P.TArrow
back TCaret1 = P.TCaret1
back TCaret0 = P.TCaret0
back TCaretW = P.TCaretW
back TLambda = P.TLambda
back TComma = P.TComma
back TSemicolon = P.TSemicolon
back TAt = P.TAt
back TPipe = P.TPipe
back TDot = P.TDot
back TPlus = P.TPlus
back TMinus = P.TMinus
back TStar = P.TStar
back TSlash = P.TSlash
back TPercent = P.TPercent
back TAmpersand = P.TAmpersand
back TLt = P.TLt
back TLe = P.TLe
back TGt = P.TGt
back TGe = P.TGe
back TEqEq = P.TEqEq
back TNeq = P.TNeq
back TBang = P.TBang
back TNewline = P.TNewline
back TEOF = P.TEOF

back-view : ∀ {t u} → TokView t u → isLit u ≡ false → t ≡ back u
back-view tv-word   _ = refl
back-view tv-int    ()
back-view tv-float  ()
back-view tv-string _ = refl
back-view tv-lparen _ = refl
back-view tv-rparen _ = refl
back-view tv-lbrace _ = refl
back-view tv-rbrace _ = refl
back-view tv-colon _ = refl
back-view tv-equals _ = refl
back-view tv-arrow _ = refl
back-view tv-caret1 _ = refl
back-view tv-caret0 _ = refl
back-view tv-caretw _ = refl
back-view tv-lambda _ = refl
back-view tv-comma _ = refl
back-view tv-semicolon _ = refl
back-view tv-at _ = refl
back-view tv-pipe _ = refl
back-view tv-dot _ = refl
back-view tv-plus _ = refl
back-view tv-minus _ = refl
back-view tv-star _ = refl
back-view tv-slash _ = refl
back-view tv-percent _ = refl
back-view tv-ampersand _ = refl
back-view tv-lt _ = refl
back-view tv-le _ = refl
back-view tv-gt _ = refl
back-view tv-ge _ = refl
back-view tv-eqeq _ = refl
back-view tv-neq _ = refl
back-view tv-bang _ = refl
back-view tv-newline _ = refl
back-view tv-eof _ = refl

back-inv : ∀ {t u} → isLit u ≡ false → forget t ≡ u → t ≡ back u
back-inv nl e = back-view (tview e) nl

-- Read a forgotten list's head back, in continuation-passing style.
private
  step′ : ∀ {u us} (K : List P.Token → Set) {toks} → isLit u ≡ false → ConsView u us toks
        → (∀ {toks′} → map forget toks′ ≡ us → K (back u ∷ toks′)) → K toks
  step′ K nl (cv {t} {toks′} ft er) k = subst (λ x → K (x ∷ toks′)) (sym (back-inv nl ft)) (k er)

step : ∀ {u us} (K : List P.Token → Set) {toks} → isLit u ≡ false → map forget toks ≡ u ∷ us
     → (∀ {toks′} → map forget toks′ ≡ us → K (back u ∷ toks′)) → K toks
step K nl e k = step′ K nl (uncons e) k

-- The same, as an equation.
peel : ∀ {u us} {toks} → isLit u ≡ false → map forget toks ≡ u ∷ us
     → Σ[ toks′ ∈ List P.Token ] (toks ≡ back u ∷ toks′ × map forget toks′ ≡ us)
peel {toks = toks} nl e = step (λ x → Σ[ toks′ ∈ List P.Token ] (x ≡ back _ ∷ toks′ × map forget toks′ ≡ _)) nl e
  (λ {toks′} e′ → toks′ , refl , e′)


-- Several heads at once.
data NonLits : List Token → Set where
  []  : NonLits []
  _∷_ : ∀ {u us} → isLit u ≡ false → NonLits us → NonLits (u ∷ us)

private
  peels-cons : ∀ u us {toks₁ toks r} → (Σ[ toks′ ∈ List P.Token ] (toks₁ ≡ map back us ++ toks′ × map forget toks′ ≡ r))
             → toks ≡ back u ∷ toks₁ → Σ[ toks′ ∈ List P.Token ] (toks ≡ back u ∷ map back us ++ toks′ × map forget toks′ ≡ r)
  peels-cons u us (toks′ , refl , e′) refl = toks′ , refl , e′

peels : ∀ us {toks r} → NonLits us → map forget toks ≡ us ++ r
      → Σ[ toks′ ∈ List P.Token ] (toks ≡ map back us ++ toks′ × map forget toks′ ≡ r)
peels []       []         e = _ , refl , e
peels (u ∷ us) (nl ∷ nls) e = peels-go (peel nl e)
  where
    peels-go : Σ[ toks₁ ∈ List P.Token ] (_ ≡ back u ∷ toks₁ × map forget toks₁ ≡ us ++ _) → _
    peels-go (toks₁ , eq , e₁) = peels-cons u us (peels us nls e₁) eq

-- A literal head.
private
  int′ : ∀ {n r} (K : List P.Token → Set) {toks} → ConsView (TInt n) r toks
       → (∀ p {toks′} → map forget toks′ ≡ r → K (P.TInt n p ∷ toks′)) → K toks
  int′ K (cv ft er) k = int″ K (tview ft) er k
    where
      int″ : ∀ {n r t toks′} (K : List P.Token → Set) → TokView t (TInt n) → map forget toks′ ≡ r
           → (∀ p {toks′} → map forget toks′ ≡ r → K (P.TInt n p ∷ toks′)) → K (t ∷ toks′)
      int″ K tv-int er k = k _ er

  float′ : ∀ {i f l r} (K : List P.Token → Set) {toks} → ConsView (TFloat i f l) r toks
         → (∀ p {toks′} → map forget toks′ ≡ r → K (P.TFloat i f l p ∷ toks′)) → K toks
  float′ K (cv ft er) k = float″ K (tview ft) er k
    where
      float″ : ∀ {i f l r t toks′} (K : List P.Token → Set) → TokView t (TFloat i f l) → map forget toks′ ≡ r
             → (∀ p {toks′} → map forget toks′ ≡ r → K (P.TFloat i f l p ∷ toks′)) → K (t ∷ toks′)
      float″ K tv-float er k = k _ er

stepInt : ∀ {n r} (K : List P.Token → Set) {toks} → map forget toks ≡ TInt n ∷ r
        → (∀ p {toks′} → map forget toks′ ≡ r → K (P.TInt n p ∷ toks′)) → K toks
stepInt K e k = int′ K (uncons e) k

stepFloat : ∀ {i f l r} (K : List P.Token → Set) {toks} → map forget toks ≡ TFloat i f l ∷ r
          → (∀ p {toks′} → map forget toks′ ≡ r → K (P.TFloat i f l p ∷ toks′)) → K toks
stepFloat K e k = float′ K (uncons e) k
