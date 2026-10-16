-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecGrammar.ExprHeads — the compiler's expression-grammar
-- lookaheads (`NotDot`, `NotCmp`, `NotAtomStart`, `NotQualPrefix`,
-- `AppArgOk`, `isReserved`) against the Spec's, over the forgotten tokens.
-- Mostly generated case splits on the head token.
------------------------------------------------------------------------

module Once.Adequacy.SpecGrammar.ExprHeads where

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; map)
open import Data.String using (String)
open import Data.String.Properties using (_≟_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (isYes)

open import Once.Spec.Surface.Lexing using (Token)
open Token
open import Once.Spec.Surface.Grammar
  using (Starts; starts; Reserved; r-in; r-of; r-let; r-destruct; r-Left; r-Right;
         ArgStart; as-paren; as-lambda; as-int; as-float; as-word; QualSuffix; qual-suffix;
         CompareToken; ct-lt; ct-le; ct-gt; ct-ge; ct-eq; ct-ne; AddToken; at-plus; at-minus;
         MulToken; mt-star; mt-slash; mt-pct)
import Once.Parser.Token as P
open import Once.Parser.ExprRelation
  using (isReserved; NotDot; NotCmp; NotAdd; NotMul; NotAtomStart; AppArgOk; NotTWord; NotQualPrefix)
open NotAtomStart
open AppArgOk
open NotTWord
open NotQualPrefix
open import Once.Adequacy.SpecGrammar.Tokens using (forget)

private
  F : List P.Token → List Token
  F = map forget

------------------------------------------------------------------------
-- Reserved words
------------------------------------------------------------------------

data ResView (s : String) : Bool → Set where
  rv-yes : Reserved s → ResView s true
  rv-no  : ¬ Reserved s → ResView s false

private
  not-reserved : ∀ {s} → s ≢ "in" → s ≢ "of" → s ≢ "let" → s ≢ "destruct" → s ≢ "Left" → s ≢ "Right" → ¬ Reserved s
  not-reserved a _ _ _ _ _ r-in       = a refl
  not-reserved _ b _ _ _ _ r-of       = b refl
  not-reserved _ _ c _ _ _ r-let      = c refl
  not-reserved _ _ _ d _ _ r-destruct = d refl
  not-reserved _ _ _ _ e _ r-Left     = e refl
  not-reserved _ _ _ _ _ f r-Right    = f refl

  rv-step : ∀ s (d₁ : Dec (s ≡ "in")) (d₂ : Dec (s ≡ "of")) (d₃ : Dec (s ≡ "let")) (d₄ : Dec (s ≡ "destruct"))
            (d₅ : Dec (s ≡ "Left")) (d₆ : Dec (s ≡ "Right"))
          → ResView s (isYes d₁ ∨ isYes d₂ ∨ isYes d₃ ∨ isYes d₄ ∨ isYes d₅ ∨ isYes d₆)
  rv-step s (yes refl) _ _ _ _ _ = rv-yes r-in
  rv-step s (no _) (yes refl) _ _ _ _ = rv-yes r-of
  rv-step s (no _) (no _) (yes refl) _ _ _ = rv-yes r-let
  rv-step s (no _) (no _) (no _) (yes refl) _ _ = rv-yes r-destruct
  rv-step s (no _) (no _) (no _) (no _) (yes refl) _ = rv-yes r-Left
  rv-step s (no _) (no _) (no _) (no _) (no _) (yes refl) = rv-yes r-Right
  rv-step s (no a) (no b) (no c) (no d) (no e) (no f) = rv-no (not-reserved a b c d e f)

res-view : ∀ s → ResView s (isReserved s)
res-view s = rv-step s (s ≟ "in") (s ≟ "of") (s ≟ "let") (s ≟ "destruct") (s ≟ "Left") (s ≟ "Right")

private
  rv-true : ∀ {s b} → ResView s b → b ≡ true → Reserved s
  rv-true (rv-yes r) _ = r
  rv-true (rv-no _) ()

  rv-false : ∀ {s b} → ResView s b → b ≡ false → ¬ Reserved s
  rv-false (rv-yes _) ()
  rv-false (rv-no n) _ = n

  rv-not : ∀ {s b} → ResView s b → ¬ Reserved s → b ≡ false
  rv-not (rv-yes r) n = ⊥-elim (n r)
  rv-not (rv-no _) _ = refl

  rv-is : ∀ {s b} → ResView s b → ¬ ¬ Reserved s → b ≡ true
  rv-is (rv-yes _) _ = refl
  rv-is (rv-no n) k = ⊥-elim (k n)

reserved-true : ∀ {s} → isReserved s ≡ true → Reserved s
reserved-true {s} = rv-true (res-view s)

reserved-false→ : ∀ {s} → isReserved s ≡ false → ¬ Reserved s
reserved-false→ {s} = rv-false (res-view s)

reserved-false : ∀ {s} → ¬ Reserved s → isReserved s ≡ false
reserved-false {s} = rv-not (res-view s)

reserved-is : ∀ {s} → ¬ ¬ Reserved s → isReserved s ≡ true
reserved-is {s} = rv-is (res-view s)

-- A token stream that starts with a string literal (no Spec rule reads one).
data StrHead : List Token → Set where
  str-head : ∀ {s ts} → StrHead (TString s ∷ ts)

notDot→TDot : ∀ toks → NotDot toks → ¬ Starts (F toks) TDot
notDot→TDot [] _ ()
notDot→TDot ((P.TWord _) ∷ _) _ ()
notDot→TDot ((P.TInt _ _) ∷ _) _ ()
notDot→TDot ((P.TFloat _ _ _ _) ∷ _) _ ()
notDot→TDot ((P.TString _) ∷ _) _ ()
notDot→TDot (P.TLParen ∷ _) _ ()
notDot→TDot (P.TRParen ∷ _) _ ()
notDot→TDot (P.TLBrace ∷ _) _ ()
notDot→TDot (P.TRBrace ∷ _) _ ()
notDot→TDot (P.TColon ∷ _) _ ()
notDot→TDot (P.TEquals ∷ _) _ ()
notDot→TDot (P.TArrow ∷ _) _ ()
notDot→TDot (P.TCaret1 ∷ _) _ ()
notDot→TDot (P.TCaret0 ∷ _) _ ()
notDot→TDot (P.TCaretW ∷ _) _ ()
notDot→TDot (P.TLambda ∷ _) _ ()
notDot→TDot (P.TComma ∷ _) _ ()
notDot→TDot (P.TSemicolon ∷ _) _ ()
notDot→TDot (P.TAt ∷ _) _ ()
notDot→TDot (P.TPipe ∷ _) _ ()
notDot→TDot (P.TDot ∷ _) ()
notDot→TDot (P.TPlus ∷ _) _ ()
notDot→TDot (P.TMinus ∷ _) _ ()
notDot→TDot (P.TStar ∷ _) _ ()
notDot→TDot (P.TSlash ∷ _) _ ()
notDot→TDot (P.TPercent ∷ _) _ ()
notDot→TDot (P.TAmpersand ∷ _) _ ()
notDot→TDot (P.TLt ∷ _) _ ()
notDot→TDot (P.TLe ∷ _) _ ()
notDot→TDot (P.TGt ∷ _) _ ()
notDot→TDot (P.TGe ∷ _) _ ()
notDot→TDot (P.TEqEq ∷ _) _ ()
notDot→TDot (P.TNeq ∷ _) _ ()
notDot→TDot (P.TBang ∷ _) _ ()
notDot→TDot (P.TNewline ∷ _) _ ()
notDot→TDot (P.TEOF ∷ _) _ ()

notDot← : ∀ toks → ¬ Starts (F toks) TDot → NotDot toks
notDot← [] _ = tt
notDot← ((P.TWord _) ∷ _) _ = tt
notDot← ((P.TInt _ _) ∷ _) _ = tt
notDot← ((P.TFloat _ _ _ _) ∷ _) _ = tt
notDot← ((P.TString _) ∷ _) _ = tt
notDot← (P.TLParen ∷ _) _ = tt
notDot← (P.TRParen ∷ _) _ = tt
notDot← (P.TLBrace ∷ _) _ = tt
notDot← (P.TRBrace ∷ _) _ = tt
notDot← (P.TColon ∷ _) _ = tt
notDot← (P.TEquals ∷ _) _ = tt
notDot← (P.TArrow ∷ _) _ = tt
notDot← (P.TCaret1 ∷ _) _ = tt
notDot← (P.TCaret0 ∷ _) _ = tt
notDot← (P.TCaretW ∷ _) _ = tt
notDot← (P.TLambda ∷ _) _ = tt
notDot← (P.TComma ∷ _) _ = tt
notDot← (P.TSemicolon ∷ _) _ = tt
notDot← (P.TAt ∷ _) _ = tt
notDot← (P.TPipe ∷ _) _ = tt
notDot← (P.TDot ∷ _) n = ⊥-elim (n starts)
notDot← (P.TPlus ∷ _) _ = tt
notDot← (P.TMinus ∷ _) _ = tt
notDot← (P.TStar ∷ _) _ = tt
notDot← (P.TSlash ∷ _) _ = tt
notDot← (P.TPercent ∷ _) _ = tt
notDot← (P.TAmpersand ∷ _) _ = tt
notDot← (P.TLt ∷ _) _ = tt
notDot← (P.TLe ∷ _) _ = tt
notDot← (P.TGt ∷ _) _ = tt
notDot← (P.TGe ∷ _) _ = tt
notDot← (P.TEqEq ∷ _) _ = tt
notDot← (P.TNeq ∷ _) _ = tt
notDot← (P.TBang ∷ _) _ = tt
notDot← (P.TNewline ∷ _) _ = tt
notDot← (P.TEOF ∷ _) _ = tt

notCmp→ : ∀ toks → NotCmp toks → ∀ {t op} → Starts (F toks) t → ¬ CompareToken t op
notCmp→ [] _ ()
notCmp→ ((P.TWord _) ∷ _) _ starts ()
notCmp→ ((P.TInt _ _) ∷ _) _ starts ()
notCmp→ ((P.TFloat _ _ _ _) ∷ _) _ starts ()
notCmp→ ((P.TString _) ∷ _) _ starts ()
notCmp→ (P.TLParen ∷ _) _ starts ()
notCmp→ (P.TRParen ∷ _) _ starts ()
notCmp→ (P.TLBrace ∷ _) _ starts ()
notCmp→ (P.TRBrace ∷ _) _ starts ()
notCmp→ (P.TColon ∷ _) _ starts ()
notCmp→ (P.TEquals ∷ _) _ starts ()
notCmp→ (P.TArrow ∷ _) _ starts ()
notCmp→ (P.TCaret1 ∷ _) _ starts ()
notCmp→ (P.TCaret0 ∷ _) _ starts ()
notCmp→ (P.TCaretW ∷ _) _ starts ()
notCmp→ (P.TLambda ∷ _) _ starts ()
notCmp→ (P.TComma ∷ _) _ starts ()
notCmp→ (P.TSemicolon ∷ _) _ starts ()
notCmp→ (P.TAt ∷ _) _ starts ()
notCmp→ (P.TPipe ∷ _) _ starts ()
notCmp→ (P.TDot ∷ _) _ starts ()
notCmp→ (P.TPlus ∷ _) _ starts ()
notCmp→ (P.TMinus ∷ _) _ starts ()
notCmp→ (P.TStar ∷ _) _ starts ()
notCmp→ (P.TSlash ∷ _) _ starts ()
notCmp→ (P.TPercent ∷ _) _ starts ()
notCmp→ (P.TAmpersand ∷ _) _ starts ()
notCmp→ (P.TLt ∷ _) ()
notCmp→ (P.TLe ∷ _) ()
notCmp→ (P.TGt ∷ _) ()
notCmp→ (P.TGe ∷ _) ()
notCmp→ (P.TEqEq ∷ _) ()
notCmp→ (P.TNeq ∷ _) ()
notCmp→ (P.TBang ∷ _) _ starts ()
notCmp→ (P.TNewline ∷ _) _ starts ()
notCmp→ (P.TEOF ∷ _) _ starts ()

notCmp← : ∀ toks → (∀ {t op} → Starts (F toks) t → ¬ CompareToken t op) → NotCmp toks
notCmp← [] _ = tt
notCmp← ((P.TWord _) ∷ _) _ = tt
notCmp← ((P.TInt _ _) ∷ _) _ = tt
notCmp← ((P.TFloat _ _ _ _) ∷ _) _ = tt
notCmp← ((P.TString _) ∷ _) _ = tt
notCmp← (P.TLParen ∷ _) _ = tt
notCmp← (P.TRParen ∷ _) _ = tt
notCmp← (P.TLBrace ∷ _) _ = tt
notCmp← (P.TRBrace ∷ _) _ = tt
notCmp← (P.TColon ∷ _) _ = tt
notCmp← (P.TEquals ∷ _) _ = tt
notCmp← (P.TArrow ∷ _) _ = tt
notCmp← (P.TCaret1 ∷ _) _ = tt
notCmp← (P.TCaret0 ∷ _) _ = tt
notCmp← (P.TCaretW ∷ _) _ = tt
notCmp← (P.TLambda ∷ _) _ = tt
notCmp← (P.TComma ∷ _) _ = tt
notCmp← (P.TSemicolon ∷ _) _ = tt
notCmp← (P.TAt ∷ _) _ = tt
notCmp← (P.TPipe ∷ _) _ = tt
notCmp← (P.TDot ∷ _) _ = tt
notCmp← (P.TPlus ∷ _) _ = tt
notCmp← (P.TMinus ∷ _) _ = tt
notCmp← (P.TStar ∷ _) _ = tt
notCmp← (P.TSlash ∷ _) _ = tt
notCmp← (P.TPercent ∷ _) _ = tt
notCmp← (P.TAmpersand ∷ _) _ = tt
notCmp← (P.TLt ∷ _) n = n starts ct-lt
notCmp← (P.TLe ∷ _) n = n starts ct-le
notCmp← (P.TGt ∷ _) n = n starts ct-gt
notCmp← (P.TGe ∷ _) n = n starts ct-ge
notCmp← (P.TEqEq ∷ _) n = n starts ct-eq
notCmp← (P.TNeq ∷ _) n = n starts ct-ne
notCmp← (P.TBang ∷ _) _ = tt
notCmp← (P.TNewline ∷ _) _ = tt
notCmp← (P.TEOF ∷ _) _ = tt

notAdd→ : ∀ toks → NotAdd toks → ∀ {t op} → Starts (F toks) t → ¬ AddToken t op
notAdd→ [] _ ()
notAdd→ ((P.TWord _) ∷ _) _ starts ()
notAdd→ ((P.TInt _ _) ∷ _) _ starts ()
notAdd→ ((P.TFloat _ _ _ _) ∷ _) _ starts ()
notAdd→ ((P.TString _) ∷ _) _ starts ()
notAdd→ (P.TLParen ∷ _) _ starts ()
notAdd→ (P.TRParen ∷ _) _ starts ()
notAdd→ (P.TLBrace ∷ _) _ starts ()
notAdd→ (P.TRBrace ∷ _) _ starts ()
notAdd→ (P.TColon ∷ _) _ starts ()
notAdd→ (P.TEquals ∷ _) _ starts ()
notAdd→ (P.TArrow ∷ _) _ starts ()
notAdd→ (P.TCaret1 ∷ _) _ starts ()
notAdd→ (P.TCaret0 ∷ _) _ starts ()
notAdd→ (P.TCaretW ∷ _) _ starts ()
notAdd→ (P.TLambda ∷ _) _ starts ()
notAdd→ (P.TComma ∷ _) _ starts ()
notAdd→ (P.TSemicolon ∷ _) _ starts ()
notAdd→ (P.TAt ∷ _) _ starts ()
notAdd→ (P.TPipe ∷ _) _ starts ()
notAdd→ (P.TDot ∷ _) _ starts ()
notAdd→ (P.TPlus ∷ _) ()
notAdd→ (P.TMinus ∷ _) ()
notAdd→ (P.TStar ∷ _) _ starts ()
notAdd→ (P.TSlash ∷ _) _ starts ()
notAdd→ (P.TPercent ∷ _) _ starts ()
notAdd→ (P.TAmpersand ∷ _) _ starts ()
notAdd→ (P.TLt ∷ _) _ starts ()
notAdd→ (P.TLe ∷ _) _ starts ()
notAdd→ (P.TGt ∷ _) _ starts ()
notAdd→ (P.TGe ∷ _) _ starts ()
notAdd→ (P.TEqEq ∷ _) _ starts ()
notAdd→ (P.TNeq ∷ _) _ starts ()
notAdd→ (P.TBang ∷ _) _ starts ()
notAdd→ (P.TNewline ∷ _) _ starts ()
notAdd→ (P.TEOF ∷ _) _ starts ()

notAdd← : ∀ toks → (∀ {t op} → Starts (F toks) t → ¬ AddToken t op) → NotAdd toks
notAdd← [] _ = tt
notAdd← ((P.TWord _) ∷ _) _ = tt
notAdd← ((P.TInt _ _) ∷ _) _ = tt
notAdd← ((P.TFloat _ _ _ _) ∷ _) _ = tt
notAdd← ((P.TString _) ∷ _) _ = tt
notAdd← (P.TLParen ∷ _) _ = tt
notAdd← (P.TRParen ∷ _) _ = tt
notAdd← (P.TLBrace ∷ _) _ = tt
notAdd← (P.TRBrace ∷ _) _ = tt
notAdd← (P.TColon ∷ _) _ = tt
notAdd← (P.TEquals ∷ _) _ = tt
notAdd← (P.TArrow ∷ _) _ = tt
notAdd← (P.TCaret1 ∷ _) _ = tt
notAdd← (P.TCaret0 ∷ _) _ = tt
notAdd← (P.TCaretW ∷ _) _ = tt
notAdd← (P.TLambda ∷ _) _ = tt
notAdd← (P.TComma ∷ _) _ = tt
notAdd← (P.TSemicolon ∷ _) _ = tt
notAdd← (P.TAt ∷ _) _ = tt
notAdd← (P.TPipe ∷ _) _ = tt
notAdd← (P.TDot ∷ _) _ = tt
notAdd← (P.TPlus ∷ _) n = n starts at-plus
notAdd← (P.TMinus ∷ _) n = n starts at-minus
notAdd← (P.TStar ∷ _) _ = tt
notAdd← (P.TSlash ∷ _) _ = tt
notAdd← (P.TPercent ∷ _) _ = tt
notAdd← (P.TAmpersand ∷ _) _ = tt
notAdd← (P.TLt ∷ _) _ = tt
notAdd← (P.TLe ∷ _) _ = tt
notAdd← (P.TGt ∷ _) _ = tt
notAdd← (P.TGe ∷ _) _ = tt
notAdd← (P.TEqEq ∷ _) _ = tt
notAdd← (P.TNeq ∷ _) _ = tt
notAdd← (P.TBang ∷ _) _ = tt
notAdd← (P.TNewline ∷ _) _ = tt
notAdd← (P.TEOF ∷ _) _ = tt

notMul→ : ∀ toks → NotMul toks → ∀ {t op} → Starts (F toks) t → ¬ MulToken t op
notMul→ [] _ ()
notMul→ ((P.TWord _) ∷ _) _ starts ()
notMul→ ((P.TInt _ _) ∷ _) _ starts ()
notMul→ ((P.TFloat _ _ _ _) ∷ _) _ starts ()
notMul→ ((P.TString _) ∷ _) _ starts ()
notMul→ (P.TLParen ∷ _) _ starts ()
notMul→ (P.TRParen ∷ _) _ starts ()
notMul→ (P.TLBrace ∷ _) _ starts ()
notMul→ (P.TRBrace ∷ _) _ starts ()
notMul→ (P.TColon ∷ _) _ starts ()
notMul→ (P.TEquals ∷ _) _ starts ()
notMul→ (P.TArrow ∷ _) _ starts ()
notMul→ (P.TCaret1 ∷ _) _ starts ()
notMul→ (P.TCaret0 ∷ _) _ starts ()
notMul→ (P.TCaretW ∷ _) _ starts ()
notMul→ (P.TLambda ∷ _) _ starts ()
notMul→ (P.TComma ∷ _) _ starts ()
notMul→ (P.TSemicolon ∷ _) _ starts ()
notMul→ (P.TAt ∷ _) _ starts ()
notMul→ (P.TPipe ∷ _) _ starts ()
notMul→ (P.TDot ∷ _) _ starts ()
notMul→ (P.TPlus ∷ _) _ starts ()
notMul→ (P.TMinus ∷ _) _ starts ()
notMul→ (P.TStar ∷ _) ()
notMul→ (P.TSlash ∷ _) ()
notMul→ (P.TPercent ∷ _) ()
notMul→ (P.TAmpersand ∷ _) _ starts ()
notMul→ (P.TLt ∷ _) _ starts ()
notMul→ (P.TLe ∷ _) _ starts ()
notMul→ (P.TGt ∷ _) _ starts ()
notMul→ (P.TGe ∷ _) _ starts ()
notMul→ (P.TEqEq ∷ _) _ starts ()
notMul→ (P.TNeq ∷ _) _ starts ()
notMul→ (P.TBang ∷ _) _ starts ()
notMul→ (P.TNewline ∷ _) _ starts ()
notMul→ (P.TEOF ∷ _) _ starts ()

notMul← : ∀ toks → (∀ {t op} → Starts (F toks) t → ¬ MulToken t op) → NotMul toks
notMul← [] _ = tt
notMul← ((P.TWord _) ∷ _) _ = tt
notMul← ((P.TInt _ _) ∷ _) _ = tt
notMul← ((P.TFloat _ _ _ _) ∷ _) _ = tt
notMul← ((P.TString _) ∷ _) _ = tt
notMul← (P.TLParen ∷ _) _ = tt
notMul← (P.TRParen ∷ _) _ = tt
notMul← (P.TLBrace ∷ _) _ = tt
notMul← (P.TRBrace ∷ _) _ = tt
notMul← (P.TColon ∷ _) _ = tt
notMul← (P.TEquals ∷ _) _ = tt
notMul← (P.TArrow ∷ _) _ = tt
notMul← (P.TCaret1 ∷ _) _ = tt
notMul← (P.TCaret0 ∷ _) _ = tt
notMul← (P.TCaretW ∷ _) _ = tt
notMul← (P.TLambda ∷ _) _ = tt
notMul← (P.TComma ∷ _) _ = tt
notMul← (P.TSemicolon ∷ _) _ = tt
notMul← (P.TAt ∷ _) _ = tt
notMul← (P.TPipe ∷ _) _ = tt
notMul← (P.TDot ∷ _) _ = tt
notMul← (P.TPlus ∷ _) _ = tt
notMul← (P.TMinus ∷ _) _ = tt
notMul← (P.TStar ∷ _) n = n starts mt-star
notMul← (P.TSlash ∷ _) n = n starts mt-slash
notMul← (P.TPercent ∷ _) n = n starts mt-pct
notMul← (P.TAmpersand ∷ _) _ = tt
notMul← (P.TLt ∷ _) _ = tt
notMul← (P.TLe ∷ _) _ = tt
notMul← (P.TGt ∷ _) _ = tt
notMul← (P.TGe ∷ _) _ = tt
notMul← (P.TEqEq ∷ _) _ = tt
notMul← (P.TNeq ∷ _) _ = tt
notMul← (P.TBang ∷ _) _ = tt
notMul← (P.TNewline ∷ _) _ = tt
notMul← (P.TEOF ∷ _) _ = tt

notAtom→ : ∀ {toks} → NotAtomStart toks → ¬ ArgStart (F toks)
notAtom→ nas-[] ()
notAtom→ (nas-word-res e) (as-word nr) = nr (reserved-true e)
notAtom→ nas-TRParen ()
notAtom→ nas-TLBrace ()
notAtom→ nas-TRBrace ()
notAtom→ nas-TColon ()
notAtom→ nas-TEquals ()
notAtom→ nas-TArrow ()
notAtom→ nas-TCaret1 ()
notAtom→ nas-TCaret0 ()
notAtom→ nas-TCaretW ()
notAtom→ nas-TComma ()
notAtom→ nas-TSemicolon ()
notAtom→ nas-TAt ()
notAtom→ nas-TPipe ()
notAtom→ nas-TDot ()
notAtom→ nas-TPlus ()
notAtom→ nas-TMinus ()
notAtom→ nas-TStar ()
notAtom→ nas-TSlash ()
notAtom→ nas-TPercent ()
notAtom→ nas-TAmpersand ()
notAtom→ nas-TLt ()
notAtom→ nas-TLe ()
notAtom→ nas-TGt ()
notAtom→ nas-TGe ()
notAtom→ nas-TEqEq ()
notAtom→ nas-TNeq ()
notAtom→ nas-TBang ()
notAtom→ nas-TNewline ()
notAtom→ nas-TEOF ()

notAtom← : ∀ toks → ¬ ArgStart (F toks) → ¬ StrHead (F toks) → NotAtomStart toks
notAtom← [] _ _ = nas-[]
notAtom← (P.TWord w ∷ _) n _ = nas-word-res (reserved-is (λ nr → n (as-word nr)))
notAtom← (P.TInt _ _ ∷ _) n _ = ⊥-elim (n as-int)
notAtom← (P.TFloat _ _ _ _ ∷ _) n _ = ⊥-elim (n as-float)
notAtom← (P.TString _ ∷ _) _ s = ⊥-elim (s str-head)
notAtom← (P.TLParen ∷ _) n _ = ⊥-elim (n as-paren)
notAtom← (P.TRParen ∷ _) _ _ = nas-TRParen
notAtom← (P.TLBrace ∷ _) _ _ = nas-TLBrace
notAtom← (P.TRBrace ∷ _) _ _ = nas-TRBrace
notAtom← (P.TColon ∷ _) _ _ = nas-TColon
notAtom← (P.TEquals ∷ _) _ _ = nas-TEquals
notAtom← (P.TArrow ∷ _) _ _ = nas-TArrow
notAtom← (P.TCaret1 ∷ _) _ _ = nas-TCaret1
notAtom← (P.TCaret0 ∷ _) _ _ = nas-TCaret0
notAtom← (P.TCaretW ∷ _) _ _ = nas-TCaretW
notAtom← (P.TLambda ∷ _) n _ = ⊥-elim (n as-lambda)
notAtom← (P.TComma ∷ _) _ _ = nas-TComma
notAtom← (P.TSemicolon ∷ _) _ _ = nas-TSemicolon
notAtom← (P.TAt ∷ _) _ _ = nas-TAt
notAtom← (P.TPipe ∷ _) _ _ = nas-TPipe
notAtom← (P.TDot ∷ _) _ _ = nas-TDot
notAtom← (P.TPlus ∷ _) _ _ = nas-TPlus
notAtom← (P.TMinus ∷ _) _ _ = nas-TMinus
notAtom← (P.TStar ∷ _) _ _ = nas-TStar
notAtom← (P.TSlash ∷ _) _ _ = nas-TSlash
notAtom← (P.TPercent ∷ _) _ _ = nas-TPercent
notAtom← (P.TAmpersand ∷ _) _ _ = nas-TAmpersand
notAtom← (P.TLt ∷ _) _ _ = nas-TLt
notAtom← (P.TLe ∷ _) _ _ = nas-TLe
notAtom← (P.TGt ∷ _) _ _ = nas-TGt
notAtom← (P.TGe ∷ _) _ _ = nas-TGe
notAtom← (P.TEqEq ∷ _) _ _ = nas-TEqEq
notAtom← (P.TNeq ∷ _) _ _ = nas-TNeq
notAtom← (P.TBang ∷ _) _ _ = nas-TBang
notAtom← (P.TNewline ∷ _) _ _ = nas-TNewline
notAtom← (P.TEOF ∷ _) _ _ = nas-TEOF

argOk← : ∀ toks → ArgStart (F toks) → AppArgOk toks
argOk← [] ()
argOk← (P.TWord w ∷ _) (as-word nr) = aao-word (reserved-false nr)
argOk← (P.TInt _ _ ∷ _) as-int = aao-TInt
argOk← (P.TFloat _ _ _ _ ∷ _) as-float = aao-TFloat
argOk← ((P.TString _) ∷ _) ()
argOk← (P.TLParen ∷ _) as-paren = aao-TLParen
argOk← (P.TRParen ∷ _) ()
argOk← (P.TLBrace ∷ _) ()
argOk← (P.TRBrace ∷ _) ()
argOk← (P.TColon ∷ _) ()
argOk← (P.TEquals ∷ _) ()
argOk← (P.TArrow ∷ _) ()
argOk← (P.TCaret1 ∷ _) ()
argOk← (P.TCaret0 ∷ _) ()
argOk← (P.TCaretW ∷ _) ()
argOk← (P.TLambda ∷ _) as-lambda = aao-TLambda
argOk← (P.TComma ∷ _) ()
argOk← (P.TSemicolon ∷ _) ()
argOk← (P.TAt ∷ _) ()
argOk← (P.TPipe ∷ _) ()
argOk← (P.TDot ∷ _) ()
argOk← (P.TPlus ∷ _) ()
argOk← (P.TMinus ∷ _) ()
argOk← (P.TStar ∷ _) ()
argOk← (P.TSlash ∷ _) ()
argOk← (P.TPercent ∷ _) ()
argOk← (P.TAmpersand ∷ _) ()
argOk← (P.TLt ∷ _) ()
argOk← (P.TLe ∷ _) ()
argOk← (P.TGt ∷ _) ()
argOk← (P.TGe ∷ _) ()
argOk← (P.TEqEq ∷ _) ()
argOk← (P.TNeq ∷ _) ()
argOk← (P.TBang ∷ _) ()
argOk← (P.TNewline ∷ _) ()
argOk← (P.TEOF ∷ _) ()

notQual→ : ∀ {rest} → NotQualPrefix rest → ¬ QualSuffix (F rest)
notQual→ nqp-[] ()
notQual→ nqp-TWord ()
notQual→ nqp-TInt ()
notQual→ nqp-TFloat ()
notQual→ nqp-TString ()
notQual→ nqp-TLParen ()
notQual→ nqp-TRParen ()
notQual→ nqp-TLBrace ()
notQual→ nqp-TRBrace ()
notQual→ nqp-TColon ()
notQual→ nqp-TEquals ()
notQual→ nqp-TArrow ()
notQual→ nqp-TCaret1 ()
notQual→ nqp-TCaret0 ()
notQual→ nqp-TCaretW ()
notQual→ nqp-TLambda ()
notQual→ nqp-TComma ()
notQual→ nqp-TSemicolon ()
notQual→ nqp-TPipe ()
notQual→ nqp-TDot ()
notQual→ nqp-TPlus ()
notQual→ nqp-TMinus ()
notQual→ nqp-TStar ()
notQual→ nqp-TSlash ()
notQual→ nqp-TPercent ()
notQual→ nqp-TAmpersand ()
notQual→ nqp-TLt ()
notQual→ nqp-TLe ()
notQual→ nqp-TGt ()
notQual→ nqp-TGe ()
notQual→ nqp-TEqEq ()
notQual→ nqp-TNeq ()
notQual→ nqp-TBang ()
notQual→ nqp-TNewline ()
notQual→ nqp-TEOF ()
notQual→ nqp-TAt-[] ()
notQual→ (nqp-TAt-cons ntw-TInt) ()
notQual→ (nqp-TAt-cons ntw-TFloat) ()
notQual→ (nqp-TAt-cons ntw-TString) ()
notQual→ (nqp-TAt-cons ntw-TLParen) ()
notQual→ (nqp-TAt-cons ntw-TRParen) ()
notQual→ (nqp-TAt-cons ntw-TLBrace) ()
notQual→ (nqp-TAt-cons ntw-TRBrace) ()
notQual→ (nqp-TAt-cons ntw-TColon) ()
notQual→ (nqp-TAt-cons ntw-TEquals) ()
notQual→ (nqp-TAt-cons ntw-TArrow) ()
notQual→ (nqp-TAt-cons ntw-TCaret1) ()
notQual→ (nqp-TAt-cons ntw-TCaret0) ()
notQual→ (nqp-TAt-cons ntw-TCaretW) ()
notQual→ (nqp-TAt-cons ntw-TLambda) ()
notQual→ (nqp-TAt-cons ntw-TComma) ()
notQual→ (nqp-TAt-cons ntw-TSemicolon) ()
notQual→ (nqp-TAt-cons ntw-TAt) ()
notQual→ (nqp-TAt-cons ntw-TPipe) ()
notQual→ (nqp-TAt-cons ntw-TDot) ()
notQual→ (nqp-TAt-cons ntw-TPlus) ()
notQual→ (nqp-TAt-cons ntw-TMinus) ()
notQual→ (nqp-TAt-cons ntw-TStar) ()
notQual→ (nqp-TAt-cons ntw-TSlash) ()
notQual→ (nqp-TAt-cons ntw-TPercent) ()
notQual→ (nqp-TAt-cons ntw-TAmpersand) ()
notQual→ (nqp-TAt-cons ntw-TLt) ()
notQual→ (nqp-TAt-cons ntw-TLe) ()
notQual→ (nqp-TAt-cons ntw-TGt) ()
notQual→ (nqp-TAt-cons ntw-TGe) ()
notQual→ (nqp-TAt-cons ntw-TEqEq) ()
notQual→ (nqp-TAt-cons ntw-TNeq) ()
notQual→ (nqp-TAt-cons ntw-TBang) ()
notQual→ (nqp-TAt-cons ntw-TNewline) ()
notQual→ (nqp-TAt-cons ntw-TEOF) ()

notQual← : ∀ rest → ¬ QualSuffix (F rest) → NotQualPrefix rest
notQual← [] _ = nqp-[]
notQual← (P.TAt ∷ []) _ = nqp-TAt-[]
notQual← (P.TAt ∷ P.TWord _ ∷ _) n = ⊥-elim (n qual-suffix)
notQual← (P.TAt ∷ (P.TInt _ _) ∷ _) _ = nqp-TAt-cons ntw-TInt
notQual← (P.TAt ∷ (P.TFloat _ _ _ _) ∷ _) _ = nqp-TAt-cons ntw-TFloat
notQual← (P.TAt ∷ (P.TString _) ∷ _) _ = nqp-TAt-cons ntw-TString
notQual← (P.TAt ∷ P.TLParen ∷ _) _ = nqp-TAt-cons ntw-TLParen
notQual← (P.TAt ∷ P.TRParen ∷ _) _ = nqp-TAt-cons ntw-TRParen
notQual← (P.TAt ∷ P.TLBrace ∷ _) _ = nqp-TAt-cons ntw-TLBrace
notQual← (P.TAt ∷ P.TRBrace ∷ _) _ = nqp-TAt-cons ntw-TRBrace
notQual← (P.TAt ∷ P.TColon ∷ _) _ = nqp-TAt-cons ntw-TColon
notQual← (P.TAt ∷ P.TEquals ∷ _) _ = nqp-TAt-cons ntw-TEquals
notQual← (P.TAt ∷ P.TArrow ∷ _) _ = nqp-TAt-cons ntw-TArrow
notQual← (P.TAt ∷ P.TCaret1 ∷ _) _ = nqp-TAt-cons ntw-TCaret1
notQual← (P.TAt ∷ P.TCaret0 ∷ _) _ = nqp-TAt-cons ntw-TCaret0
notQual← (P.TAt ∷ P.TCaretW ∷ _) _ = nqp-TAt-cons ntw-TCaretW
notQual← (P.TAt ∷ P.TLambda ∷ _) _ = nqp-TAt-cons ntw-TLambda
notQual← (P.TAt ∷ P.TComma ∷ _) _ = nqp-TAt-cons ntw-TComma
notQual← (P.TAt ∷ P.TSemicolon ∷ _) _ = nqp-TAt-cons ntw-TSemicolon
notQual← (P.TAt ∷ P.TAt ∷ _) _ = nqp-TAt-cons ntw-TAt
notQual← (P.TAt ∷ P.TPipe ∷ _) _ = nqp-TAt-cons ntw-TPipe
notQual← (P.TAt ∷ P.TDot ∷ _) _ = nqp-TAt-cons ntw-TDot
notQual← (P.TAt ∷ P.TPlus ∷ _) _ = nqp-TAt-cons ntw-TPlus
notQual← (P.TAt ∷ P.TMinus ∷ _) _ = nqp-TAt-cons ntw-TMinus
notQual← (P.TAt ∷ P.TStar ∷ _) _ = nqp-TAt-cons ntw-TStar
notQual← (P.TAt ∷ P.TSlash ∷ _) _ = nqp-TAt-cons ntw-TSlash
notQual← (P.TAt ∷ P.TPercent ∷ _) _ = nqp-TAt-cons ntw-TPercent
notQual← (P.TAt ∷ P.TAmpersand ∷ _) _ = nqp-TAt-cons ntw-TAmpersand
notQual← (P.TAt ∷ P.TLt ∷ _) _ = nqp-TAt-cons ntw-TLt
notQual← (P.TAt ∷ P.TLe ∷ _) _ = nqp-TAt-cons ntw-TLe
notQual← (P.TAt ∷ P.TGt ∷ _) _ = nqp-TAt-cons ntw-TGt
notQual← (P.TAt ∷ P.TGe ∷ _) _ = nqp-TAt-cons ntw-TGe
notQual← (P.TAt ∷ P.TEqEq ∷ _) _ = nqp-TAt-cons ntw-TEqEq
notQual← (P.TAt ∷ P.TNeq ∷ _) _ = nqp-TAt-cons ntw-TNeq
notQual← (P.TAt ∷ P.TBang ∷ _) _ = nqp-TAt-cons ntw-TBang
notQual← (P.TAt ∷ P.TNewline ∷ _) _ = nqp-TAt-cons ntw-TNewline
notQual← (P.TAt ∷ P.TEOF ∷ _) _ = nqp-TAt-cons ntw-TEOF
notQual← ((P.TWord _) ∷ _) _ = nqp-TWord
notQual← ((P.TInt _ _) ∷ _) _ = nqp-TInt
notQual← ((P.TFloat _ _ _ _) ∷ _) _ = nqp-TFloat
notQual← ((P.TString _) ∷ _) _ = nqp-TString
notQual← (P.TLParen ∷ _) _ = nqp-TLParen
notQual← (P.TRParen ∷ _) _ = nqp-TRParen
notQual← (P.TLBrace ∷ _) _ = nqp-TLBrace
notQual← (P.TRBrace ∷ _) _ = nqp-TRBrace
notQual← (P.TColon ∷ _) _ = nqp-TColon
notQual← (P.TEquals ∷ _) _ = nqp-TEquals
notQual← (P.TArrow ∷ _) _ = nqp-TArrow
notQual← (P.TCaret1 ∷ _) _ = nqp-TCaret1
notQual← (P.TCaret0 ∷ _) _ = nqp-TCaret0
notQual← (P.TCaretW ∷ _) _ = nqp-TCaretW
notQual← (P.TLambda ∷ _) _ = nqp-TLambda
notQual← (P.TComma ∷ _) _ = nqp-TComma
notQual← (P.TSemicolon ∷ _) _ = nqp-TSemicolon
notQual← (P.TPipe ∷ _) _ = nqp-TPipe
notQual← (P.TDot ∷ _) _ = nqp-TDot
notQual← (P.TPlus ∷ _) _ = nqp-TPlus
notQual← (P.TMinus ∷ _) _ = nqp-TMinus
notQual← (P.TStar ∷ _) _ = nqp-TStar
notQual← (P.TSlash ∷ _) _ = nqp-TSlash
notQual← (P.TPercent ∷ _) _ = nqp-TPercent
notQual← (P.TAmpersand ∷ _) _ = nqp-TAmpersand
notQual← (P.TLt ∷ _) _ = nqp-TLt
notQual← (P.TLe ∷ _) _ = nqp-TLe
notQual← (P.TGt ∷ _) _ = nqp-TGt
notQual← (P.TGe ∷ _) _ = nqp-TGe
notQual← (P.TEqEq ∷ _) _ = nqp-TEqEq
notQual← (P.TNeq ∷ _) _ = nqp-TNeq
notQual← (P.TBang ∷ _) _ = nqp-TBang
notQual← (P.TNewline ∷ _) _ = nqp-TNewline
notQual← (P.TEOF ∷ _) _ = nqp-TEOF
