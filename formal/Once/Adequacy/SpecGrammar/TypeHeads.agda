-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecGrammar.TypeHeads — the compiler's type-grammar
-- lookaheads (`isStar`, `isPlus`, `arrowDir`, `NotStar`, …) against the
-- Spec's (`Starts` on the forgotten tokens). Generated case splits: a
-- catch-all classifier reduces only once the head token is a constructor.
------------------------------------------------------------------------

module Once.Adequacy.SpecGrammar.TypeHeads where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (Σ-syntax; _,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import Once.Spec.Surface.Lexing using (Token)
open Token
open import Once.Spec.Surface.Grammar using (Starts; starts)
import Once.Parser.Token as P
open import Once.Spec.Grade using (Zero; One; Many)
open import Once.Parser.Generic.Relation using (isStar; isPlus; arrowDir; adG; adA; adR; adD; ArrowDir)
open import Once.Parser.TypeRelation using (NotStar; NotStarPlus; NotArrowOrGrade)
open import Once.Adequacy.SpecLexing using (forget)

private
  F : List P.Token → List Token
  F = map forget

star-false→ : ∀ toks → isStar toks ≡ false → ¬ Starts (F toks) TStar
star-false→ [] _ ()
star-false→ ((P.TWord _) ∷ _) _ ()
star-false→ ((P.TInt _ _) ∷ _) _ ()
star-false→ ((P.TFloat _ _ _ _) ∷ _) _ ()
star-false→ ((P.TString _) ∷ _) _ ()
star-false→ (P.TLParen ∷ _) _ ()
star-false→ (P.TRParen ∷ _) _ ()
star-false→ (P.TLBrace ∷ _) _ ()
star-false→ (P.TRBrace ∷ _) _ ()
star-false→ (P.TColon ∷ _) _ ()
star-false→ (P.TEquals ∷ _) _ ()
star-false→ (P.TArrow ∷ _) _ ()
star-false→ (P.TCaret1 ∷ _) _ ()
star-false→ (P.TCaret0 ∷ _) _ ()
star-false→ (P.TCaretW ∷ _) _ ()
star-false→ (P.TLambda ∷ _) _ ()
star-false→ (P.TComma ∷ _) _ ()
star-false→ (P.TSemicolon ∷ _) _ ()
star-false→ (P.TAt ∷ _) _ ()
star-false→ (P.TPipe ∷ _) _ ()
star-false→ (P.TDot ∷ _) _ ()
star-false→ (P.TPlus ∷ _) _ ()
star-false→ (P.TMinus ∷ _) _ ()
star-false→ (P.TStar ∷ _) () _
star-false→ (P.TSlash ∷ _) _ ()
star-false→ (P.TPercent ∷ _) _ ()
star-false→ (P.TAmpersand ∷ _) _ ()
star-false→ (P.TLt ∷ _) _ ()
star-false→ (P.TLe ∷ _) _ ()
star-false→ (P.TGt ∷ _) _ ()
star-false→ (P.TGe ∷ _) _ ()
star-false→ (P.TEqEq ∷ _) _ ()
star-false→ (P.TNeq ∷ _) _ ()
star-false→ (P.TBang ∷ _) _ ()
star-false→ (P.TNewline ∷ _) _ ()
star-false→ (P.TEOF ∷ _) _ ()

star-false← : ∀ toks → ¬ Starts (F toks) TStar → isStar toks ≡ false
star-false← [] _ = refl
star-false← ((P.TWord _) ∷ _) _ = refl
star-false← ((P.TInt _ _) ∷ _) _ = refl
star-false← ((P.TFloat _ _ _ _) ∷ _) _ = refl
star-false← ((P.TString _) ∷ _) _ = refl
star-false← (P.TLParen ∷ _) _ = refl
star-false← (P.TRParen ∷ _) _ = refl
star-false← (P.TLBrace ∷ _) _ = refl
star-false← (P.TRBrace ∷ _) _ = refl
star-false← (P.TColon ∷ _) _ = refl
star-false← (P.TEquals ∷ _) _ = refl
star-false← (P.TArrow ∷ _) _ = refl
star-false← (P.TCaret1 ∷ _) _ = refl
star-false← (P.TCaret0 ∷ _) _ = refl
star-false← (P.TCaretW ∷ _) _ = refl
star-false← (P.TLambda ∷ _) _ = refl
star-false← (P.TComma ∷ _) _ = refl
star-false← (P.TSemicolon ∷ _) _ = refl
star-false← (P.TAt ∷ _) _ = refl
star-false← (P.TPipe ∷ _) _ = refl
star-false← (P.TDot ∷ _) _ = refl
star-false← (P.TPlus ∷ _) _ = refl
star-false← (P.TMinus ∷ _) _ = refl
star-false← (P.TStar ∷ _) n = ⊥-elim (n starts)
star-false← (P.TSlash ∷ _) _ = refl
star-false← (P.TPercent ∷ _) _ = refl
star-false← (P.TAmpersand ∷ _) _ = refl
star-false← (P.TLt ∷ _) _ = refl
star-false← (P.TLe ∷ _) _ = refl
star-false← (P.TGt ∷ _) _ = refl
star-false← (P.TGe ∷ _) _ = refl
star-false← (P.TEqEq ∷ _) _ = refl
star-false← (P.TNeq ∷ _) _ = refl
star-false← (P.TBang ∷ _) _ = refl
star-false← (P.TNewline ∷ _) _ = refl
star-false← (P.TEOF ∷ _) _ = refl

star-true : ∀ toks → isStar toks ≡ true → Σ[ t ∈ List P.Token ] toks ≡ P.TStar ∷ t
star-true [] ()
star-true ((P.TWord _) ∷ _) ()
star-true ((P.TInt _ _) ∷ _) ()
star-true ((P.TFloat _ _ _ _) ∷ _) ()
star-true ((P.TString _) ∷ _) ()
star-true (P.TLParen ∷ _) ()
star-true (P.TRParen ∷ _) ()
star-true (P.TLBrace ∷ _) ()
star-true (P.TRBrace ∷ _) ()
star-true (P.TColon ∷ _) ()
star-true (P.TEquals ∷ _) ()
star-true (P.TArrow ∷ _) ()
star-true (P.TCaret1 ∷ _) ()
star-true (P.TCaret0 ∷ _) ()
star-true (P.TCaretW ∷ _) ()
star-true (P.TLambda ∷ _) ()
star-true (P.TComma ∷ _) ()
star-true (P.TSemicolon ∷ _) ()
star-true (P.TAt ∷ _) ()
star-true (P.TPipe ∷ _) ()
star-true (P.TDot ∷ _) ()
star-true (P.TPlus ∷ _) ()
star-true (P.TMinus ∷ _) ()
star-true (P.TStar ∷ t) _ = t , refl
star-true (P.TSlash ∷ _) ()
star-true (P.TPercent ∷ _) ()
star-true (P.TAmpersand ∷ _) ()
star-true (P.TLt ∷ _) ()
star-true (P.TLe ∷ _) ()
star-true (P.TGt ∷ _) ()
star-true (P.TGe ∷ _) ()
star-true (P.TEqEq ∷ _) ()
star-true (P.TNeq ∷ _) ()
star-true (P.TBang ∷ _) ()
star-true (P.TNewline ∷ _) ()
star-true (P.TEOF ∷ _) ()

plus-false→ : ∀ toks → isPlus toks ≡ false → ¬ Starts (F toks) TPlus
plus-false→ [] _ ()
plus-false→ ((P.TWord _) ∷ _) _ ()
plus-false→ ((P.TInt _ _) ∷ _) _ ()
plus-false→ ((P.TFloat _ _ _ _) ∷ _) _ ()
plus-false→ ((P.TString _) ∷ _) _ ()
plus-false→ (P.TLParen ∷ _) _ ()
plus-false→ (P.TRParen ∷ _) _ ()
plus-false→ (P.TLBrace ∷ _) _ ()
plus-false→ (P.TRBrace ∷ _) _ ()
plus-false→ (P.TColon ∷ _) _ ()
plus-false→ (P.TEquals ∷ _) _ ()
plus-false→ (P.TArrow ∷ _) _ ()
plus-false→ (P.TCaret1 ∷ _) _ ()
plus-false→ (P.TCaret0 ∷ _) _ ()
plus-false→ (P.TCaretW ∷ _) _ ()
plus-false→ (P.TLambda ∷ _) _ ()
plus-false→ (P.TComma ∷ _) _ ()
plus-false→ (P.TSemicolon ∷ _) _ ()
plus-false→ (P.TAt ∷ _) _ ()
plus-false→ (P.TPipe ∷ _) _ ()
plus-false→ (P.TDot ∷ _) _ ()
plus-false→ (P.TPlus ∷ _) () _
plus-false→ (P.TMinus ∷ _) _ ()
plus-false→ (P.TStar ∷ _) _ ()
plus-false→ (P.TSlash ∷ _) _ ()
plus-false→ (P.TPercent ∷ _) _ ()
plus-false→ (P.TAmpersand ∷ _) _ ()
plus-false→ (P.TLt ∷ _) _ ()
plus-false→ (P.TLe ∷ _) _ ()
plus-false→ (P.TGt ∷ _) _ ()
plus-false→ (P.TGe ∷ _) _ ()
plus-false→ (P.TEqEq ∷ _) _ ()
plus-false→ (P.TNeq ∷ _) _ ()
plus-false→ (P.TBang ∷ _) _ ()
plus-false→ (P.TNewline ∷ _) _ ()
plus-false→ (P.TEOF ∷ _) _ ()

plus-false← : ∀ toks → ¬ Starts (F toks) TPlus → isPlus toks ≡ false
plus-false← [] _ = refl
plus-false← ((P.TWord _) ∷ _) _ = refl
plus-false← ((P.TInt _ _) ∷ _) _ = refl
plus-false← ((P.TFloat _ _ _ _) ∷ _) _ = refl
plus-false← ((P.TString _) ∷ _) _ = refl
plus-false← (P.TLParen ∷ _) _ = refl
plus-false← (P.TRParen ∷ _) _ = refl
plus-false← (P.TLBrace ∷ _) _ = refl
plus-false← (P.TRBrace ∷ _) _ = refl
plus-false← (P.TColon ∷ _) _ = refl
plus-false← (P.TEquals ∷ _) _ = refl
plus-false← (P.TArrow ∷ _) _ = refl
plus-false← (P.TCaret1 ∷ _) _ = refl
plus-false← (P.TCaret0 ∷ _) _ = refl
plus-false← (P.TCaretW ∷ _) _ = refl
plus-false← (P.TLambda ∷ _) _ = refl
plus-false← (P.TComma ∷ _) _ = refl
plus-false← (P.TSemicolon ∷ _) _ = refl
plus-false← (P.TAt ∷ _) _ = refl
plus-false← (P.TPipe ∷ _) _ = refl
plus-false← (P.TDot ∷ _) _ = refl
plus-false← (P.TPlus ∷ _) n = ⊥-elim (n starts)
plus-false← (P.TMinus ∷ _) _ = refl
plus-false← (P.TStar ∷ _) _ = refl
plus-false← (P.TSlash ∷ _) _ = refl
plus-false← (P.TPercent ∷ _) _ = refl
plus-false← (P.TAmpersand ∷ _) _ = refl
plus-false← (P.TLt ∷ _) _ = refl
plus-false← (P.TLe ∷ _) _ = refl
plus-false← (P.TGt ∷ _) _ = refl
plus-false← (P.TGe ∷ _) _ = refl
plus-false← (P.TEqEq ∷ _) _ = refl
plus-false← (P.TNeq ∷ _) _ = refl
plus-false← (P.TBang ∷ _) _ = refl
plus-false← (P.TNewline ∷ _) _ = refl
plus-false← (P.TEOF ∷ _) _ = refl

plus-true : ∀ toks → isPlus toks ≡ true → Σ[ t ∈ List P.Token ] toks ≡ P.TPlus ∷ t
plus-true [] ()
plus-true ((P.TWord _) ∷ _) ()
plus-true ((P.TInt _ _) ∷ _) ()
plus-true ((P.TFloat _ _ _ _) ∷ _) ()
plus-true ((P.TString _) ∷ _) ()
plus-true (P.TLParen ∷ _) ()
plus-true (P.TRParen ∷ _) ()
plus-true (P.TLBrace ∷ _) ()
plus-true (P.TRBrace ∷ _) ()
plus-true (P.TColon ∷ _) ()
plus-true (P.TEquals ∷ _) ()
plus-true (P.TArrow ∷ _) ()
plus-true (P.TCaret1 ∷ _) ()
plus-true (P.TCaret0 ∷ _) ()
plus-true (P.TCaretW ∷ _) ()
plus-true (P.TLambda ∷ _) ()
plus-true (P.TComma ∷ _) ()
plus-true (P.TSemicolon ∷ _) ()
plus-true (P.TAt ∷ _) ()
plus-true (P.TPipe ∷ _) ()
plus-true (P.TDot ∷ _) ()
plus-true (P.TPlus ∷ t) _ = t , refl
plus-true (P.TMinus ∷ _) ()
plus-true (P.TStar ∷ _) ()
plus-true (P.TSlash ∷ _) ()
plus-true (P.TPercent ∷ _) ()
plus-true (P.TAmpersand ∷ _) ()
plus-true (P.TLt ∷ _) ()
plus-true (P.TLe ∷ _) ()
plus-true (P.TGt ∷ _) ()
plus-true (P.TGe ∷ _) ()
plus-true (P.TEqEq ∷ _) ()
plus-true (P.TNeq ∷ _) ()
plus-true (P.TBang ∷ _) ()
plus-true (P.TNewline ∷ _) ()
plus-true (P.TEOF ∷ _) ()


notStar→TStar : ∀ toks → NotStar toks → ¬ Starts (F toks) TStar
notStar→TStar [] _ ()
notStar→TStar ((P.TWord _) ∷ _) _ ()
notStar→TStar ((P.TInt _ _) ∷ _) _ ()
notStar→TStar ((P.TFloat _ _ _ _) ∷ _) _ ()
notStar→TStar ((P.TString _) ∷ _) _ ()
notStar→TStar (P.TLParen ∷ _) _ ()
notStar→TStar (P.TRParen ∷ _) _ ()
notStar→TStar (P.TLBrace ∷ _) _ ()
notStar→TStar (P.TRBrace ∷ _) _ ()
notStar→TStar (P.TColon ∷ _) _ ()
notStar→TStar (P.TEquals ∷ _) _ ()
notStar→TStar (P.TArrow ∷ _) _ ()
notStar→TStar (P.TCaret1 ∷ _) _ ()
notStar→TStar (P.TCaret0 ∷ _) _ ()
notStar→TStar (P.TCaretW ∷ _) _ ()
notStar→TStar (P.TLambda ∷ _) _ ()
notStar→TStar (P.TComma ∷ _) _ ()
notStar→TStar (P.TSemicolon ∷ _) _ ()
notStar→TStar (P.TAt ∷ _) _ ()
notStar→TStar (P.TPipe ∷ _) _ ()
notStar→TStar (P.TDot ∷ _) _ ()
notStar→TStar (P.TPlus ∷ _) _ ()
notStar→TStar (P.TMinus ∷ _) _ ()
notStar→TStar (P.TStar ∷ _) ()
notStar→TStar (P.TSlash ∷ _) _ ()
notStar→TStar (P.TPercent ∷ _) _ ()
notStar→TStar (P.TAmpersand ∷ _) _ ()
notStar→TStar (P.TLt ∷ _) _ ()
notStar→TStar (P.TLe ∷ _) _ ()
notStar→TStar (P.TGt ∷ _) _ ()
notStar→TStar (P.TGe ∷ _) _ ()
notStar→TStar (P.TEqEq ∷ _) _ ()
notStar→TStar (P.TNeq ∷ _) _ ()
notStar→TStar (P.TBang ∷ _) _ ()
notStar→TStar (P.TNewline ∷ _) _ ()
notStar→TStar (P.TEOF ∷ _) _ ()

notStar← : ∀ toks → ¬ Starts (F toks) TStar → NotStar toks
notStar← [] _ = tt
notStar← ((P.TWord _) ∷ _) _ = tt
notStar← ((P.TInt _ _) ∷ _) _ = tt
notStar← ((P.TFloat _ _ _ _) ∷ _) _ = tt
notStar← ((P.TString _) ∷ _) _ = tt
notStar← (P.TLParen ∷ _) _ = tt
notStar← (P.TRParen ∷ _) _ = tt
notStar← (P.TLBrace ∷ _) _ = tt
notStar← (P.TRBrace ∷ _) _ = tt
notStar← (P.TColon ∷ _) _ = tt
notStar← (P.TEquals ∷ _) _ = tt
notStar← (P.TArrow ∷ _) _ = tt
notStar← (P.TCaret1 ∷ _) _ = tt
notStar← (P.TCaret0 ∷ _) _ = tt
notStar← (P.TCaretW ∷ _) _ = tt
notStar← (P.TLambda ∷ _) _ = tt
notStar← (P.TComma ∷ _) _ = tt
notStar← (P.TSemicolon ∷ _) _ = tt
notStar← (P.TAt ∷ _) _ = tt
notStar← (P.TPipe ∷ _) _ = tt
notStar← (P.TDot ∷ _) _ = tt
notStar← (P.TPlus ∷ _) _ = tt
notStar← (P.TMinus ∷ _) _ = tt
notStar← (P.TStar ∷ _) n = ⊥-elim (n starts)
notStar← (P.TSlash ∷ _) _ = tt
notStar← (P.TPercent ∷ _) _ = tt
notStar← (P.TAmpersand ∷ _) _ = tt
notStar← (P.TLt ∷ _) _ = tt
notStar← (P.TLe ∷ _) _ = tt
notStar← (P.TGt ∷ _) _ = tt
notStar← (P.TGe ∷ _) _ = tt
notStar← (P.TEqEq ∷ _) _ = tt
notStar← (P.TNeq ∷ _) _ = tt
notStar← (P.TBang ∷ _) _ = tt
notStar← (P.TNewline ∷ _) _ = tt
notStar← (P.TEOF ∷ _) _ = tt


notPlus→TPlus : ∀ toks → NotStarPlus toks → ¬ Starts (F toks) TPlus
notPlus→TPlus [] _ ()
notPlus→TPlus ((P.TWord _) ∷ _) _ ()
notPlus→TPlus ((P.TInt _ _) ∷ _) _ ()
notPlus→TPlus ((P.TFloat _ _ _ _) ∷ _) _ ()
notPlus→TPlus ((P.TString _) ∷ _) _ ()
notPlus→TPlus (P.TLParen ∷ _) _ ()
notPlus→TPlus (P.TRParen ∷ _) _ ()
notPlus→TPlus (P.TLBrace ∷ _) _ ()
notPlus→TPlus (P.TRBrace ∷ _) _ ()
notPlus→TPlus (P.TColon ∷ _) _ ()
notPlus→TPlus (P.TEquals ∷ _) _ ()
notPlus→TPlus (P.TArrow ∷ _) _ ()
notPlus→TPlus (P.TCaret1 ∷ _) _ ()
notPlus→TPlus (P.TCaret0 ∷ _) _ ()
notPlus→TPlus (P.TCaretW ∷ _) _ ()
notPlus→TPlus (P.TLambda ∷ _) _ ()
notPlus→TPlus (P.TComma ∷ _) _ ()
notPlus→TPlus (P.TSemicolon ∷ _) _ ()
notPlus→TPlus (P.TAt ∷ _) _ ()
notPlus→TPlus (P.TPipe ∷ _) _ ()
notPlus→TPlus (P.TDot ∷ _) _ ()
notPlus→TPlus (P.TPlus ∷ _) ()
notPlus→TPlus (P.TMinus ∷ _) _ ()
notPlus→TPlus (P.TStar ∷ _) _ ()
notPlus→TPlus (P.TSlash ∷ _) _ ()
notPlus→TPlus (P.TPercent ∷ _) _ ()
notPlus→TPlus (P.TAmpersand ∷ _) _ ()
notPlus→TPlus (P.TLt ∷ _) _ ()
notPlus→TPlus (P.TLe ∷ _) _ ()
notPlus→TPlus (P.TGt ∷ _) _ ()
notPlus→TPlus (P.TGe ∷ _) _ ()
notPlus→TPlus (P.TEqEq ∷ _) _ ()
notPlus→TPlus (P.TNeq ∷ _) _ ()
notPlus→TPlus (P.TBang ∷ _) _ ()
notPlus→TPlus (P.TNewline ∷ _) _ ()
notPlus→TPlus (P.TEOF ∷ _) _ ()

notPlus← : ∀ toks → ¬ Starts (F toks) TPlus → NotStarPlus toks
notPlus← [] _ = tt
notPlus← ((P.TWord _) ∷ _) _ = tt
notPlus← ((P.TInt _ _) ∷ _) _ = tt
notPlus← ((P.TFloat _ _ _ _) ∷ _) _ = tt
notPlus← ((P.TString _) ∷ _) _ = tt
notPlus← (P.TLParen ∷ _) _ = tt
notPlus← (P.TRParen ∷ _) _ = tt
notPlus← (P.TLBrace ∷ _) _ = tt
notPlus← (P.TRBrace ∷ _) _ = tt
notPlus← (P.TColon ∷ _) _ = tt
notPlus← (P.TEquals ∷ _) _ = tt
notPlus← (P.TArrow ∷ _) _ = tt
notPlus← (P.TCaret1 ∷ _) _ = tt
notPlus← (P.TCaret0 ∷ _) _ = tt
notPlus← (P.TCaretW ∷ _) _ = tt
notPlus← (P.TLambda ∷ _) _ = tt
notPlus← (P.TComma ∷ _) _ = tt
notPlus← (P.TSemicolon ∷ _) _ = tt
notPlus← (P.TAt ∷ _) _ = tt
notPlus← (P.TPipe ∷ _) _ = tt
notPlus← (P.TDot ∷ _) _ = tt
notPlus← (P.TPlus ∷ _) n = ⊥-elim (n starts)
notPlus← (P.TMinus ∷ _) _ = tt
notPlus← (P.TStar ∷ _) _ = tt
notPlus← (P.TSlash ∷ _) _ = tt
notPlus← (P.TPercent ∷ _) _ = tt
notPlus← (P.TAmpersand ∷ _) _ = tt
notPlus← (P.TLt ∷ _) _ = tt
notPlus← (P.TLe ∷ _) _ = tt
notPlus← (P.TGt ∷ _) _ = tt
notPlus← (P.TGe ∷ _) _ = tt
notPlus← (P.TEqEq ∷ _) _ = tt
notPlus← (P.TNeq ∷ _) _ = tt
notPlus← (P.TBang ∷ _) _ = tt
notPlus← (P.TNewline ∷ _) _ = tt
notPlus← (P.TEOF ∷ _) _ = tt


notArrow→TArrow : ∀ toks → NotArrowOrGrade toks → ¬ Starts (F toks) TArrow
notArrow→TArrow [] _ ()
notArrow→TArrow ((P.TWord _) ∷ _) _ ()
notArrow→TArrow ((P.TInt _ _) ∷ _) _ ()
notArrow→TArrow ((P.TFloat _ _ _ _) ∷ _) _ ()
notArrow→TArrow ((P.TString _) ∷ _) _ ()
notArrow→TArrow (P.TLParen ∷ _) _ ()
notArrow→TArrow (P.TRParen ∷ _) _ ()
notArrow→TArrow (P.TLBrace ∷ _) _ ()
notArrow→TArrow (P.TRBrace ∷ _) _ ()
notArrow→TArrow (P.TColon ∷ _) _ ()
notArrow→TArrow (P.TEquals ∷ _) _ ()
notArrow→TArrow (P.TArrow ∷ _) ()
notArrow→TArrow (P.TCaret1 ∷ _) ()
notArrow→TArrow (P.TCaret0 ∷ _) ()
notArrow→TArrow (P.TCaretW ∷ _) ()
notArrow→TArrow (P.TLambda ∷ _) _ ()
notArrow→TArrow (P.TComma ∷ _) _ ()
notArrow→TArrow (P.TSemicolon ∷ _) _ ()
notArrow→TArrow (P.TAt ∷ _) _ ()
notArrow→TArrow (P.TPipe ∷ _) _ ()
notArrow→TArrow (P.TDot ∷ _) _ ()
notArrow→TArrow (P.TPlus ∷ _) _ ()
notArrow→TArrow (P.TMinus ∷ _) _ ()
notArrow→TArrow (P.TStar ∷ _) _ ()
notArrow→TArrow (P.TSlash ∷ _) _ ()
notArrow→TArrow (P.TPercent ∷ _) _ ()
notArrow→TArrow (P.TAmpersand ∷ _) _ ()
notArrow→TArrow (P.TLt ∷ _) _ ()
notArrow→TArrow (P.TLe ∷ _) _ ()
notArrow→TArrow (P.TGt ∷ _) _ ()
notArrow→TArrow (P.TGe ∷ _) _ ()
notArrow→TArrow (P.TEqEq ∷ _) _ ()
notArrow→TArrow (P.TNeq ∷ _) _ ()
notArrow→TArrow (P.TBang ∷ _) _ ()
notArrow→TArrow (P.TNewline ∷ _) _ ()
notArrow→TArrow (P.TEOF ∷ _) _ ()

notArrow→TCaret0 : ∀ toks → NotArrowOrGrade toks → ¬ Starts (F toks) TCaret0
notArrow→TCaret0 [] _ ()
notArrow→TCaret0 ((P.TWord _) ∷ _) _ ()
notArrow→TCaret0 ((P.TInt _ _) ∷ _) _ ()
notArrow→TCaret0 ((P.TFloat _ _ _ _) ∷ _) _ ()
notArrow→TCaret0 ((P.TString _) ∷ _) _ ()
notArrow→TCaret0 (P.TLParen ∷ _) _ ()
notArrow→TCaret0 (P.TRParen ∷ _) _ ()
notArrow→TCaret0 (P.TLBrace ∷ _) _ ()
notArrow→TCaret0 (P.TRBrace ∷ _) _ ()
notArrow→TCaret0 (P.TColon ∷ _) _ ()
notArrow→TCaret0 (P.TEquals ∷ _) _ ()
notArrow→TCaret0 (P.TArrow ∷ _) ()
notArrow→TCaret0 (P.TCaret1 ∷ _) ()
notArrow→TCaret0 (P.TCaret0 ∷ _) ()
notArrow→TCaret0 (P.TCaretW ∷ _) ()
notArrow→TCaret0 (P.TLambda ∷ _) _ ()
notArrow→TCaret0 (P.TComma ∷ _) _ ()
notArrow→TCaret0 (P.TSemicolon ∷ _) _ ()
notArrow→TCaret0 (P.TAt ∷ _) _ ()
notArrow→TCaret0 (P.TPipe ∷ _) _ ()
notArrow→TCaret0 (P.TDot ∷ _) _ ()
notArrow→TCaret0 (P.TPlus ∷ _) _ ()
notArrow→TCaret0 (P.TMinus ∷ _) _ ()
notArrow→TCaret0 (P.TStar ∷ _) _ ()
notArrow→TCaret0 (P.TSlash ∷ _) _ ()
notArrow→TCaret0 (P.TPercent ∷ _) _ ()
notArrow→TCaret0 (P.TAmpersand ∷ _) _ ()
notArrow→TCaret0 (P.TLt ∷ _) _ ()
notArrow→TCaret0 (P.TLe ∷ _) _ ()
notArrow→TCaret0 (P.TGt ∷ _) _ ()
notArrow→TCaret0 (P.TGe ∷ _) _ ()
notArrow→TCaret0 (P.TEqEq ∷ _) _ ()
notArrow→TCaret0 (P.TNeq ∷ _) _ ()
notArrow→TCaret0 (P.TBang ∷ _) _ ()
notArrow→TCaret0 (P.TNewline ∷ _) _ ()
notArrow→TCaret0 (P.TEOF ∷ _) _ ()

notArrow→TCaret1 : ∀ toks → NotArrowOrGrade toks → ¬ Starts (F toks) TCaret1
notArrow→TCaret1 [] _ ()
notArrow→TCaret1 ((P.TWord _) ∷ _) _ ()
notArrow→TCaret1 ((P.TInt _ _) ∷ _) _ ()
notArrow→TCaret1 ((P.TFloat _ _ _ _) ∷ _) _ ()
notArrow→TCaret1 ((P.TString _) ∷ _) _ ()
notArrow→TCaret1 (P.TLParen ∷ _) _ ()
notArrow→TCaret1 (P.TRParen ∷ _) _ ()
notArrow→TCaret1 (P.TLBrace ∷ _) _ ()
notArrow→TCaret1 (P.TRBrace ∷ _) _ ()
notArrow→TCaret1 (P.TColon ∷ _) _ ()
notArrow→TCaret1 (P.TEquals ∷ _) _ ()
notArrow→TCaret1 (P.TArrow ∷ _) ()
notArrow→TCaret1 (P.TCaret1 ∷ _) ()
notArrow→TCaret1 (P.TCaret0 ∷ _) ()
notArrow→TCaret1 (P.TCaretW ∷ _) ()
notArrow→TCaret1 (P.TLambda ∷ _) _ ()
notArrow→TCaret1 (P.TComma ∷ _) _ ()
notArrow→TCaret1 (P.TSemicolon ∷ _) _ ()
notArrow→TCaret1 (P.TAt ∷ _) _ ()
notArrow→TCaret1 (P.TPipe ∷ _) _ ()
notArrow→TCaret1 (P.TDot ∷ _) _ ()
notArrow→TCaret1 (P.TPlus ∷ _) _ ()
notArrow→TCaret1 (P.TMinus ∷ _) _ ()
notArrow→TCaret1 (P.TStar ∷ _) _ ()
notArrow→TCaret1 (P.TSlash ∷ _) _ ()
notArrow→TCaret1 (P.TPercent ∷ _) _ ()
notArrow→TCaret1 (P.TAmpersand ∷ _) _ ()
notArrow→TCaret1 (P.TLt ∷ _) _ ()
notArrow→TCaret1 (P.TLe ∷ _) _ ()
notArrow→TCaret1 (P.TGt ∷ _) _ ()
notArrow→TCaret1 (P.TGe ∷ _) _ ()
notArrow→TCaret1 (P.TEqEq ∷ _) _ ()
notArrow→TCaret1 (P.TNeq ∷ _) _ ()
notArrow→TCaret1 (P.TBang ∷ _) _ ()
notArrow→TCaret1 (P.TNewline ∷ _) _ ()
notArrow→TCaret1 (P.TEOF ∷ _) _ ()

notArrow→TCaretW : ∀ toks → NotArrowOrGrade toks → ¬ Starts (F toks) TCaretW
notArrow→TCaretW [] _ ()
notArrow→TCaretW ((P.TWord _) ∷ _) _ ()
notArrow→TCaretW ((P.TInt _ _) ∷ _) _ ()
notArrow→TCaretW ((P.TFloat _ _ _ _) ∷ _) _ ()
notArrow→TCaretW ((P.TString _) ∷ _) _ ()
notArrow→TCaretW (P.TLParen ∷ _) _ ()
notArrow→TCaretW (P.TRParen ∷ _) _ ()
notArrow→TCaretW (P.TLBrace ∷ _) _ ()
notArrow→TCaretW (P.TRBrace ∷ _) _ ()
notArrow→TCaretW (P.TColon ∷ _) _ ()
notArrow→TCaretW (P.TEquals ∷ _) _ ()
notArrow→TCaretW (P.TArrow ∷ _) ()
notArrow→TCaretW (P.TCaret1 ∷ _) ()
notArrow→TCaretW (P.TCaret0 ∷ _) ()
notArrow→TCaretW (P.TCaretW ∷ _) ()
notArrow→TCaretW (P.TLambda ∷ _) _ ()
notArrow→TCaretW (P.TComma ∷ _) _ ()
notArrow→TCaretW (P.TSemicolon ∷ _) _ ()
notArrow→TCaretW (P.TAt ∷ _) _ ()
notArrow→TCaretW (P.TPipe ∷ _) _ ()
notArrow→TCaretW (P.TDot ∷ _) _ ()
notArrow→TCaretW (P.TPlus ∷ _) _ ()
notArrow→TCaretW (P.TMinus ∷ _) _ ()
notArrow→TCaretW (P.TStar ∷ _) _ ()
notArrow→TCaretW (P.TSlash ∷ _) _ ()
notArrow→TCaretW (P.TPercent ∷ _) _ ()
notArrow→TCaretW (P.TAmpersand ∷ _) _ ()
notArrow→TCaretW (P.TLt ∷ _) _ ()
notArrow→TCaretW (P.TLe ∷ _) _ ()
notArrow→TCaretW (P.TGt ∷ _) _ ()
notArrow→TCaretW (P.TGe ∷ _) _ ()
notArrow→TCaretW (P.TEqEq ∷ _) _ ()
notArrow→TCaretW (P.TNeq ∷ _) _ ()
notArrow→TCaretW (P.TBang ∷ _) _ ()
notArrow→TCaretW (P.TNewline ∷ _) _ ()
notArrow→TCaretW (P.TEOF ∷ _) _ ()

notArrow← : ∀ toks → ¬ Starts (F toks) TArrow → ¬ Starts (F toks) TCaret0 → ¬ Starts (F toks) TCaret1 → ¬ Starts (F toks) TCaretW → NotArrowOrGrade toks
notArrow← [] _ _ _ _ = tt
notArrow← ((P.TWord _) ∷ _) _ _ _ _ = tt
notArrow← ((P.TInt _ _) ∷ _) _ _ _ _ = tt
notArrow← ((P.TFloat _ _ _ _) ∷ _) _ _ _ _ = tt
notArrow← ((P.TString _) ∷ _) _ _ _ _ = tt
notArrow← (P.TLParen ∷ _) _ _ _ _ = tt
notArrow← (P.TRParen ∷ _) _ _ _ _ = tt
notArrow← (P.TLBrace ∷ _) _ _ _ _ = tt
notArrow← (P.TRBrace ∷ _) _ _ _ _ = tt
notArrow← (P.TColon ∷ _) _ _ _ _ = tt
notArrow← (P.TEquals ∷ _) _ _ _ _ = tt
notArrow← (P.TArrow ∷ _) n _ _ _ = ⊥-elim (n starts)
notArrow← (P.TCaret1 ∷ _) _ _ n _ = ⊥-elim (n starts)
notArrow← (P.TCaret0 ∷ _) _ n _ _ = ⊥-elim (n starts)
notArrow← (P.TCaretW ∷ _) _ _ _ n = ⊥-elim (n starts)
notArrow← (P.TLambda ∷ _) _ _ _ _ = tt
notArrow← (P.TComma ∷ _) _ _ _ _ = tt
notArrow← (P.TSemicolon ∷ _) _ _ _ _ = tt
notArrow← (P.TAt ∷ _) _ _ _ _ = tt
notArrow← (P.TPipe ∷ _) _ _ _ _ = tt
notArrow← (P.TDot ∷ _) _ _ _ _ = tt
notArrow← (P.TPlus ∷ _) _ _ _ _ = tt
notArrow← (P.TMinus ∷ _) _ _ _ _ = tt
notArrow← (P.TStar ∷ _) _ _ _ _ = tt
notArrow← (P.TSlash ∷ _) _ _ _ _ = tt
notArrow← (P.TPercent ∷ _) _ _ _ _ = tt
notArrow← (P.TAmpersand ∷ _) _ _ _ _ = tt
notArrow← (P.TLt ∷ _) _ _ _ _ = tt
notArrow← (P.TLe ∷ _) _ _ _ _ = tt
notArrow← (P.TGt ∷ _) _ _ _ _ = tt
notArrow← (P.TGe ∷ _) _ _ _ _ = tt
notArrow← (P.TEqEq ∷ _) _ _ _ _ = tt
notArrow← (P.TNeq ∷ _) _ _ _ _ = tt
notArrow← (P.TBang ∷ _) _ _ _ _ = tt
notArrow← (P.TNewline ∷ _) _ _ _ _ = tt
notArrow← (P.TEOF ∷ _) _ _ _ _ = tt

-- What `arrowDir` saw.
data IsCaret : P.Token → Set where
  ic0 : IsCaret P.TCaret0
  ic1 : IsCaret P.TCaret1
  icw : IsCaret P.TCaretW

data ArrowView : List P.Token → ArrowDir → Set where
  av-g1 : ∀ {t} → ArrowView (P.TCaret1 ∷ P.TArrow ∷ t) (adG One)
  av-g0 : ∀ {t} → ArrowView (P.TCaret0 ∷ P.TArrow ∷ t) (adG Zero)
  av-gw : ∀ {t} → ArrowView (P.TCaretW ∷ P.TArrow ∷ t) (adG Many)
  av-a  : ∀ {t} → ArrowView (P.TArrow ∷ t) adA
  av-r  : ∀ {g t} → IsCaret g → ArrowView (g ∷ t) adR
  av-d  : ∀ {toks} → ¬ Starts (F toks) TArrow → ¬ Starts (F toks) TCaret0 → ¬ Starts (F toks) TCaret1
        → ¬ Starts (F toks) TCaretW → ArrowView toks adD

arrow-view : ∀ toks → ArrowView toks (arrowDir toks)
arrow-view [] = av-d (λ ()) (λ ()) (λ ()) (λ ())
arrow-view ((P.TWord _) ∷ t) = av-d (λ ()) (λ ()) (λ ()) (λ ())
arrow-view ((P.TInt _ _) ∷ t) = av-d (λ ()) (λ ()) (λ ()) (λ ())
arrow-view ((P.TFloat _ _ _ _) ∷ t) = av-d (λ ()) (λ ()) (λ ()) (λ ())
arrow-view ((P.TString _) ∷ t) = av-d (λ ()) (λ ()) (λ ()) (λ ())
arrow-view (P.TLParen ∷ t) = av-d (λ ()) (λ ()) (λ ()) (λ ())
arrow-view (P.TRParen ∷ t) = av-d (λ ()) (λ ()) (λ ()) (λ ())
arrow-view (P.TLBrace ∷ t) = av-d (λ ()) (λ ()) (λ ()) (λ ())
arrow-view (P.TRBrace ∷ t) = av-d (λ ()) (λ ()) (λ ()) (λ ())
arrow-view (P.TColon ∷ t) = av-d (λ ()) (λ ()) (λ ()) (λ ())
arrow-view (P.TEquals ∷ t) = av-d (λ ()) (λ ()) (λ ()) (λ ())
arrow-view (P.TArrow ∷ t) = av-a
arrow-view (P.TCaret1 ∷ []) = av-r ic1
arrow-view (P.TCaret1 ∷ (P.TWord _) ∷ t) = av-r ic1
arrow-view (P.TCaret1 ∷ (P.TInt _ _) ∷ t) = av-r ic1
arrow-view (P.TCaret1 ∷ (P.TFloat _ _ _ _) ∷ t) = av-r ic1
arrow-view (P.TCaret1 ∷ (P.TString _) ∷ t) = av-r ic1
arrow-view (P.TCaret1 ∷ P.TLParen ∷ t) = av-r ic1
arrow-view (P.TCaret1 ∷ P.TRParen ∷ t) = av-r ic1
arrow-view (P.TCaret1 ∷ P.TLBrace ∷ t) = av-r ic1
arrow-view (P.TCaret1 ∷ P.TRBrace ∷ t) = av-r ic1
arrow-view (P.TCaret1 ∷ P.TColon ∷ t) = av-r ic1
arrow-view (P.TCaret1 ∷ P.TEquals ∷ t) = av-r ic1
arrow-view (P.TCaret1 ∷ P.TArrow ∷ t) = av-g1
arrow-view (P.TCaret1 ∷ P.TCaret1 ∷ t) = av-r ic1
arrow-view (P.TCaret1 ∷ P.TCaret0 ∷ t) = av-r ic1
arrow-view (P.TCaret1 ∷ P.TCaretW ∷ t) = av-r ic1
arrow-view (P.TCaret1 ∷ P.TLambda ∷ t) = av-r ic1
arrow-view (P.TCaret1 ∷ P.TComma ∷ t) = av-r ic1
arrow-view (P.TCaret1 ∷ P.TSemicolon ∷ t) = av-r ic1
arrow-view (P.TCaret1 ∷ P.TAt ∷ t) = av-r ic1
arrow-view (P.TCaret1 ∷ P.TPipe ∷ t) = av-r ic1
arrow-view (P.TCaret1 ∷ P.TDot ∷ t) = av-r ic1
arrow-view (P.TCaret1 ∷ P.TPlus ∷ t) = av-r ic1
arrow-view (P.TCaret1 ∷ P.TMinus ∷ t) = av-r ic1
arrow-view (P.TCaret1 ∷ P.TStar ∷ t) = av-r ic1
arrow-view (P.TCaret1 ∷ P.TSlash ∷ t) = av-r ic1
arrow-view (P.TCaret1 ∷ P.TPercent ∷ t) = av-r ic1
arrow-view (P.TCaret1 ∷ P.TAmpersand ∷ t) = av-r ic1
arrow-view (P.TCaret1 ∷ P.TLt ∷ t) = av-r ic1
arrow-view (P.TCaret1 ∷ P.TLe ∷ t) = av-r ic1
arrow-view (P.TCaret1 ∷ P.TGt ∷ t) = av-r ic1
arrow-view (P.TCaret1 ∷ P.TGe ∷ t) = av-r ic1
arrow-view (P.TCaret1 ∷ P.TEqEq ∷ t) = av-r ic1
arrow-view (P.TCaret1 ∷ P.TNeq ∷ t) = av-r ic1
arrow-view (P.TCaret1 ∷ P.TBang ∷ t) = av-r ic1
arrow-view (P.TCaret1 ∷ P.TNewline ∷ t) = av-r ic1
arrow-view (P.TCaret1 ∷ P.TEOF ∷ t) = av-r ic1
arrow-view (P.TCaret0 ∷ []) = av-r ic0
arrow-view (P.TCaret0 ∷ (P.TWord _) ∷ t) = av-r ic0
arrow-view (P.TCaret0 ∷ (P.TInt _ _) ∷ t) = av-r ic0
arrow-view (P.TCaret0 ∷ (P.TFloat _ _ _ _) ∷ t) = av-r ic0
arrow-view (P.TCaret0 ∷ (P.TString _) ∷ t) = av-r ic0
arrow-view (P.TCaret0 ∷ P.TLParen ∷ t) = av-r ic0
arrow-view (P.TCaret0 ∷ P.TRParen ∷ t) = av-r ic0
arrow-view (P.TCaret0 ∷ P.TLBrace ∷ t) = av-r ic0
arrow-view (P.TCaret0 ∷ P.TRBrace ∷ t) = av-r ic0
arrow-view (P.TCaret0 ∷ P.TColon ∷ t) = av-r ic0
arrow-view (P.TCaret0 ∷ P.TEquals ∷ t) = av-r ic0
arrow-view (P.TCaret0 ∷ P.TArrow ∷ t) = av-g0
arrow-view (P.TCaret0 ∷ P.TCaret1 ∷ t) = av-r ic0
arrow-view (P.TCaret0 ∷ P.TCaret0 ∷ t) = av-r ic0
arrow-view (P.TCaret0 ∷ P.TCaretW ∷ t) = av-r ic0
arrow-view (P.TCaret0 ∷ P.TLambda ∷ t) = av-r ic0
arrow-view (P.TCaret0 ∷ P.TComma ∷ t) = av-r ic0
arrow-view (P.TCaret0 ∷ P.TSemicolon ∷ t) = av-r ic0
arrow-view (P.TCaret0 ∷ P.TAt ∷ t) = av-r ic0
arrow-view (P.TCaret0 ∷ P.TPipe ∷ t) = av-r ic0
arrow-view (P.TCaret0 ∷ P.TDot ∷ t) = av-r ic0
arrow-view (P.TCaret0 ∷ P.TPlus ∷ t) = av-r ic0
arrow-view (P.TCaret0 ∷ P.TMinus ∷ t) = av-r ic0
arrow-view (P.TCaret0 ∷ P.TStar ∷ t) = av-r ic0
arrow-view (P.TCaret0 ∷ P.TSlash ∷ t) = av-r ic0
arrow-view (P.TCaret0 ∷ P.TPercent ∷ t) = av-r ic0
arrow-view (P.TCaret0 ∷ P.TAmpersand ∷ t) = av-r ic0
arrow-view (P.TCaret0 ∷ P.TLt ∷ t) = av-r ic0
arrow-view (P.TCaret0 ∷ P.TLe ∷ t) = av-r ic0
arrow-view (P.TCaret0 ∷ P.TGt ∷ t) = av-r ic0
arrow-view (P.TCaret0 ∷ P.TGe ∷ t) = av-r ic0
arrow-view (P.TCaret0 ∷ P.TEqEq ∷ t) = av-r ic0
arrow-view (P.TCaret0 ∷ P.TNeq ∷ t) = av-r ic0
arrow-view (P.TCaret0 ∷ P.TBang ∷ t) = av-r ic0
arrow-view (P.TCaret0 ∷ P.TNewline ∷ t) = av-r ic0
arrow-view (P.TCaret0 ∷ P.TEOF ∷ t) = av-r ic0
arrow-view (P.TCaretW ∷ []) = av-r icw
arrow-view (P.TCaretW ∷ (P.TWord _) ∷ t) = av-r icw
arrow-view (P.TCaretW ∷ (P.TInt _ _) ∷ t) = av-r icw
arrow-view (P.TCaretW ∷ (P.TFloat _ _ _ _) ∷ t) = av-r icw
arrow-view (P.TCaretW ∷ (P.TString _) ∷ t) = av-r icw
arrow-view (P.TCaretW ∷ P.TLParen ∷ t) = av-r icw
arrow-view (P.TCaretW ∷ P.TRParen ∷ t) = av-r icw
arrow-view (P.TCaretW ∷ P.TLBrace ∷ t) = av-r icw
arrow-view (P.TCaretW ∷ P.TRBrace ∷ t) = av-r icw
arrow-view (P.TCaretW ∷ P.TColon ∷ t) = av-r icw
arrow-view (P.TCaretW ∷ P.TEquals ∷ t) = av-r icw
arrow-view (P.TCaretW ∷ P.TArrow ∷ t) = av-gw
arrow-view (P.TCaretW ∷ P.TCaret1 ∷ t) = av-r icw
arrow-view (P.TCaretW ∷ P.TCaret0 ∷ t) = av-r icw
arrow-view (P.TCaretW ∷ P.TCaretW ∷ t) = av-r icw
arrow-view (P.TCaretW ∷ P.TLambda ∷ t) = av-r icw
arrow-view (P.TCaretW ∷ P.TComma ∷ t) = av-r icw
arrow-view (P.TCaretW ∷ P.TSemicolon ∷ t) = av-r icw
arrow-view (P.TCaretW ∷ P.TAt ∷ t) = av-r icw
arrow-view (P.TCaretW ∷ P.TPipe ∷ t) = av-r icw
arrow-view (P.TCaretW ∷ P.TDot ∷ t) = av-r icw
arrow-view (P.TCaretW ∷ P.TPlus ∷ t) = av-r icw
arrow-view (P.TCaretW ∷ P.TMinus ∷ t) = av-r icw
arrow-view (P.TCaretW ∷ P.TStar ∷ t) = av-r icw
arrow-view (P.TCaretW ∷ P.TSlash ∷ t) = av-r icw
arrow-view (P.TCaretW ∷ P.TPercent ∷ t) = av-r icw
arrow-view (P.TCaretW ∷ P.TAmpersand ∷ t) = av-r icw
arrow-view (P.TCaretW ∷ P.TLt ∷ t) = av-r icw
arrow-view (P.TCaretW ∷ P.TLe ∷ t) = av-r icw
arrow-view (P.TCaretW ∷ P.TGt ∷ t) = av-r icw
arrow-view (P.TCaretW ∷ P.TGe ∷ t) = av-r icw
arrow-view (P.TCaretW ∷ P.TEqEq ∷ t) = av-r icw
arrow-view (P.TCaretW ∷ P.TNeq ∷ t) = av-r icw
arrow-view (P.TCaretW ∷ P.TBang ∷ t) = av-r icw
arrow-view (P.TCaretW ∷ P.TNewline ∷ t) = av-r icw
arrow-view (P.TCaretW ∷ P.TEOF ∷ t) = av-r icw
arrow-view (P.TLambda ∷ t) = av-d (λ ()) (λ ()) (λ ()) (λ ())
arrow-view (P.TComma ∷ t) = av-d (λ ()) (λ ()) (λ ()) (λ ())
arrow-view (P.TSemicolon ∷ t) = av-d (λ ()) (λ ()) (λ ()) (λ ())
arrow-view (P.TAt ∷ t) = av-d (λ ()) (λ ()) (λ ()) (λ ())
arrow-view (P.TPipe ∷ t) = av-d (λ ()) (λ ()) (λ ()) (λ ())
arrow-view (P.TDot ∷ t) = av-d (λ ()) (λ ()) (λ ()) (λ ())
arrow-view (P.TPlus ∷ t) = av-d (λ ()) (λ ()) (λ ()) (λ ())
arrow-view (P.TMinus ∷ t) = av-d (λ ()) (λ ()) (λ ()) (λ ())
arrow-view (P.TStar ∷ t) = av-d (λ ()) (λ ()) (λ ()) (λ ())
arrow-view (P.TSlash ∷ t) = av-d (λ ()) (λ ()) (λ ()) (λ ())
arrow-view (P.TPercent ∷ t) = av-d (λ ()) (λ ()) (λ ()) (λ ())
arrow-view (P.TAmpersand ∷ t) = av-d (λ ()) (λ ()) (λ ()) (λ ())
arrow-view (P.TLt ∷ t) = av-d (λ ()) (λ ()) (λ ()) (λ ())
arrow-view (P.TLe ∷ t) = av-d (λ ()) (λ ()) (λ ()) (λ ())
arrow-view (P.TGt ∷ t) = av-d (λ ()) (λ ()) (λ ()) (λ ())
arrow-view (P.TGe ∷ t) = av-d (λ ()) (λ ()) (λ ()) (λ ())
arrow-view (P.TEqEq ∷ t) = av-d (λ ()) (λ ()) (λ ()) (λ ())
arrow-view (P.TNeq ∷ t) = av-d (λ ()) (λ ()) (λ ()) (λ ())
arrow-view (P.TBang ∷ t) = av-d (λ ()) (λ ()) (λ ()) (λ ())
arrow-view (P.TNewline ∷ t) = av-d (λ ()) (λ ()) (λ ()) (λ ())
arrow-view (P.TEOF ∷ t) = av-d (λ ()) (λ ()) (λ ()) (λ ())
