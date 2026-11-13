-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.NumTableAgree — the checker's operator table is the Spec's.
--
-- `NumTable.binSym` restates `Spec.Surface.Typing.binSym` outside that
-- module's parameters; here the two are the same, row by row.
------------------------------------------------------------------------

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Once.Spec.Name using (CanonicalName)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)

module Once.TypeCheck.NumTableAgree (Σ : Signature) {s : ℕ} (S : Defs s) (nm : Fin s → CanonicalName) where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym; trans)
open import Once.Spec.Type using (Float; _*_)
open import Relation.Nullary using (¬_)
open import Data.Bool using (true; false)
open import Once.Spec.Theory using (NumTy; float; ⌜_⌝ⁿ; Rounded; Sym; symDom)
open import Once.Spec.Surface.Operator using (BinOp; plain; dotted; ‹_›; o%; o+; o-; o*; o/; o<; o<=; o>; o>=; o==; o!=)
import Once.Spec.Surface.Typing Σ S nm as SU
import Once.TypeCheck.NumTable as NT

-- | The Spec's row, as the checker's.
toSpec : NT.BinSym → SU.BinSym
toSpec b = NT.theory b SU.∶ NT.shape b ∶ NT.symbol b

agree : ∀ op → SU.binSym op ≡ toSpec (NT.binSym op)
agree (plain ‹ o+ ›)  = refl
agree (plain ‹ o- ›)  = refl
agree (plain ‹ o* ›)  = refl
agree (plain ‹ o/ ›)  = refl
agree (plain o%)      = refl
agree (plain ‹ o< ›)  = refl
agree (plain ‹ o<= ›) = refl
agree (plain ‹ o> ›)  = refl
agree (plain ‹ o>= ›) = refl
agree (plain ‹ o== ›) = refl
agree (plain ‹ o!= ›) = refl
agree (dotted o+)     = refl
agree (dotted o-)     = refl
agree (dotted o*)     = refl
agree (dotted o/)     = refl
agree (dotted o<)     = refl
agree (dotted o<=)    = refl
agree (dotted o>)     = refl
agree (dotted o>=)    = refl
agree (dotted o==)    = refl
agree (dotted o!=)    = refl

-- | A binary operator's domain at `A`, by the Spec's table.
binDom : ∀ {m} op (A : NumTy) → symDom {m} A (SU.BinSym.shape (SU.binSym op)) ≡ ⌜ A ⌝ⁿ * ⌜ A ⌝ⁿ
binDom op A = subst (λ b → symDom A (SU.BinSym.shape b) ≡ ⌜ A ⌝ⁿ * ⌜ A ⌝ⁿ) (sym (agree op)) (NT.binDom op A)

-- | A dotted operator's domain, at `Float`.
mixedDom : ∀ {m op k} {o : Sym Rounded k} → SU.binSym op ≡ (Rounded SU.∶ k ∶ o) → symDom {m} float k ≡ Float * Float
mixedDom {op = op} eq = subst (λ k → symDom float k ≡ Float * Float) (cong SU.BinSym.shape eq) (binDom op float)

-- | The checker's negative-zero test is the Spec's.
negZero-sound : ∀ {sg i f} → SU.NegativeZero sg i f → NT.negZeroᵇ sg i f ≡ true
negZero-sound SU.neg-zero = refl

negZero-false : ∀ {sg i f} → NT.negZeroᵇ sg i f ≡ false → ¬ SU.NegativeZero sg i f
negZero-false eq nz with () ← trans (sym eq) (negZero-sound nz)
