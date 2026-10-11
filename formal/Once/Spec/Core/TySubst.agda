-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Core.TySubst — plan 0.103 phase 5: type substitution over the
-- core's open types: ground types are fixed by it (`⌈⌉-⟨⟩`), and subtyping is
-- reflexive (`<:ₚ-refl`).
--
-- The TYPE-SUBSTITUTION LEMMA itself (`tsubst`: a typing at `Δ` gives one at
-- every kind-respecting instance) was proved here, postulate-free, but nothing
-- on the apex used it — `PolyTyping.instantiate` is the ground-target form the
-- proof needs — and the merge's island pass (2026-10-11) removed it with the
-- term/context substitutions it needed. It is in git at 320bb3eb9.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
import Once.Type
open import Once.Spec.Core.PolyTy using (Sig)

open import Once.Spec.Contract using (ISig)
module Once.Spec.Core.TySubst {Fs : ISig} {s : ℕ} (S : Sig Fs s) where

open import Data.Nat using (suc)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong; cong₂)

import Once.Type as T
open T using (Purity; pure; mk-kind; Many; One)
open import Once.Type.Sub using ()
open import Once.Type.SubLaws using (⊑π-refl)
open import Once.Surface.Context using (Usage; zeroUsage; singleUse)
open import Once.Spec.Core.PolyTy
open Schema using (type)
open import Once.Spec.Core.PolyTyping S
import Once.Spec.Core.Syntax S as G
open G using (primDom; primCod)

------------------------------------------------------------------------
-- Substitution respecting kinds
------------------------------------------------------------------------

-- Ground types are fixed by substitution.
mutual
  ⌈⌉-⟨⟩ : ∀ {m k} (A : T.Type) (σ : Sub m k) → ⌈ A ⌉ ⟨ σ ⟩ ≡ ⌈ A ⌉
  ⌈⌉-⟨⟩ T.Unit σ = refl
  ⌈⌉-⟨⟩ T.Void σ = refl
  ⌈⌉-⟨⟩ T.Int σ = refl
  ⌈⌉-⟨⟩ T.Float σ = refl
  ⌈⌉-⟨⟩ (T.rigid k i) σ = refl
  ⌈⌉-⟨⟩ (A T.* B) σ = cong₂ _*_ (⌈⌉-⟨⟩ A σ) (⌈⌉-⟨⟩ B σ)
  ⌈⌉-⟨⟩ (A T.+ B) σ = cong₂ _+_ (⌈⌉-⟨⟩ A σ) (⌈⌉-⟨⟩ B σ)
  ⌈⌉-⟨⟩ (A T.⇒[ k ] B) σ = cong₂ (λ a b → a ⇒[ k ] b) (⌈⌉-⟨⟩ A σ) (⌈⌉-⟨⟩ B σ)
  ⌈⌉-⟨⟩ (T.μ-type F) σ = cong μ-type (⌈⌉F-⟨⟩ F σ)
  ⌈⌉-⟨⟩ (T.ν-type F π) σ = cong (λ G → ν-type G π) (⌈⌉F-⟨⟩ F σ)

  ⌈⌉F-⟨⟩ : ∀ {m k} (F : T.Functor) (σ : Sub m k) → ⌈ F ⌉F ⟨ σ ⟩F ≡ ⌈ F ⌉F
  ⌈⌉F-⟨⟩ (T.K A) σ = cong K (⌈⌉-⟨⟩ A σ)
  ⌈⌉F-⟨⟩ T.Id σ = refl
  ⌈⌉F-⟨⟩ (F T.⊕ G) σ = cong₂ _⊕_ (⌈⌉F-⟨⟩ F σ) (⌈⌉F-⟨⟩ G σ)
  ⌈⌉F-⟨⟩ (F T.⊗ G) σ = cong₂ _⊗_ (⌈⌉F-⟨⟩ F σ) (⌈⌉F-⟨⟩ G σ)

-- Subtyping over open types is reflexive, hence stable under substitution.
<:ₚ-refl : ∀ {m} (A : Ty m) → A <:ₚ A
<:ₚ-refl (var i) = sub-var
<:ₚ-refl Unit = sub-unit
<:ₚ-refl Void = sub-void
<:ₚ-refl Int = sub-int
<:ₚ-refl Float = sub-float
<:ₚ-refl (rigid k i) = sub-rigid
<:ₚ-refl (A * B) = sub-prod (<:ₚ-refl A) (<:ₚ-refl B)
<:ₚ-refl (A + B) = sub-sum (<:ₚ-refl A) (<:ₚ-refl B)
<:ₚ-refl (A ⇒[ mk-kind q π ] B) = sub-arr (<:ₚ-refl A) (<:ₚ-refl B) (⊑π-refl π)
<:ₚ-refl (μ-type F) = sub-μ
<:ₚ-refl (ν-type F π) = sub-ν (⊑π-refl π)
