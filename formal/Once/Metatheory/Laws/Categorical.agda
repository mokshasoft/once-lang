{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws.Categorical — the combinator laws
-- (`Spec.Metatheory.Categorical`): each side, read through what its
-- combinators mean (`Laws.Compose`, …), is the same computation; the closures
-- are the same functions (extensionally, by the monad laws up to
-- bisimilarity).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature; OneName)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Laws.Categorical (Σ : Signature) (u : OneName Σ) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

open import Data.Fin using (zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Once.Spec.Grade using (Quantity; Zero; One; Many; mk-kind; Purity; pure; 0≤q; 1≤ω)
open import Once.Spec.Type using (Ty; KCtx; TySub; _⟨_⟩; _⇒[_]_)
open import Once.Spec.Context using (Ctx; ∅; _▸_; _∷_; []; Usage; zeroUsage; _⊑ᵘ_; _⊑∷_)
open import Once.Spec.Core.Syntax
open import Once.Spec.Core.Derived using (idᶜ; composeᶜ)
open import Once.Spec.Core.Typing Σ S
open import Once.Spec.Core.Meaning Σ fmt S
open import Once.Spec.Effect Σ using (M; bind; sub; T∞; _>>=∞_; return∞; _≈_; toT∞)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ)
open import Once.Spec.Equivalence Σ using (Same)
open import Once.Spec.Metatheory using (_≅_)
open import Once.Metatheory.Erase Σ using (toT∞-bind; toT∞-sub)
open import Once.Metatheory.Bisim Σ using (≈-refl; ≈-sym; ≈-trans; ≈-bind; idˡ; idʳ)
open import Once.Metatheory.Coherence.Relation Σ using (Related; ≈-Relatedˡ; ≈-Relatedʳ; bindRel; returnRel; toObserved)
open import Once.Metatheory.Coherence.Layer Σ using (rel; runs; appMany)
open import Once.Metatheory.Laws.Tools Σ u fmt S
open import Once.Metatheory.Laws.Views Σ u fmt S
open import Once.Metatheory.Laws.Strengthen Σ S using (pure⊑)
open import Once.Metatheory.Laws.Compose Σ u fmt S using (compᵛ; module CompV)

-- Nothing is used below every usage.
zero⊑ : ∀ {n} (Ψ : Usage n) → zeroUsage ⊑ᵘ Ψ
zero⊑ []      = []
zero⊑ (q ∷ Ψ) = 0≤q ⊑∷ zero⊑ Ψ

module _ {m : ℕ} {Δ : KCtx m} where

  -- `idᶜ`, typed once and for all.
  idD : ∀ {n} {Γ : Ctx m n} (B : Ty m) (π : Purity) → Δ ⊩ Γ ⊢[ zeroUsage ] idᶜ B π ∷ B ⇒[ mk-kind Many π ] B ! pure
  idD B π = ⊢lam 1≤ω (⊢sub-eff (pure⊑ π) (⊢var zero))

  compose-idˡ : ∀ {n} {Γ : Ctx m n} {Ψ A B π π₀ f}
                (d : Δ ⊩ Γ ⊢[ Ψ ] composeᶜ A π (idᶜ B π) f ∷ A ⇒[ mk-kind Many π ] B ! π₀)
                (d′ : Δ ⊩ Γ ⊢[ Ψ ] f ∷ A ⇒[ mk-kind Many π ] B ! π₀) → _≅_ Σ fmt S d d′
  compose-idˡ {Γ = Γ} {Ψ} {A} {B} {π} {π₀} d d′ δ sd σ r γ sγ =
    sameM {T ⟨ σ ⟩} {π₀}
      (rel (~trans {T} (CompV.compSem δ sd σ r γ sγ d base (idD B π) r₀ d′ base)
             (≈-Relatedˡ (idˡ _ _)
               (≈-Relatedʳ (≈-sym (idʳ (⟪ d′ ⟫ γ)))
                 (bindRel (runs (fl d′ d′ base base)) (λ sg → returnRel (SAME sg)))))))
    where
      open Views δ sd σ r γ sγ
      T = A ⇒[ mk-kind Many π ] B
      r₀ = resR base (zero⊑ Ψ)
      idv = ⟦ idD {Γ = Γ} B π ⟧ δ σ r (restrict σ (zero⊑ Ψ) γ)
      SAME : ∀ {gv gv′} → Same (T ⟨ σ ⟩) gv gv′ → Same (T ⟨ σ ⟩) (compᵛ π idv gv) gv′
      SAME {gv} {gv′} sg a a′ sa = toObserved
        (≈-Relatedˡ (≈-trans (toT∞-bind π (gv a) idv) (≈-trans (≈-bind (≈-refl _) (λ b → toT∞-sub (pure⊑ π) b)) (idʳ _)))
          (runs (appMany {π} {A ⟨ σ ⟩} {B ⟨ σ ⟩} sg sa)))

  compose-idʳ : ∀ {n} {Γ : Ctx m n} {Ψ A B π π₀ f}
                (d : Δ ⊩ Γ ⊢[ Ψ ] composeᶜ A π f (idᶜ A π) ∷ A ⇒[ mk-kind Many π ] B ! π₀)
                (d′ : Δ ⊩ Γ ⊢[ Ψ ] f ∷ A ⇒[ mk-kind Many π ] B ! π₀) → _≅_ Σ fmt S d d′
  compose-idʳ {Γ = Γ} {Ψ} {A} {B} {π} {π₀} d d′ δ sd σ r γ sγ =
    sameM {T ⟨ σ ⟩} {π₀}
      (rel (~trans {T} (CompV.compSem δ sd σ r γ sγ d base d′ base (idD A π) r₀)
             (≈-Relatedʳ (≈-sym (idʳ (⟪ d′ ⟫ γ)))
               (bindRel (runs (fl d′ d′ base base))
                 (λ {fv} {fv′} sf → ≈-Relatedˡ (idˡ idv (λ gv → return∞ (compᵛ π fv gv))) (returnRel (SAME sf)))))))
    where
      open Views δ sd σ r γ sγ
      T = A ⇒[ mk-kind Many π ] B
      r₀ = resR base (zero⊑ Ψ)
      idv = ⟦ idD {Γ = Γ} A π ⟧ δ σ r (restrict σ (zero⊑ Ψ) γ)
      SAME : ∀ {fv fv′} → Same (T ⟨ σ ⟩) fv fv′ → Same (T ⟨ σ ⟩) (compᵛ π fv idv) fv′
      SAME {fv} {fv′} sf a a′ sa = toObserved
        (≈-Relatedˡ (≈-trans (toT∞-bind π (idv a) fv) (≈-trans (≈-bind (toT∞-sub (pure⊑ π) a) (λ _ → ≈-refl _)) (idˡ a _)))
          (runs (appMany {π} {A ⟨ σ ⟩} {B ⟨ σ ⟩} sf sa)))
