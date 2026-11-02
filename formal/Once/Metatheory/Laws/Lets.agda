{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws.Lets — `let` is the effect structure's bind
-- (`Spec.Metatheory.Equations`): its right unit.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature; OneName)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Laws.Lets (Σ : Signature) (u : OneName Σ) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

import Data.Empty
open import Data.Empty using (⊥-elim)
open import Data.Fin using (zero; suc)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Spec.Grade using (Quantity; Zero; One; Many; 1≤1; 1≤ω; positionGrade)
open import Once.Spec.Type using (Ty; KCtx; _⟨_⟩; Void)
open import Once.Spec.Context using (Ctx; _▸_; _∷_; _⊑∷_)
open import Once.Spec.Core.Syntax
open import Once.Spec.Core.Typing Σ S
open import Once.Spec.Core.Meaning Σ fmt S
open import Once.Spec.Effect Σ using (T∞; _>>=∞_; return∞; _≈_)
open import Once.Spec.Equivalence Σ using (Same)
open import Once.Spec.Metatheory using (_≅_)
open import Once.Metatheory.Bisim Σ using (≈-refl; ≈-sym; ≈-trans; ≈-bind; idˡ; idʳ; assoc)
open import Once.Metatheory.Coherence.Relation Σ using (Related; ≈-Relatedˡ; ≈-Relatedʳ; bindRel; returnRel)
open import Once.Metatheory.Coherence.Layer Σ using (rel; runs)
open import Once.Metatheory.Coherence.Uniqueness Σ S using (ty-unique)
open import Once.Metatheory.Laws.Tools Σ u fmt S
open import Once.Metatheory.Laws.Views Σ u fmt S
open import Once.Metatheory.Coherence.Env Σ fmt S using (SlotAgree)

module _ {m : ℕ} {Δ : KCtx m} where

  let-unit : ∀ {n} {Γ : Ctx m n} {Ψ A q π t}
             (d : Δ ⊩ Γ ⊢[ Ψ ] let′ q t (var zero) ∷ A ! π)
             (d′ : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π) → _≅_ Σ fmt S d d′
  let-unit {Γ = Γ} {A = A} {q} {π} d d′ δ sd σ r γ sγ = sameM {A ⟨ σ ⟩} {π} (rel (go (viewLet d base)))
    where
      open Views δ sd σ r γ sγ

      -- the body returns the bound value
      body : ∀ {Ψ₂ q′ π₂ eb} (db : Δ ⊩ (Γ ▸ A) ⊢[ q′ ∷ Ψ₂ ] var zero ∷ A ! π₂) → Res eb → ∀ {v v′}
           → Same (A ⟨ σ ⟩) v v′ → SlotAgree σ A q′ q′ (slot q′ v) (slot q′ v)
           → _~_ {A} (⟪ db ⟫▸ eb (slot q′ v)) (return∞ v′)
      body {q′ = q′} db rb sv sl = ~trans {A} (readVar0 δ sd σ r (sameEnv▸ σ q′ (sameEnvOf rb) sl) db) (returnRel sv)

      fin : ∀ q′ {Ψ₁ Ψ₂ π₁ π₂ eb} (de : Δ ⊩ Γ ⊢[ Ψ₁ ] _ ∷ A ! positionGrade q′ π₁)
              (db : Δ ⊩ (Γ ▸ A) ⊢[ q′ ∷ Ψ₂ ] var zero ∷ A ! π₂) → Res eb
          → LetSem q′ (⟪ d ⟫ γ) de db eb → _~_ {A} (⟪ d ⟫ γ) (⟪ d′ ⟫ γ)
      fin Zero de db rb sem with varUse db
      ... | () ⊑∷ _
      fin One  de db rb (ee , re , eqR) =
        ~trans {A} eqR (≈-Relatedʳ (≈-sym (idʳ (⟪ d′ ⟫ γ)))
          (bindRel (runs (fl de d′ re base)) (λ {x} {y} sv → body db rb {x} {y} sv (sameRefl (A ⟨ σ ⟩) sv))))
      fin Many de db rb (ee , re , eqR) =
        ~trans {A} eqR (≈-Relatedʳ (≈-sym (idʳ (⟪ d′ ⟫ γ)))
          (bindRel (runs (fl de d′ re base)) (λ {x} {y} sv → body db rb {x} {y} sv (sameRefl (A ⟨ σ ⟩) sv))))

      go : LetView d γ → _~_ {A} (⟪ d ⟫ γ) (⟪ d′ ⟫ γ)
      go (letView de db rb sem) with ty-unique de d′
      ... | refl = fin q de db rb sem

  absurd-η : ∀ {n} {Γ : Ctx m n} {Ψ A q π e t}
             (d : Δ ⊩ Γ ⊢[ Ψ ] let′ q e t ∷ A ! π)
             (d′ : Δ ⊩ Γ ⊢[ Ψ ] absurd A e ∷ A ! π) → _≅_ Σ fmt S d d′
  absurd-η {Γ = Γ} {A = A} {q} {π} d d′ δ sd σ r γ sγ =
    sameM {A ⟨ σ ⟩} {π} (rel (go (viewLet d base) (AbsurdV.viewAbsurd δ sd σ r γ sγ d′ base)))
    where
      open Views δ sd σ r γ sγ
      open AbsurdV δ sd σ r γ sγ using (AbsurdView; absurdView)

      fin : ∀ q′ {Ψ₁ Ψ₂ Ψ₀ π₁ π₂ π₀ eb γ₀} (de : Δ ⊩ Γ ⊢[ Ψ₁ ] _ ∷ Void ! positionGrade q′ π₁)
              (db : Δ ⊩ (Γ ▸ Void) ⊢[ q′ ∷ Ψ₂ ] _ ∷ A ! π₂) → Res eb
          → (de′ : Δ ⊩ Γ ⊢[ Ψ₀ ] _ ∷ Void ! π₀) → Res γ₀
          → LetSem q′ (⟪ d ⟫ γ) de db eb → _~_ {A} (⟪ d ⟫ γ) (⟪ de′ ⟫ γ₀ >>=∞ λ ())
      fin Zero {γ₀ = γ₀} de db rb de′ r₀ sem = ⊥-elim (⟦ transfer de de′ ⟧ δ σ r γ₀)
      fin One  de db rb de′ r₀ (ee , re , eqR) =
        ~trans {A} eqR (bindRel (runs (fl de de′ re r₀)) (λ {x} → ⊥-elim x))
      fin Many de db rb de′ r₀ (ee , re , eqR) =
        ~trans {A} eqR (bindRel (runs (fl de de′ re r₀)) (λ {x} → ⊥-elim x))

      go : LetView d γ → AbsurdView d′ γ → _~_ {A} (⟪ d ⟫ γ) (⟪ d′ ⟫ γ)
      go (letView de db rb sem) (absurdView de′ r₀ eqA) with ty-unique de de′
      ... | refl = ~trans {A} (fin q de db rb de′ r₀ sem) (~sym {A} eqA)
