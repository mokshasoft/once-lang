-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.EnvAlgebraV — `EnvAlgebra`'s environment laws over the
-- GRADED domain `⟦_⟧ᵛ` (D250, plan 0.104), clause for clause: an environment is
-- a nested product, so the laws do not depend on the grade.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)
open import Once.Spec.Type using (TySub)

-- Plan 0.122 §5.5 M4: over the Spec's domain, at an instance `σ`.
module Once.Denotation.EnvAlgebraV (Σ : Signature) (σ : TySub 0 0) where

open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans)

open import Once.Spec.Grade using (Quantity; Zero; One; Many)
open import Once.Spec.Type using (Type)
open import Once.Internal.Context using (Ctx; ∅; Usage; _↾_; _⊑ᵘ_; ⊑[]; _≤q'_; z≤z; z≤o; z≤m; o≤o; o≤m; m≤m; ⊑ᵘ-trans; ⊑ᵘ-unique) renaming (⟦_⟧ᶜ to ⟦_⟧ᶜᵗ)
open import Once.Spec.Context using (_∷_; _⊑∷_; _▸_)
open import Once.Denotation.SpecDomain Σ σ using (⟦_⟧ᵛ; restrictᵛ; bindᵛ)

Env : ∀ {n} → Ctx 0 n → Usage n → Set
Env Γ Ψ = ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᵛ

------------------------------------------------------------------------
-- Proof irrelevance
------------------------------------------------------------------------

restrict-irr : ∀ {n} {Γ : Ctx 0 n} {Ψ Ψ' : Usage n} (u v : Ψ' ⊑ᵘ Ψ) (x : Env Γ Ψ)
             → restrictᵛ {Γ = Γ} u x ≡ restrictᵛ {Γ = Γ} v x
restrict-irr {Γ = Γ} u v x = cong (λ w → restrictᵛ {Γ = Γ} w x) (⊑ᵘ-unique u v)

------------------------------------------------------------------------
-- Identity and composition
------------------------------------------------------------------------

restrict-refl : ∀ {n} {Γ : Ctx 0 n} {Ψ : Usage n} (u : Ψ ⊑ᵘ Ψ) (x : Env Γ Ψ) → restrictᵛ {Γ = Γ} u x ≡ x
restrict-refl {Γ = ∅}         ⊑[]        x = refl
restrict-refl {Γ = Γ ▸ A} (z≤z ⊑∷ u) x = restrict-refl {Γ = Γ} u x
restrict-refl {Γ = Γ ▸ A} (o≤o ⊑∷ u) x = cong (_, proj₂ x) (restrict-refl {Γ = Γ} u (proj₁ x))
restrict-refl {Γ = Γ ▸ A} (m≤m ⊑∷ u) x = cong (_, proj₂ x) (restrict-refl {Γ = Γ} u (proj₁ x))

restrict-∘ : ∀ {n} {Γ : Ctx 0 n} {Ψ₁ Ψ₂ Ψ₃ : Usage n} (u : Ψ₁ ⊑ᵘ Ψ₂) (v : Ψ₂ ⊑ᵘ Ψ₃) (x : Env Γ Ψ₃)
           → restrictᵛ {Γ = Γ} u (restrictᵛ {Γ = Γ} v x) ≡ restrictᵛ {Γ = Γ} (⊑ᵘ-trans u v) x
restrict-∘ {Γ = ∅}         ⊑[]        ⊑[]        x = refl
restrict-∘ {Γ = Γ ▸ A} (z≤z ⊑∷ u) (z≤z ⊑∷ v) x = restrict-∘ {Γ = Γ} u v x
restrict-∘ {Γ = Γ ▸ A} (z≤z ⊑∷ u) (z≤o ⊑∷ v) x = restrict-∘ {Γ = Γ} u v (proj₁ x)
restrict-∘ {Γ = Γ ▸ A} (z≤z ⊑∷ u) (z≤m ⊑∷ v) x = restrict-∘ {Γ = Γ} u v (proj₁ x)
restrict-∘ {Γ = Γ ▸ A} (z≤o ⊑∷ u) (o≤o ⊑∷ v) x = restrict-∘ {Γ = Γ} u v (proj₁ x)
restrict-∘ {Γ = Γ ▸ A} (z≤o ⊑∷ u) (o≤m ⊑∷ v) x = restrict-∘ {Γ = Γ} u v (proj₁ x)
restrict-∘ {Γ = Γ ▸ A} (z≤m ⊑∷ u) (m≤m ⊑∷ v) x = restrict-∘ {Γ = Γ} u v (proj₁ x)
restrict-∘ {Γ = Γ ▸ A} (o≤o ⊑∷ u) (o≤o ⊑∷ v) x = cong (_, proj₂ x) (restrict-∘ {Γ = Γ} u v (proj₁ x))
restrict-∘ {Γ = Γ ▸ A} (o≤o ⊑∷ u) (o≤m ⊑∷ v) x = cong (_, proj₂ x) (restrict-∘ {Γ = Γ} u v (proj₁ x))
restrict-∘ {Γ = Γ ▸ A} (o≤m ⊑∷ u) (m≤m ⊑∷ v) x = cong (_, proj₂ x) (restrict-∘ {Γ = Γ} u v (proj₁ x))
restrict-∘ {Γ = Γ ▸ A} (m≤m ⊑∷ u) (m≤m ⊑∷ v) x = cong (_, proj₂ x) (restrict-∘ {Γ = Γ} u v (proj₁ x))

-- Any two restrictions of one environment to one usage agree.
restrict-≡ : ∀ {n} {Γ : Ctx 0 n} {Ψ₁ Ψ₂ Ψ₃ : Usage n} (u : Ψ₁ ⊑ᵘ Ψ₂) (v : Ψ₂ ⊑ᵘ Ψ₃) (w : Ψ₁ ⊑ᵘ Ψ₃) (x : Env Γ Ψ₃)
           → restrictᵛ {Γ = Γ} u (restrictᵛ {Γ = Γ} v x) ≡ restrictᵛ {Γ = Γ} w x
restrict-≡ {Γ = Γ} u v w x = trans (restrict-∘ {Γ = Γ} u v x) (restrict-irr {Γ = Γ} (⊑ᵘ-trans u v) w x)

------------------------------------------------------------------------
-- Binders
------------------------------------------------------------------------

-- Restricting an extended environment: the bound variable is dropped when the
-- restricted usage does not use it, and kept when it does.
restrict-bind : ∀ {n} {Γ : Ctx 0 n} {A : Type} {Ψ' Ψ : Usage n} (q' q : Quantity)
                  (w : (q' ∷ Ψ') ⊑ᵘ (q ∷ Ψ)) (u : Ψ' ⊑ᵘ Ψ) (x : Env Γ Ψ) (a : ⟦ A ⟧ᵛ)
              → restrictᵛ {Γ = Γ ▸ A} w (bindᵛ {Γ = Γ} {A = A} q x a)
                ≡ bindᵛ {Γ = Γ} {A = A} q' (restrictᵛ {Γ = Γ} u x) a
restrict-bind {Γ = Γ} Zero Zero (z≤z ⊑∷ w) u x a = restrict-irr {Γ = Γ} w u x
restrict-bind {Γ = Γ} Zero One  (z≤o ⊑∷ w) u x a = restrict-irr {Γ = Γ} w u x
restrict-bind {Γ = Γ} Zero Many (z≤m ⊑∷ w) u x a = restrict-irr {Γ = Γ} w u x
restrict-bind {Γ = Γ} One  One  (o≤o ⊑∷ w) u x a = cong (_, a) (restrict-irr {Γ = Γ} w u x)
restrict-bind {Γ = Γ} One  Many (o≤m ⊑∷ w) u x a = cong (_, a) (restrict-irr {Γ = Γ} w u x)
restrict-bind {Γ = Γ} Many Many (m≤m ⊑∷ w) u x a = cong (_, a) (restrict-irr {Γ = Γ} w u x)
