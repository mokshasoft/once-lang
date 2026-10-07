-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.EnvAlgebraV — `EnvAlgebra`'s environment laws over the
-- GRADED domain `⟦_⟧ᵛ` (D250, plan 0.104), clause for clause: an environment is
-- a nested product, so the laws do not depend on the grade.
------------------------------------------------------------------------

module Once.Denotation.EnvAlgebraV where

open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans)

open import Once.Type using (Type; Quantity; Zero; One; Many)
open import Once.Surface.Context
  using (Ctx; ∅; _,_^_; Usage; _∷_; _↾_; _⊑ᵘ_; ⊑[]; _⊑∷_; _≤q'_; z≤z; z≤o; z≤m; o≤o; o≤m; m≤m; ⊑ᵘ-trans)
  renaming (⟦_⟧ᶜ to ⟦_⟧ᶜᵗ)
open import Once.Denotation.GradedDomain using (⟦_⟧ᵛ)
open import Once.Denotation.PhaseV using (restrictᵛ; bindᵛ)

Env : ∀ {n} → Ctx n → Usage n → Set
Env Γ Ψ = ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᵛ

------------------------------------------------------------------------
-- Proof irrelevance
------------------------------------------------------------------------

≤q'-unique : ∀ {q r} (a b : q ≤q' r) → a ≡ b
≤q'-unique z≤z z≤z = refl
≤q'-unique z≤o z≤o = refl
≤q'-unique z≤m z≤m = refl
≤q'-unique o≤o o≤o = refl
≤q'-unique o≤m o≤m = refl
≤q'-unique m≤m m≤m = refl

⊑ᵘ-unique : ∀ {n} {Ψ Φ : Usage n} (u v : Ψ ⊑ᵘ Φ) → u ≡ v
⊑ᵘ-unique ⊑[]       ⊑[]       = refl
⊑ᵘ-unique (a ⊑∷ u) (b ⊑∷ v) = cong₂ _⊑∷_ (≤q'-unique a b) (⊑ᵘ-unique u v)

restrict-irr : ∀ {n} {Γ : Ctx n} {Ψ Ψ' : Usage n} (u v : Ψ' ⊑ᵘ Ψ) (x : Env Γ Ψ)
             → restrictᵛ {Γ = Γ} u x ≡ restrictᵛ {Γ = Γ} v x
restrict-irr {Γ = Γ} u v x = cong (λ w → restrictᵛ {Γ = Γ} w x) (⊑ᵘ-unique u v)

------------------------------------------------------------------------
-- Identity and composition
------------------------------------------------------------------------

restrict-refl : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} (u : Ψ ⊑ᵘ Ψ) (x : Env Γ Ψ) → restrictᵛ {Γ = Γ} u x ≡ x
restrict-refl {Γ = ∅}         ⊑[]        x = refl
restrict-refl {Γ = Γ , A ^ q} (z≤z ⊑∷ u) x = restrict-refl {Γ = Γ} u x
restrict-refl {Γ = Γ , A ^ q} (o≤o ⊑∷ u) x = cong (_, proj₂ x) (restrict-refl {Γ = Γ} u (proj₁ x))
restrict-refl {Γ = Γ , A ^ q} (m≤m ⊑∷ u) x = cong (_, proj₂ x) (restrict-refl {Γ = Γ} u (proj₁ x))

restrict-∘ : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ Ψ₃ : Usage n} (u : Ψ₁ ⊑ᵘ Ψ₂) (v : Ψ₂ ⊑ᵘ Ψ₃) (x : Env Γ Ψ₃)
           → restrictᵛ {Γ = Γ} u (restrictᵛ {Γ = Γ} v x) ≡ restrictᵛ {Γ = Γ} (⊑ᵘ-trans u v) x
restrict-∘ {Γ = ∅}         ⊑[]        ⊑[]        x = refl
restrict-∘ {Γ = Γ , A ^ q} (z≤z ⊑∷ u) (z≤z ⊑∷ v) x = restrict-∘ {Γ = Γ} u v x
restrict-∘ {Γ = Γ , A ^ q} (z≤z ⊑∷ u) (z≤o ⊑∷ v) x = restrict-∘ {Γ = Γ} u v (proj₁ x)
restrict-∘ {Γ = Γ , A ^ q} (z≤z ⊑∷ u) (z≤m ⊑∷ v) x = restrict-∘ {Γ = Γ} u v (proj₁ x)
restrict-∘ {Γ = Γ , A ^ q} (z≤o ⊑∷ u) (o≤o ⊑∷ v) x = restrict-∘ {Γ = Γ} u v (proj₁ x)
restrict-∘ {Γ = Γ , A ^ q} (z≤o ⊑∷ u) (o≤m ⊑∷ v) x = restrict-∘ {Γ = Γ} u v (proj₁ x)
restrict-∘ {Γ = Γ , A ^ q} (z≤m ⊑∷ u) (m≤m ⊑∷ v) x = restrict-∘ {Γ = Γ} u v (proj₁ x)
restrict-∘ {Γ = Γ , A ^ q} (o≤o ⊑∷ u) (o≤o ⊑∷ v) x = cong (_, proj₂ x) (restrict-∘ {Γ = Γ} u v (proj₁ x))
restrict-∘ {Γ = Γ , A ^ q} (o≤o ⊑∷ u) (o≤m ⊑∷ v) x = cong (_, proj₂ x) (restrict-∘ {Γ = Γ} u v (proj₁ x))
restrict-∘ {Γ = Γ , A ^ q} (o≤m ⊑∷ u) (m≤m ⊑∷ v) x = cong (_, proj₂ x) (restrict-∘ {Γ = Γ} u v (proj₁ x))
restrict-∘ {Γ = Γ , A ^ q} (m≤m ⊑∷ u) (m≤m ⊑∷ v) x = cong (_, proj₂ x) (restrict-∘ {Γ = Γ} u v (proj₁ x))

-- Any two restrictions of one environment to one usage agree.
restrict-≡ : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ Ψ₃ : Usage n} (u : Ψ₁ ⊑ᵘ Ψ₂) (v : Ψ₂ ⊑ᵘ Ψ₃) (w : Ψ₁ ⊑ᵘ Ψ₃) (x : Env Γ Ψ₃)
           → restrictᵛ {Γ = Γ} u (restrictᵛ {Γ = Γ} v x) ≡ restrictᵛ {Γ = Γ} w x
restrict-≡ {Γ = Γ} u v w x = trans (restrict-∘ {Γ = Γ} u v x) (restrict-irr {Γ = Γ} (⊑ᵘ-trans u v) w x)

------------------------------------------------------------------------
-- Binders
------------------------------------------------------------------------

-- Restricting an extended environment: the bound variable is dropped when the
-- restricted usage does not use it, and kept when it does.
restrict-bind : ∀ {n} {Γ : Ctx n} {A : Type} {Ψ' Ψ : Usage n} (q' q : Quantity)
                  (w : (q' ∷ Ψ') ⊑ᵘ (q ∷ Ψ)) (u : Ψ' ⊑ᵘ Ψ) (x : Env Γ Ψ) (a : ⟦ A ⟧ᵛ)
              → restrictᵛ {Γ = Γ , A ^ Many} w (bindᵛ {Γ = Γ} {A = A} q x a)
                ≡ bindᵛ {Γ = Γ} {A = A} q' (restrictᵛ {Γ = Γ} u x) a
restrict-bind {Γ = Γ} Zero Zero (z≤z ⊑∷ w) u x a = restrict-irr {Γ = Γ} w u x
restrict-bind {Γ = Γ} Zero One  (z≤o ⊑∷ w) u x a = restrict-irr {Γ = Γ} w u x
restrict-bind {Γ = Γ} Zero Many (z≤m ⊑∷ w) u x a = restrict-irr {Γ = Γ} w u x
restrict-bind {Γ = Γ} One  One  (o≤o ⊑∷ w) u x a = cong (_, a) (restrict-irr {Γ = Γ} w u x)
restrict-bind {Γ = Γ} One  Many (o≤m ⊑∷ w) u x a = cong (_, a) (restrict-irr {Γ = Γ} w u x)
restrict-bind {Γ = Γ} Many Many (m≤m ⊑∷ w) u x a = cong (_, a) (restrict-irr {Γ = Γ} w u x)
