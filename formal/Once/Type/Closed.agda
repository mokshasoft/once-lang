-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Type.Closed — a type of no variables is the same type under any
-- substitution.
--
-- Two substitutions out of `Fin 0` are equal only by function
-- extensionality; their results on a closed type are equal by induction on
-- the type. So the compiler's weakening (`wk₀ T = T ⟨ none ⟩`) is the Spec's
-- `↑ T = T ⟨ (λ ()) ⟩` with no postulate.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Once.Type.Closed where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Once.Spec.Type using (Ty; Fun; TySub; _⟨_⟩; _⟨_⟩F; var; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ; ν; K; Id; _⊕_; _⊗_)

mutual
  sub0 : ∀ {m} (T : Ty 0) (σ σ′ : TySub 0 m) → T ⟨ σ ⟩ ≡ T ⟨ σ′ ⟩
  sub0 (var ()) σ σ′
  sub0 Unit  σ σ′ = refl
  sub0 Void  σ σ′ = refl
  sub0 Int   σ σ′ = refl
  sub0 Float σ σ′ = refl
  sub0 (A * B) σ σ′ = cong₂ _*_ (sub0 A σ σ′) (sub0 B σ σ′)
  sub0 (A + B) σ σ′ = cong₂ _+_ (sub0 A σ σ′) (sub0 B σ σ′)
  sub0 (A ⇒[ k ] B) σ σ′ = cong₂ (λ X Y → X ⇒[ k ] Y) (sub0 A σ σ′) (sub0 B σ σ′)
  sub0 (μ F) σ σ′ = cong μ (sub0F F σ σ′)
  sub0 (ν F φ) σ σ′ = cong (λ G → ν G φ) (sub0F F σ σ′)

  sub0F : ∀ {m} (F : Fun 0) (σ σ′ : TySub 0 m) → F ⟨ σ ⟩F ≡ F ⟨ σ′ ⟩F
  sub0F (K A) σ σ′ = cong K (sub0 A σ σ′)
  sub0F Id σ σ′ = refl
  sub0F (F ⊕ G) σ σ′ = cong₂ _⊕_ (sub0F F σ σ′) (sub0F G σ σ′)
  sub0F (F ⊗ G) σ σ′ = cong₂ _⊗_ (sub0F F σ σ′) (sub0F G σ σ′)

-- …at an arity known to be zero.
sub0≡ : ∀ {n m} → n ≡ 0 → (T : Ty n) (σ σ′ : TySub n m) → T ⟨ σ ⟩ ≡ T ⟨ σ′ ⟩
sub0≡ refl = sub0
