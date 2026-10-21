{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Type.Substitution — substitution is functorial: an instance of an
-- instance is the composed instance, and it keeps respecting the kinds.
--
-- THE ONE EXEMPTION from "the Spec is proof-free" (D335, MERGE.md §1). The
-- meaning of a reference to a polymorphic definition, inside a body read at
-- an instance of its own type variables, is the definition's value at the
-- composed instance; that value's type agrees with the reference's only by
-- the law below. Every formulation of the meaning of polymorphism needs it:
-- it is part of the definition of the language, not a claim about any
-- implementation. Nothing else in the Spec proves anything.
------------------------------------------------------------------------

module Once.Spec.Type.Substitution where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Once.Spec.Type

-- What the meaning of a reference to a definition at an instance needs: an
-- instance of an instance is an instance — it composes, and it keeps
-- respecting the kinds.
base-⟨⟩ : ∀ {m k} {Δ : KCtx m} {Δ′ : KCtx k} {σ : TySub m k} {A} → Respects Δ Δ′ σ → Base Δ A → Base Δ′ (A ⟨ σ ⟩)
base-⟨⟩ r (b-var e) = r _ e
base-⟨⟩ r b-Unit    = b-Unit
base-⟨⟩ r b-Void    = b-Void
base-⟨⟩ r b-Int     = b-Int
base-⟨⟩ r b-Float   = b-Float
base-⟨⟩ r (b-* a b) = b-* (base-⟨⟩ r a) (base-⟨⟩ r b)
base-⟨⟩ r (b-+ a b) = b-+ (base-⟨⟩ r a) (base-⟨⟩ r b)

respects-∘ : ∀ {m k l} {Δ : KCtx m} {Δ′ : KCtx k} {Δ″ : KCtx l} {σ : TySub m k} {τ : TySub k l}
           → Respects Δ Δ′ σ → Respects Δ′ Δ″ τ → Respects Δ Δ″ (λ i → σ i ⟨ τ ⟩)
respects-∘ rσ rτ i e = base-⟨⟩ rτ (rσ i e)

mutual
  ⟨⟩-∘ : ∀ {m k l} (A : Ty m) (σ : TySub m k) (τ : TySub k l) → A ⟨ σ ⟩ ⟨ τ ⟩ ≡ A ⟨ (λ i → σ i ⟨ τ ⟩) ⟩
  ⟨⟩-∘ (var i)      σ τ = refl
  ⟨⟩-∘ Unit         σ τ = refl
  ⟨⟩-∘ Void         σ τ = refl
  ⟨⟩-∘ (A * B)      σ τ = cong₂ _*_ (⟨⟩-∘ A σ τ) (⟨⟩-∘ B σ τ)
  ⟨⟩-∘ (A + B)      σ τ = cong₂ _+_ (⟨⟩-∘ A σ τ) (⟨⟩-∘ B σ τ)
  ⟨⟩-∘ (A ⇒[ k ] B) σ τ = cong₂ (λ a b → a ⇒[ k ] b) (⟨⟩-∘ A σ τ) (⟨⟩-∘ B σ τ)
  ⟨⟩-∘ (μ F)        σ τ = cong μ (⟨⟩F-∘ F σ τ)
  ⟨⟩-∘ (ν F f)      σ τ = cong (λ G → ν G f) (⟨⟩F-∘ F σ τ)
  ⟨⟩-∘ Int          σ τ = refl
  ⟨⟩-∘ Float        σ τ = refl

  ⟨⟩F-∘ : ∀ {m k l} (F : Fun m) (σ : TySub m k) (τ : TySub k l) → F ⟨ σ ⟩F ⟨ τ ⟩F ≡ F ⟨ (λ i → σ i ⟨ τ ⟩) ⟩F
  ⟨⟩F-∘ (K A)   σ τ = cong K (⟨⟩-∘ A σ τ)
  ⟨⟩F-∘ Id      σ τ = refl
  ⟨⟩F-∘ (F ⊕ G) σ τ = cong₂ _⊕_ (⟨⟩F-∘ F σ τ) (⟨⟩F-∘ G σ τ)
  ⟨⟩F-∘ (F ⊗ G) σ τ = cong₂ _⊗_ (⟨⟩F-∘ F σ τ) (⟨⟩F-∘ G σ τ)
