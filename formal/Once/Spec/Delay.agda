{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Delay — a value that may take any number of steps to arrive,
-- or never arrive (Capretta's delay monad, `Delay A = νY. A + Y`).
--
-- Two delays are the same when they arrive at related values or neither
-- ever arrives; how many steps it takes is not observed (D179).
------------------------------------------------------------------------

module Once.Spec.Delay where

open import Data.Product using (_×_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

record Delay (A : Set) : Set where
  coinductive
  field step : A ⊎ Delay A
open Delay

-- What arrives, transformed.
mapD : ∀ {A B : Set} → (A → B) → Delay A → Delay B
mapStep : ∀ {A B : Set} → (A → B) → A ⊎ Delay A → B ⊎ Delay B
step (mapD f d) = mapStep f (step d)
mapStep f (inj₁ a) = inj₁ (f a)
mapStep f (inj₂ d) = inj₂ (mapD f d)

-- `d` arrives at `a`, after finitely many steps.
data _⇓_ {A : Set} (d : Delay A) (a : A) : Set where
  now⇓   : step d ≡ inj₁ a → d ⇓ a
  later⇓ : ∀ {d′} → step d ≡ inj₂ d′ → d′ ⇓ a → d ⇓ a

infix 4 _⇓_

-- The same up to `R`: whatever one arrives at, the other arrives at a value
-- related to it.
_≈⟨_⟩_ : ∀ {A B : Set} → Delay A → (A → B → Set) → Delay B → Set
d ≈⟨ R ⟩ d′ = (∀ a → d ⇓ a → ∃[ b ] (d′ ⇓ b × R a b)) × (∀ b → d′ ⇓ b → ∃[ a ] (d ⇓ a × R a b))

-- The same.
_≈D_ : ∀ {A : Set} → Delay A → Delay A → Set
d ≈D d′ = d ≈⟨ _≡_ ⟩ d′

infix 4 _≈D_
