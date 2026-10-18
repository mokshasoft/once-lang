{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Trace — what a run does, and when two runs do the same.
--
-- A TRACE is the final coalgebra of `Delay ∘ (End + Event × −)` — after
-- finitely many silent steps it ends, or makes one call and goes on, or it
-- never does either. Two traces are the same when they are WEAKLY BISIMILAR:
-- the next call or end arrives in both or in neither, the same call, the rests
-- again the same; how many silent steps it takes is not observed (D179, D317).
--
-- A trace mentions events only, never a signature: every program's behaviour
-- has the one type `Tr ⊤`.
------------------------------------------------------------------------

module Once.Spec.Trace where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.Spec.Signature using (Event)
open import Once.Spec.Delay using (Delay; _⇓_; _≈⟨_⟩_)

-- How a run ends: with a value, or halted by a call with no answer.
data End (X : Set) : Set where
  returned : X → End X
  halted   : End X

record Tr (X : Set) : Set where
  coinductive
  field next : Delay (End X ⊎ (Event × Tr X))
open Tr

------------------------------------------------------------------------
-- Weak bisimilarity
------------------------------------------------------------------------

-- Two ends: the same way, the values related.
data EndRel {X : Set} (R : X → X → Set) : End X → End X → Set where
  returned≈ : ∀ {x y} → R x y → EndRel R (returned x) (returned y)
  halted≈   : EndRel R halted halted

-- Two visible steps: related ends, or the same call and related rests.
StepRel : ∀ {X : Set} → (X → X → Set) → (Tr X → Tr X → Set) → End X ⊎ (Event × Tr X) → End X ⊎ (Event × Tr X) → Set
StepRel R S (inj₁ e)       (inj₁ e′)        = EndRel R e e′
StepRel R S (inj₂ (v , t)) (inj₂ (v′ , t′)) = v ≡ v′ × S t t′
StepRel R S (inj₁ _)       (inj₂ _)         = ⊥
StepRel R S (inj₂ _)       (inj₁ _)         = ⊥

record _≈ᵗ⟨_⟩_ {X : Set} (t : Tr X) (R : X → X → Set) (t′ : Tr X) : Set where
  coinductive
  field same : next t ≈⟨ StepRel R (λ u u′ → u ≈ᵗ⟨ R ⟩ u′) ⟩ next t′
open _≈ᵗ⟨_⟩_

infix 4 _≈ᵗ⟨_⟩_

-- The calls a trace makes first.
data Calls {X : Set} : Tr X → List Event → Set where
  none : ∀ {t} → Calls t []
  call : ∀ {t v t′ vs} → next t ⇓ inj₂ (v , t′) → Calls t′ vs → Calls t (v ∷ vs)
