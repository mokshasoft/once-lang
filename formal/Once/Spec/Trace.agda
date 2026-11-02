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
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.Spec.Signature using (Event)
open import Once.Spec.Delay using (Delay; _⇓_; _≈⟨_⟩_)

-- How a run ends: with a value, halted by a call with no answer, or
-- exhausted: out of memory. A source program never runs out (the Spec's
-- model has unlimited memory: `Spec.Metatheory`'s `never-exhausted`, D348);
-- only a compiled program's run ends `exhausted` (D347).
data End (X : Set) : Set where
  returned  : X → End X
  halted    : End X
  exhausted : End X

record Tr (X : Set) : Set where
  coinductive
  field next : Delay (End X ⊎ (Event × Tr X))
open Tr

------------------------------------------------------------------------
-- Weak bisimilarity
------------------------------------------------------------------------

-- Two ends: the same way, the values related.
data EndRel {X : Set} (R : X → X → Set) : End X → End X → Set where
  returned≈  : ∀ {x y} → R x y → EndRel R (returned x) (returned y)
  halted≈    : EndRel R halted halted
  exhausted≈ : EndRel R exhausted exhausted

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

------------------------------------------------------------------------
-- Up to running out
------------------------------------------------------------------------

-- `t ⊑ᵗ⟨ R ⟩ s`: the run t does what s does, except that it may end
-- `exhausted` at any point, and then it matches whatever s does from there
-- on (CakeML's `extend_with_resource_limit`). Every call t makes before it
-- runs out is the call s makes; t never stops silently where s goes on, and
-- never goes on where s ends. It is not symmetric: s is the source's trace,
-- which never runs out. A run that ran out at once matches every s; that a
-- program does NOT run out is a separate, space claim (D347).

record _⊑ᵗ⟨_⟩_ {X : Set} (t : Tr X) (R : X → X → Set) (s : Tr X) : Set where
  coinductive
  field
    -- t's next visible step: it ran out, or s takes a step related to it
    sound    : ∀ a → next t ⇓ a →
               a ≡ inj₁ exhausted ⊎ ∃[ b ] (next s ⇓ b × StepRel R (λ u u′ → u ⊑ᵗ⟨ R ⟩ u′) a b)
    -- s's next visible step: t runs out, or takes a step related to it
    complete : ∀ b → next s ⇓ b →
               next t ⇓ inj₁ exhausted ⊎ ∃[ a ] (next t ⇓ a × StepRel R (λ u u′ → u ⊑ᵗ⟨ R ⟩ u′) a b)
open _⊑ᵗ⟨_⟩_

infix 4 _⊑ᵗ⟨_⟩_

-- The calls a trace makes first.
data Calls {X : Set} : Tr X → List Event → Set where
  none : ∀ {t} → Calls t []
  call : ∀ {t v t′ vs} → next t ⇓ inj₂ (v , t′) → Calls t′ vs → Calls t (v ∷ vs)

-- The trace ends `e`: after finitely many calls, its run ends there.
data Ends {X : Set} : Tr X → End X → Set where
  ends-now   : ∀ {t e} → next t ⇓ inj₁ e → Ends t e
  ends-after : ∀ {t v t′ e} → next t ⇓ inj₂ (v , t′) → Ends t′ e → Ends t e
