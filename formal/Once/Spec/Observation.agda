{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Observation — the world, and what a computation does in it.
--
-- The world has two parts. Its MODEL gives the signature's values (constants
-- and pure functions): what a program's meaning reads. Its ANSWERS reply to
-- the operations, from what the world has seen so far: what a run reads.
-- The world answers whenever an answer exists; a call whose answer type is
-- empty has no continuation, and the run halts there.
--
-- What a computation does in a world is its TRACE: the final coalgebra of
-- `Delay ∘ (End + Event × −)` — after finitely many silent steps it ends, or
-- makes one call and goes on, or it never does either. Two traces are the
-- same when they are WEAKLY BISIMILAR: the next call or end arrives in both
-- or in neither, the same call, the rests again the same; how many silent
-- steps it takes is not observed (D179, D317).
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)

module Once.Spec.Observation (Σ : Signature) where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (Dec; yes; no)
open import Once.Spec.Signature
  using (BTy; ⟦_⟧ᵇ; NotEmpty; notEmpty?; constant; value; _∶_; Op; module Op; arg; argAt; call; Event; eventOf)
open Op using (ans)
open import Once.Spec.Effect Σ using (T; roll; done; node; T∞; force)
open import Once.Spec.Delay using (Delay; module Delay; now; _⇓_; _≈⟨_⟩_)
open Delay using (step)

------------------------------------------------------------------------
-- The world
------------------------------------------------------------------------

History : Set
History = List Event

-- The signature's values.
record Model : Set where
  field
    constantᵐ : ∀ {c b} → (c ∶ constant b) ∈ Σ → ⟦ b ⟧ᵇ
    valueᵐ    : ∀ {c a q b} → (c ∶ value a q b) ∈ Σ → ⟦ argAt q a ⟧ᵇ → ⟦ b ⟧ᵇ

-- The answers, from the calls the world has seen, whenever one exists.
record World : Set where
  field
    answer : (o : Op Σ) → History → ⟦ arg o ⟧ᵇ → NotEmpty (ans o) → ⟦ ans o ⟧ᵇ

-- An Interpretation of Σ: a model and a world.
record Interp : Set where
  field
    model : Model
    world : World

------------------------------------------------------------------------
-- Traces
------------------------------------------------------------------------

-- How a run ends: with a value, or halted by a call with no answer.
data End (X : Set) : Set where
  returned : X → End X
  halted   : End X

record Tr (X : Set) : Set where
  coinductive
  field next : Delay (End X ⊎ (Event × Tr X))
open Tr

-- The trace of a computation in a world that has seen `h`: each call is a
-- visible step, the end of a block a silent one.
module _ (w : World) where
  open World w using (answer)

  trace  : ∀ {X} → History → T∞ X → Tr X
  blockD : ∀ {X} → History → T (X ⊎ T∞ X) → Delay (End X ⊎ (Event × Tr X))
  after  : ∀ {X} → History → (o : Op Σ) → ⟦ arg o ⟧ᵇ → (⟦ ans o ⟧ᵇ → T (X ⊎ T∞ X)) → Dec (NotEmpty (ans o)) → Tr X
  next (trace h m) = blockD h (force m)
  step (blockD h (roll (done (inj₁ x))))     = inj₁ (inj₁ (returned x))
  step (blockD h (roll (done (inj₂ m))))     = inj₂ (blockD h (force m))
  step (blockD h (roll (node (call o a k)))) = inj₁ (inj₂ (eventOf o a , after h o a k (notEmpty? (ans o))))
  next (after h o a k (yes p)) = blockD (h ++ [ eventOf o a ]) (k (answer o h a p))
  next (after h o a k (no _))  = now (inj₁ halted)

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
