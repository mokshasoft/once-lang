------------------------------------------------------------------------
-- Once.Backend.X86.Correct.Star
--
-- Star transition relation: reflexive-transitive closure of step.
-- This provides a CompCert-style approach to execution proofs without
-- fuel counting or step arithmetic.
--
-- Level 0 - no dependencies on other Correct modules
------------------------------------------------------------------------

module Once.Backend.X86.Correct.Star where

open import Once.Backend.X86.Syntax using (Program)
open import Once.Backend.X86.Semantics using (State; step)

open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

-- Use State.halted as qualified access
halted : State → Bool
halted = Once.Backend.X86.Semantics.State.halted

------------------------------------------------------------------------
-- Star transition relation
------------------------------------------------------------------------

-- | Reflexive-transitive closure of single-step execution.
--
-- Design choices:
-- - `refl`: reflexivity for any state (0-step execution)
-- - `more`: take one step, then continue
--
-- This design allows trivial transitivity and doesn't require
-- halted/non-halted distinction for reflexivity.

data Star (prog : Program) : State → State → Set where
  -- | Reflexivity: 0-step execution (any state reaches itself)
  star-refl : ∀ {s} → Star prog s s

  -- | One step followed by star: if s →₁ s' and s' →* s'', then s →* s''
  star-step : ∀ {s s' s''} →
              halted s ≡ false →
              step prog s ≡ just s' →
              Star prog s' s'' →
              Star prog s s''

-- Infix syntax for readability: prog ⊢ s ↠* s'
-- (using ↠ which is a cleaner ASCII-ish arrow)
infix 4 _⊢_↠*_
_⊢_↠*_ : Program → State → State → Set
prog ⊢ s ↠* s' = Star prog s s'

------------------------------------------------------------------------
-- Basic properties
------------------------------------------------------------------------

-- | Transitivity: key property for composition!
-- If s₁ →* s₂ and s₂ →* s₃, then s₁ →* s₃
star-trans : ∀ {prog : Program} {s₁ s₂ s₃ : State} →
             Star prog s₁ s₂ →
             Star prog s₂ s₃ →
             Star prog s₁ s₃
star-trans star-refl p2 = p2
star-trans (star-step h step-eq cont) p2 = star-step h step-eq (star-trans cont p2)

-- | Single step lifts to star
star-one : ∀ {prog : Program} {s s' : State} →
           halted s ≡ false →
           step prog s ≡ just s' →
           Star prog s s'
star-one h step-eq = star-step h step-eq star-refl

-- | Two steps lift to star
star-two : ∀ {prog : Program} {s s₁ s₂ : State} →
           halted s ≡ false →
           step prog s ≡ just s₁ →
           halted s₁ ≡ false →
           step prog s₁ ≡ just s₂ →
           Star prog s s₂
star-two h1 step1 h2 step2 = star-step h1 step1 (star-one h2 step2)

-- | Three steps lift to star
star-three : ∀ {prog : Program} {s s₁ s₂ s₃ : State} →
             halted s ≡ false →
             step prog s ≡ just s₁ →
             halted s₁ ≡ false →
             step prog s₁ ≡ just s₂ →
             halted s₂ ≡ false →
             step prog s₂ ≡ just s₃ →
             Star prog s s₃
star-three h1 step1 h2 step2 h3 step3 =
  star-step h1 step1 (star-two h2 step2 h3 step3)

------------------------------------------------------------------------
-- Derived properties
------------------------------------------------------------------------

-- | Prepend a single step to a star proof
star-cons : ∀ {prog : Program} {s s' s'' : State} →
            halted s ≡ false →
            step prog s ≡ just s' →
            Star prog s' s'' →
            Star prog s s''
star-cons = star-step

-- | Append a single step to a star proof
star-snoc : ∀ {prog : Program} {s s' s'' : State} →
            Star prog s s' →
            halted s' ≡ false →
            step prog s' ≡ just s'' →
            Star prog s s''
star-snoc p h step-eq = star-trans p (star-one h step-eq)
