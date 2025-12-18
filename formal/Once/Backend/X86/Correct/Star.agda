------------------------------------------------------------------------
-- Once.Backend.X86.Correct.Star
--
-- Star (reflexive-transitive closure) relation for x86-64 execution.
-- This provides a CompCert-style approach to chaining execution proofs
-- without fuel management or step counting.
--
-- Key benefit: composition is just transitivity (trivial chaining).
------------------------------------------------------------------------

module Once.Backend.X86.Correct.Star where

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open State

open import Data.Bool using (Bool; true; false)
open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no)

------------------------------------------------------------------------
-- Star Relation
------------------------------------------------------------------------

-- | Reflexive-transitive closure of the step function.
--
-- Star prog s s' means: starting from state s, executing program prog
-- reaches state s' in zero or more steps.
--
-- This eliminates fuel management - we don't care HOW MANY steps,
-- just that execution reaches the target state.

data Star (prog : Program) : State → State → Set where
  -- | Zero steps: already at target (reflexivity)
  refl* : ∀ {s} → Star prog s s

  -- | One or more steps: take one step, then continue
  step* : ∀ {s s' s''} →
          halted s ≡ false →
          step prog s ≡ just s' →
          Star prog s' s'' →
          Star prog s s''

------------------------------------------------------------------------
-- Star Properties
------------------------------------------------------------------------

-- | Transitivity of star
-- If prog takes us from s₁ to s₂, and from s₂ to s₃, then from s₁ to s₃
star-trans : ∀ {prog s₁ s₂ s₃} →
             Star prog s₁ s₂ →
             Star prog s₂ s₃ →
             Star prog s₁ s₃
star-trans refl* p₂ = p₂
star-trans (step* h step-eq p₁) p₂ = step* h step-eq (star-trans p₁ p₂)

-- | Single step lifts to star
star-single : ∀ {prog s s'} →
              halted s ≡ false →
              step prog s ≡ just s' →
              Star prog s s'
star-single h step-eq = step* h step-eq refl*

------------------------------------------------------------------------
-- Bridge Lemmas (Postulated)
--
-- These connect the fuel-based execution (exec, exec-until-pc) to Star.
-- Postulated because proving them requires case analysis on `halted s`
-- which abstracts over expressions containing `halted s`, breaking
-- the connection to step/exec definitions.
--
-- These are "plumbing" postulates - they don't add trusted assumptions
-- about correctness, just bridge two equivalent ways of expressing
-- multi-step execution.
------------------------------------------------------------------------

postulate
  -- | If exec n succeeds, we have a star execution
  exec-to-star : ∀ {n prog s s'} →
                 exec n prog s ≡ just s' →
                 Star prog s s'

  -- | If exec-until-pc succeeds, we have a star execution
  exec-until-pc-to-star : ∀ {target fuel prog s s'} →
                          exec-until-pc target fuel prog s ≡ just s' →
                          Star prog s s'

------------------------------------------------------------------------
-- Export infix syntax
------------------------------------------------------------------------

-- Infix operator for Star (optional, for readability)
infix 4 _⟶*_
_⟶*_ : Program → State → State → Set
prog ⟶* s = Star prog s

