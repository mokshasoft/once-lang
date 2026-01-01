------------------------------------------------------------------------
-- Once.Backend.Common.Star
--
-- Common Star (reflexive-transitive closure) infrastructure for all
-- backend architectures (X86, AArch64, RiscV64).
--
-- This module is parameterized by the backend-specific Program and State
-- types, along with the halted predicate and step function. This allows
-- all backends to share the core Star semantics while maintaining their
-- architecture-specific execution semantics.
--
-- Usage:
--   module Once.Backend.MyArch.Correct.Star where
--     open import Once.Backend.MyArch.Syntax
--     open import Once.Backend.MyArch.Semantics
--     open State
--     open import Once.Backend.Common.Star Program State halted step public
--
-- Benefits:
--   - Single source of truth for Star semantics
--   - Automatic uniformity across backends
--   - Easier to extend (new helpers benefit all backends)
--   - Reduced code duplication (~115 lines per backend)
------------------------------------------------------------------------

open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module Once.Backend.Common.Star
  (Program : Set)
  (State : Set)
  (halted : State → Bool)
  (step : Program → State → Maybe State)
  where

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
-- Step Chaining Combinators
--
-- These make building long chains of steps readable:
--   star-all = step-0 ◅ step-1 ◅ step-2 ◅ ... ◅ step-n ◅ refl*
--
-- Compare to the old approach with nested exec-chain-2 calls!
------------------------------------------------------------------------

-- | Prepend a single step to a Star (snoc-style chaining)
-- Usage: star-single h₁ step₁ ◅◅ star-rest
infixr 5 _◅◅_
_◅◅_ : ∀ {prog s s' s''} →
       Star prog s s' →
       Star prog s' s'' →
       Star prog s s''
_◅◅_ = star-trans

-- | Build Star from step proof and continuation
-- Usage: ⟨ h , step-eq ⟩◅ star-rest
infixr 5 ⟨_,_⟩◅_
⟨_,_⟩◅_ : ∀ {prog s s' s''} →
          halted s ≡ false →
          step prog s ≡ just s' →
          Star prog s' s'' →
          Star prog s s''
⟨ h , step-eq ⟩◅ rest = step* h step-eq rest

------------------------------------------------------------------------
-- Helper Combinators (star-stepN)
--
-- These chain N steps into a single Star proof.
-- Useful for proving execution of fixed-length instruction sequences.
------------------------------------------------------------------------

-- | Chain 2 steps
star-step2 : ∀ {prog s₀ s₁ s₂} →
    halted s₀ ≡ false → step prog s₀ ≡ just s₁ →
    halted s₁ ≡ false → step prog s₁ ≡ just s₂ →
    Star prog s₀ s₂
star-step2 h₀ step₀ h₁ step₁ =
  ⟨ h₀ , step₀ ⟩◅ ⟨ h₁ , step₁ ⟩◅ refl*

-- | Chain 3 steps
star-step3 : ∀ {prog s₀ s₁ s₂ s₃} →
    halted s₀ ≡ false → step prog s₀ ≡ just s₁ →
    halted s₁ ≡ false → step prog s₁ ≡ just s₂ →
    halted s₂ ≡ false → step prog s₂ ≡ just s₃ →
    Star prog s₀ s₃
star-step3 h₀ step₀ h₁ step₁ h₂ step₂ =
  ⟨ h₀ , step₀ ⟩◅ ⟨ h₁ , step₁ ⟩◅ ⟨ h₂ , step₂ ⟩◅ refl*

-- | Chain 4 steps
star-step4 : ∀ {prog s₀ s₁ s₂ s₃ s₄} →
    halted s₀ ≡ false → step prog s₀ ≡ just s₁ →
    halted s₁ ≡ false → step prog s₁ ≡ just s₂ →
    halted s₂ ≡ false → step prog s₂ ≡ just s₃ →
    halted s₃ ≡ false → step prog s₃ ≡ just s₄ →
    Star prog s₀ s₄
star-step4 h₀ step₀ h₁ step₁ h₂ step₂ h₃ step₃ =
  ⟨ h₀ , step₀ ⟩◅ ⟨ h₁ , step₁ ⟩◅ ⟨ h₂ , step₂ ⟩◅ ⟨ h₃ , step₃ ⟩◅ refl*

-- | Chain 5 steps
star-step5 : ∀ {prog s₀ s₁ s₂ s₃ s₄ s₅} →
    halted s₀ ≡ false → step prog s₀ ≡ just s₁ →
    halted s₁ ≡ false → step prog s₁ ≡ just s₂ →
    halted s₂ ≡ false → step prog s₂ ≡ just s₃ →
    halted s₃ ≡ false → step prog s₃ ≡ just s₄ →
    halted s₄ ≡ false → step prog s₄ ≡ just s₅ →
    Star prog s₀ s₅
star-step5 h₀ step₀ h₁ step₁ h₂ step₂ h₃ step₃ h₄ step₄ =
  ⟨ h₀ , step₀ ⟩◅ ⟨ h₁ , step₁ ⟩◅ ⟨ h₂ , step₂ ⟩◅ ⟨ h₃ , step₃ ⟩◅ ⟨ h₄ , step₄ ⟩◅ refl*

-- | Chain 6 steps (useful for apply's 6 instructions in AArch64)
star-step6 : ∀ {prog s₀ s₁ s₂ s₃ s₄ s₅ s₆} →
    halted s₀ ≡ false → step prog s₀ ≡ just s₁ →
    halted s₁ ≡ false → step prog s₁ ≡ just s₂ →
    halted s₂ ≡ false → step prog s₂ ≡ just s₃ →
    halted s₃ ≡ false → step prog s₃ ≡ just s₄ →
    halted s₄ ≡ false → step prog s₄ ≡ just s₅ →
    halted s₅ ≡ false → step prog s₅ ≡ just s₆ →
    Star prog s₀ s₆
star-step6 h₀ step₀ h₁ step₁ h₂ step₂ h₃ step₃ h₄ step₄ h₅ step₅ =
  ⟨ h₀ , step₀ ⟩◅ ⟨ h₁ , step₁ ⟩◅ ⟨ h₂ , step₂ ⟩◅ ⟨ h₃ , step₃ ⟩◅ ⟨ h₄ , step₄ ⟩◅ ⟨ h₅ , step₅ ⟩◅ refl*

------------------------------------------------------------------------
-- Infix Notation
------------------------------------------------------------------------

-- | Infix operator for Star (optional, for readability)
-- Usage: prog ⟶* s₀ $ s₁
infix 4 _⟶*_
_⟶*_ : Program → State → State → Set
prog ⟶* s = Star prog s
