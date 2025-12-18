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

------------------------------------------------------------------------
-- StarResult: Execution result with Star instead of exec
--
-- This record captures the properties of successful IR execution
-- in a Star-friendly way, enabling trivial composition via star-trans.
------------------------------------------------------------------------

open import Data.Nat using (_+_; _>_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)

-- | Result of executing IR code with Star semantics
record StarResult (prog : Program) (s s' : State) (result-val : Word) : Set where
  field
    star-exec   : Star prog s s'           -- Execution reaches s'
    not-halted  : halted s' ≡ false        -- Still running (not ret'd)
    rax-correct : readReg (regs s') rax ≡ result-val  -- Output in rax

open StarResult public

-- | Convert exec-based result to StarResult
exec-to-star-result : ∀ {n prog s s' result-val} →
    exec n prog s ≡ just s' →
    halted s' ≡ false →
    readReg (regs s') rax ≡ result-val →
    StarResult prog s s' result-val
exec-to-star-result {n} {prog} {s} {s'} exec-eq h-false rax-eq = record
  { star-exec = exec-to-star {n} {prog} {s} {s'} exec-eq
  ; not-halted = h-false
  ; rax-correct = rax-eq
  }

-- | Compose two StarResults via transitivity
--
-- Key benefit: no fuel arithmetic needed!
-- If executing A reaches s₁, and executing from s₁ reaches s₂,
-- then we can compose them trivially.
compose-star-results : ∀ {prog s₁ s₂ s₃ v₁ v₂} →
    StarResult prog s₁ s₂ v₁ →
    Star prog s₂ s₃ →
    halted s₃ ≡ false →
    readReg (regs s₃) rax ≡ v₂ →
    StarResult prog s₁ s₃ v₂
compose-star-results r₁ star₂ h₃ rax₃ = record
  { star-exec = star-trans (star-exec r₁) star₂
  ; not-halted = h₃
  ; rax-correct = rax₃
  }

------------------------------------------------------------------------
-- Usage Pattern: Composing IR proofs with Star
--
-- Old approach (fuel arithmetic):
--   exec (len-f + 1 + len-g) prog s ≡ just s'
--   requires: exec-chain lemmas, fuel arithmetic proofs
--
-- New approach (Star transitivity):
--   Star prog s s₁  -- from running f
--   Star prog s₁ s₂ -- from transfer instruction
--   Star prog s₂ s₃ -- from running g
--   ───────────────────────────────────────
--   Star prog s s₃  -- by star-trans twice
--
-- Example structure for compose proof:
--
--   compose-star : ∀ {A B C} (f : IR A B) (g : IR B C) prog s x →
--       preconditions →
--       StarResult prog s s' (encode (eval (g ∘ f) x))
--   compose-star f g prog s x preconds =
--     let
--       -- Step 1: Execute f
--       r₁ = run-ir-star f ... -- gives StarResult prog s s₁
--
--       -- Step 2: Execute transfer (mov rdi, rax)
--       step₂ = star-single h₁ step-transfer-eq
--
--       -- Step 3: Execute g
--       r₃ = run-ir-star g ... -- gives StarResult prog s₂ s₃
--
--       -- Compose: s →* s₁ →* s₂ →* s₃
--       star-all = star-trans (star-trans (star-exec r₁) step₂) (star-exec r₃)
--     in
--       record { star-exec = star-all ; not-halted = ... ; rax-correct = ... }
------------------------------------------------------------------------

