------------------------------------------------------------------------
-- Once.Backend.AArch64.Correct.Star
--
-- Star (reflexive-transitive closure) relation for AArch64 execution.
-- This provides a CompCert-style approach to chaining execution proofs
-- without fuel management or step counting.
--
-- Key benefit: composition is just transitivity (trivial chaining).
--
-- Ported from Once.Backend.X86.Correct.Star
------------------------------------------------------------------------

module Once.Backend.AArch64.Correct.Star where

open import Once.Backend.AArch64.Syntax
open import Once.Backend.AArch64.Semantics
open State

open import Data.Bool using (Bool; true; false)
open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≟_; _≤_; z≤n; s≤s) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (≤-trans; m≤m+n)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; inspect; [_])
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

-- | Chain 6 steps (useful for apply's 6 instructions)
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
-- Bridge Lemmas (PROVEN!)
--
-- These connect the fuel-based execution (exec) to Star.
-- exec checks `halted s` FIRST, so pattern matching on `halted s`
-- makes the goals reduce.
------------------------------------------------------------------------

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)

-- | Helper: when halted, step returns the state unchanged
step-halted : ∀ {prog s} → halted s ≡ true → step prog s ≡ just s
step-halted {prog} {s} h with halted s | h
... | true | refl = refl

-- | Helper: extract equality from just
just-injective : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-injective refl = refl

-- | Helper for exec-halted-id: relates exec result to step result
exec-step-halted : ∀ {n prog s s₁} →
  step prog s ≡ just s₁ →
  halted s₁ ≡ true →
  exec (suc n) prog s ≡ just s₁
exec-step-halted {n} {prog} {s} {s₁} step-eq h₁-eq
  with step prog s
exec-step-halted {n} {prog} {s} {s₁} refl h₁-eq | just .s₁
  with halted s₁ | h₁-eq
...   | true | refl = refl

-- | Helper: exec on halted state produces just s
exec-halted-id : ∀ {n prog s} → halted s ≡ true → exec n prog s ≡ just s
exec-halted-id {zero} _ = refl
exec-halted-id {suc n} {prog} {s} h-eq =
  exec-step-halted {n} {prog} {s} {s} (step-halted h-eq) h-eq

-- | If exec n succeeds, we have a star execution (PROVEN!)
-- Note: AArch64 exec structure is: step first, then check halted of result
-- Match follows exec's structure: step first, then halted of result
exec-to-star : ∀ {n prog s s'} →
               exec n prog s ≡ just s' →
               Star prog s s'
exec-to-star {zero} refl = refl*
exec-to-star {suc n} {prog} {s} {s'} eq
  with step prog s in step-eq
-- Step returns nothing: exec would be nothing, contradiction
exec-to-star {suc n} {prog} {s} {s'} () | nothing
-- Step returns just s₁
exec-to-star {suc n} {prog} {s} {s'} eq | just s₁
  with halted s₁ in h₁-eq
-- s₁ is halted: exec returns s₁
exec-to-star {suc n} {prog} {s} {.s₁} refl | just s₁ | true
  -- Need to show Star prog s s₁. Need to know if s was halted.
  -- If halted s = true, then step prog s = just s (definition of step),
  -- so s₁ = s and Star prog s s is refl*.
  -- If halted s = false, then step* h-eq step-eq refl*.
  = helper (halted s) refl
  where
    helper : (h : Bool) → halted s ≡ h → Star prog s s₁
    helper true h-eq =
      -- halted s = true, so step prog s = just s, hence s₁ = s
      let s₁≡s = just-injective (trans (sym step-eq) (step-halted h-eq))
      in subst (Star prog s) (sym s₁≡s) refl*
    helper false h-eq = step* h-eq step-eq refl*
-- s₁ not halted: recurse
exec-to-star {suc n} {prog} {s} {s'} eq | just s₁ | false
  = helper (halted s) refl
  where
    helper : (h : Bool) → halted s ≡ h → Star prog s s'
    helper true h-eq =
      -- halted s = true, so step prog s = just s, hence s₁ = s
      -- But halted s₁ = false and halted s = true means s ≢ s₁, contradiction
      let s₁≡s = just-injective (trans (sym step-eq) (step-halted h-eq))
          h₁-should-be-true = trans (cong halted s₁≡s) h-eq
      in ⊥-elim (Bool-true≢false (trans (sym h₁-should-be-true) h₁-eq))
      where
        Bool-true≢false : true ≡ false → ⊥
        Bool-true≢false ()
    helper false h-eq = step* h-eq step-eq (exec-to-star {n} {prog} {s₁} {s'} eq)

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

-- | Result of executing IR code with Star semantics
-- Note: Uses x0 as result register (AArch64 calling convention)
record StarResult (prog : Program) (s s' : State) (result-val : Word) : Set where
  field
    star-exec   : Star prog s s'           -- Execution reaches s'
    not-halted  : halted s' ≡ false        -- Still running (not ret'd)
    x0-correct  : readReg (regs s') x0 ≡ result-val  -- Output in x0

open StarResult public

-- | Convert exec-based result to StarResult
exec-to-star-result : ∀ {n prog s s' result-val} →
    exec n prog s ≡ just s' →
    halted s' ≡ false →
    readReg (regs s') x0 ≡ result-val →
    StarResult prog s s' result-val
exec-to-star-result {n} {prog} {s} {s'} exec-eq h-false x0-eq = record
  { star-exec = exec-to-star {n} {prog} {s} {s'} exec-eq
  ; not-halted = h-false
  ; x0-correct = x0-eq
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
    readReg (regs s₃) x0 ≡ v₂ →
    StarResult prog s₁ s₃ v₂
compose-star-results r₁ star₂ h₃ x0₃ = record
  { star-exec = star-trans (star-exec r₁) star₂
  ; not-halted = h₃
  ; x0-correct = x0₃
  }

------------------------------------------------------------------------
-- Reverse Bridge: Star to exec (PROVEN!)
--
-- Convert Star execution back to fuel-based exec.
-- Used at final theorem boundaries when we need exec for extraction.
------------------------------------------------------------------------

-- | Helper: Star from halted state must be reflexive
star-halted-refl : ∀ {prog s s'} →
                   Star prog s s' →
                   halted s ≡ true →
                   s ≡ s'
star-halted-refl refl* _ = refl
star-halted-refl (step* h-false _ _) h-true with () ← trans (sym h-true) h-false

-- | Count steps in a Star (determines fuel needed)
star-length : ∀ {prog s s'} → Star prog s s' → ℕ
star-length refl* = 0
star-length (step* _ _ rest) = suc (star-length rest)

-- | Helper: if exec succeeds on a halted state, it returns that state
exec-on-halted : ∀ {n prog s s'} →
                 halted s ≡ true →
                 exec n prog s ≡ just s' →
                 s ≡ s'
exec-on-halted {zero} h refl = refl
exec-on-halted {suc n} {prog} {s} {s'} h eq =
  just-injective (trans (sym (exec-halted-id h)) eq)

-- | Helper: exec on halted state returns that state unchanged
exec-n-halted : ∀ (m : ℕ) (prog : Program) (s : State) →
                halted s ≡ true →
                exec m prog s ≡ just s
exec-n-halted m prog s h = exec-halted-id {m} {prog} {s} h

-- | Helper: exec respects step when not halted
-- Proves that if step prog s = just s₁ and exec n prog s₁ = just s',
-- then exec (suc n) prog s = just s'
exec-step-helper : ∀ {n prog s s₁ s'} →
                   halted s ≡ false →
                   step prog s ≡ just s₁ →
                   exec n prog s₁ ≡ just s' →
                   exec (suc n) prog s ≡ just s'
exec-step-helper {n} {prog} {s} {s₁} {s'} h-false step-eq rec
  with step prog s in step-eq'
-- step returned nothing: contradiction with step-eq
exec-step-helper {n} {prog} {s} {s₁} {s'} h-false () rec | nothing
-- step returned just s₁
exec-step-helper {n} {prog} {s} {s₁} {s'} h-false refl rec | just .s₁
  with halted s₁ in h₁-eq
-- s₁ halted: exec (suc n) prog s reduces to just s₁
-- Need to show just s₁ ≡ just s', which comes from rec showing s₁ ≡ s'
...   | true = trans (sym (exec-halted-id {n} {prog} {s₁} h₁-eq)) rec
-- s₁ not halted: exec continues with s₁
...   | false = rec

-- | Convert Star to exec with computed fuel
star-to-exec : ∀ {prog s s'} →
               (star : Star prog s s') →
               halted s' ≡ true →
               exec (star-length star) prog s ≡ just s'
star-to-exec refl* h-final = refl
star-to-exec (step* {s' = s₁} h-false step-eq rest) h-final =
  exec-step-helper h-false step-eq (star-to-exec rest h-final)

-- | Existential version: returns the fuel needed
star-to-exec-∃ : ∀ {prog s s'} →
                 Star prog s s' →
                 halted s' ≡ true →
                 ∃[ n ] exec n prog s ≡ just s'
star-to-exec-∃ star h-final = star-length star , star-to-exec star h-final

------------------------------------------------------------------------
-- Star chaining with non-halted intermediate state
------------------------------------------------------------------------

-- | Chain Star with additional exec when intermediate state is not halted
star-to-exec-chain : ∀ {prog s s' s''} →
  (star : Star prog s s') →
  halted s' ≡ false →
  (m : ℕ) →
  exec m prog s' ≡ just s'' →
  exec (star-length star +ℕ m) prog s ≡ just s''
star-to-exec-chain refl* h-false m exec-m = exec-m
star-to-exec-chain (step* {s' = s₁} h-false-s step-eq rest) h-false m exec-m =
  exec-step-helper h-false-s step-eq (star-to-exec-chain rest h-false m exec-m)
