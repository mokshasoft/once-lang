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
-- Import Common Star Infrastructure
------------------------------------------------------------------------

-- Import the common Star definition and properties.
-- This includes: Star data type, star-trans, star-single, infix operators,
-- helper combinators (star-step2 through star-step6), and _⟶*_ notation.
-- Eliminates ~120 lines of duplicate code.
open import Once.Backend.Common.Star Program State halted step public

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
