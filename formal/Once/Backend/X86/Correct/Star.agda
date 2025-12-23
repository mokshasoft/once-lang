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

------------------------------------------------------------------------
-- Bridge Lemmas (PROVEN!)
--
-- These connect the fuel-based execution (exec, exec-until-pc) to Star.
-- Both exec and exec-until-pc check `halted s` FIRST, so pattern matching
-- on `halted s` makes the goals reduce.
------------------------------------------------------------------------

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)

-- | If exec n succeeds, we have a star execution (PROVEN!)
exec-to-star : ∀ {n prog s s'} →
               exec n prog s ≡ just s' →
               Star prog s s'
exec-to-star {zero} refl = refl*
exec-to-star {suc n} {prog} {s} {s'} eq with halted s | inspect halted s
exec-to-star {suc n} {prog} {s} {.s} refl | true | _ = refl*
exec-to-star {suc n} {prog} {s} {s'} eq | false | [ h-eq ]
  with step prog s | inspect (step prog) s
exec-to-star {suc n} {prog} {s} {s'} () | false | _ | nothing | _
exec-to-star {suc n} {prog} {s} {s'} eq | false | [ h-eq ] | just s₁ | [ step-eq ]
  with halted s₁ | inspect halted s₁
exec-to-star {suc n} {prog} {s} {.s₁} refl | false | [ h-eq ] | just s₁ | [ step-eq ] | true | _
  = step* h-eq step-eq refl*
exec-to-star {suc n} {prog} {s} {s'} eq | false | [ h-eq ] | just s₁ | [ step-eq ] | false | _
  = step* h-eq step-eq (exec-to-star {n} {prog} {s₁} {s'} eq)

-- | If exec-until-pc succeeds, we have a star execution (PROVEN!)
exec-until-pc-to-star : ∀ {target fuel prog s s'} →
                        exec-until-pc target fuel prog s ≡ just s' →
                        Star prog s s'
exec-until-pc-to-star {target} {zero} refl = refl*
exec-until-pc-to-star {target} {suc fuel} {prog} {s} {s'} eq
  with halted s | inspect halted s
exec-until-pc-to-star {target} {suc fuel} {prog} {s} {.s} refl | true | _ = refl*
exec-until-pc-to-star {target} {suc fuel} {prog} {s} {s'} eq | false | [ h-eq ]
  with pc s ≟ target
exec-until-pc-to-star {target} {suc fuel} {prog} {s} {.s} refl | false | _ | yes _ = refl*
exec-until-pc-to-star {target} {suc fuel} {prog} {s} {s'} eq | false | [ h-eq ] | no _
  with step prog s | inspect (step prog) s
exec-until-pc-to-star {target} {suc fuel} {prog} {s} {s'} () | false | _ | no _ | nothing | _
exec-until-pc-to-star {target} {suc fuel} {prog} {s} {s'} eq | false | [ h-eq ] | no _ | just s₁ | [ step-eq ]
  = step* h-eq step-eq (exec-until-pc-to-star {target} {fuel} {prog} {s₁} {s'} eq)

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

-- | Helper: extract equality from just
just-injective : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-injective refl = refl

-- | Helper: if exec succeeds on a halted state, it returns that state
exec-on-halted : ∀ {n prog s s'} →
                 halted s ≡ true →
                 exec n prog s ≡ just s' →
                 s ≡ s'
exec-on-halted {zero} h refl = refl
exec-on-halted {suc n} {prog} {s} {s'} h eq with halted s | h
... | true | refl = just-injective eq

-- | Helper: exec on halted state returns that state unchanged
exec-n-halted : ∀ (m : ℕ) (prog : Program) (s : State) →
                halted s ≡ true →
                exec m prog s ≡ just s
exec-n-halted zero _ s _ = refl
exec-n-halted (suc m) prog s h with halted s | h
... | true | refl = refl

-- | Helper: step on non-halted state equals step-not-halted
step-on-non-halted : ∀ {prog s} →
                     halted s ≡ false →
                     step prog s ≡ step-not-halted prog s
step-on-non-halted {prog} {s} h-false with halted s | h-false
... | false | refl = refl

-- | Helper: exec respects step when not halted
-- This lemma captures the key property: if halted s = false and step prog s = just s₁,
-- then exec (suc n) prog s follows from exec n prog s₁.
--
-- PROVEN: Using rewrite to reduce exec (suc n) to exec n after step.
exec-step-helper : ∀ {n prog s s₁ s'} →
                   halted s ≡ false →
                   step prog s ≡ just s₁ →
                   exec n prog s₁ ≡ just s' →
                   exec (suc n) prog s ≡ just s'
exec-step-helper {n} {prog} {s} {s₁} {s'} h-false step-eq rec
  rewrite h-false | step-on-non-halted {prog} {s} h-false | step-eq
  with halted s₁ | inspect halted s₁
... | true  | [ h₁-true ] = trans (sym (exec-n-halted n prog s₁ h₁-true)) rec
... | false | _ = rec

-- | Helper: Star execution with extra fuel still reaches halted state
star-to-exec-extend : ∀ {prog s s'} (star : Star prog s s') (m : ℕ) →
  halted s' ≡ true →
  exec (star-length star +ℕ m) prog s ≡ just s'
star-to-exec-extend refl* m halt-eq = exec-n-halted m _ _ halt-eq
star-to-exec-extend (step* {s' = s₁} h-false step-eq rest) m halt-eq =
  exec-step-helper h-false step-eq (star-to-exec-extend rest m halt-eq)

-- | Once halted, more fuel doesn't change result
-- PROVEN: Convert to Star, then use star-to-exec-extend.
exec-halted-extend : ∀ (n m : ℕ) (prog : List Instr) (s s' : State) →
  exec n prog s ≡ just s' →
  halted s' ≡ true →
  exec (n +ℕ m) prog s ≡ just s'
exec-halted-extend n m prog s s' exec-eq halt-eq =
  star-to-exec-ge star (n +ℕ m) halt-eq le
  where
    star : Star prog s s'
    star = exec-to-star {n} {prog} {s} {s'} exec-eq

    -- Execute with at least star-length fuel reaches s'
    star-to-exec-ge : ∀ {prog₁ s₁ s₁'} (star₁ : Star prog₁ s₁ s₁') (k : ℕ) →
                      halted s₁' ≡ true →
                      star-length star₁ ≤ k →
                      exec k prog₁ s₁ ≡ just s₁'
    star-to-exec-ge refl* k halt-eq₁ _ = exec-n-halted k _ _ halt-eq₁
    star-to-exec-ge (step* {s' = s₂} h-false step-eq₁ rest) (suc k) halt-eq₁ (s≤s le₁) =
      exec-step-helper h-false step-eq₁ (star-to-exec-ge rest k halt-eq₁ le₁)
    star-to-exec-ge (step* _ _ _) zero _ ()

    -- star-length (exec-to-star exec-eq) ≤ n
    star-length-le-exec : ∀ {n₁ prog₁ s₁ s₁'} (eq : exec n₁ prog₁ s₁ ≡ just s₁') →
                          star-length (exec-to-star {n₁} {prog₁} {s₁} {s₁'} eq) ≤ n₁
    star-length-le-exec {zero} refl = z≤n
    star-length-le-exec {suc n₁} {prog₁} {s₁} eq with halted s₁ | inspect halted s₁
    star-length-le-exec {suc n₁} refl | true | _ = z≤n
    star-length-le-exec {suc n₁} {prog₁} {s₁} eq | false | [ h-eq ]
      with step prog₁ s₁ | inspect (step prog₁) s₁
    star-length-le-exec {suc n₁} () | false | _ | nothing | _
    star-length-le-exec {suc n₁} {prog₁} {s₁} eq | false | [ h-eq ] | just s₂ | [ step-eq₁ ]
      with halted s₂ | inspect halted s₂
    star-length-le-exec {suc n₁} refl | false | _ | just s₂ | _ | true | _ = s≤s z≤n
    star-length-le-exec {suc n₁} {prog₁} {s₁} eq | false | _ | just s₂ | _ | false | _ =
      s≤s (star-length-le-exec {n₁} eq)

    le : star-length star ≤ n +ℕ m
    le = ≤-trans (star-length-le-exec exec-eq) (m≤m+n n m)

-- | Convert Star to exec with computed fuel
-- PROVEN: Using exec-step-helper to handle the with abstraction.
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

