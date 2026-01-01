------------------------------------------------------------------------
-- Once.Backend.RiscV64.Correct.Star
--
-- Star (reflexive-transitive closure) relation for RISC-V 64-bit execution.
-- This provides a CompCert-style approach to chaining execution proofs
-- without fuel management or step counting.
--
-- Key benefit: composition is just transitivity (trivial chaining).
--
-- Adapted from x86-64 backend.
------------------------------------------------------------------------

{-# OPTIONS --sized-types #-}

module Once.Backend.RiscV64.Correct.Star where

open import Size

open import Once.Backend.RiscV64.Syntax
open import Once.Backend.RiscV64.Semantics
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
open import Once.Backend.Common.Star Program State halted step public

------------------------------------------------------------------------
-- RISC-V64-Specific Bridge Lemmas
--
-- These connect the fuel-based execution (exec, exec-until-pc) to Star.
-- Both exec and exec-until-pc check `halted s` FIRST, so pattern matching
-- on `halted s` makes the goals reduce.
------------------------------------------------------------------------

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)

-- | Helper: extract equality from just (used in bridge lemmas)
just-injective : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-injective refl = refl

-- | Helper: step on halted state returns that state
-- Uses rewrite to avoid with-clause conflicts
step-on-halted : ∀ (prog : Program) (s : State) →
                 halted s ≡ true →
                 step prog s ≡ just s
step-on-halted prog s h rewrite h = refl

-- | Helper: derive s₁ ≡ s from step-eq and halted proof
-- Uses auxiliary function with explicit Bool pattern to avoid with-clause issues
step-halted-eq : ∀ {prog s s₁} →
                 halted s ≡ true →
                 step prog s ≡ just s₁ →
                 s₁ ≡ s
step-halted-eq {prog} {s} {s₁} h-eq step-eq =
  step-halted-eq-aux (halted s) refl step-eq
  where
    step-halted-eq-aux : ∀ (b : Bool) → halted s ≡ b → step prog s ≡ just s₁ → s₁ ≡ s
    step-halted-eq-aux true h-eq' step-eq' rewrite h-eq' = sym (just-injective step-eq')
    step-halted-eq-aux false h-eq' _ with () ← trans (sym h-eq') h-eq

-- | Helper: When step succeeds and result halted, construct Star
-- This avoids nested with-clause issues in exec-to-star
exec-to-star-step-halted : ∀ {prog s s₁} →
  step prog s ≡ just s₁ →
  halted s₁ ≡ true →
  Star prog s s₁
exec-to-star-step-halted {prog} {s} {s₁} step-eq h₁-eq =
  exec-to-star-step-halted-aux (halted s) refl step-eq h₁-eq
  where
    exec-to-star-step-halted-aux : ∀ (b : Bool) → halted s ≡ b →
      step prog s ≡ just s₁ → halted s₁ ≡ true → Star prog s s₁
    exec-to-star-step-halted-aux true h-eq step-eq' h₁-eq'
      rewrite h-eq = subst (Star prog s) (just-injective step-eq') refl*
    exec-to-star-step-halted-aux false h-eq step-eq' h₁-eq' =
      step* h-eq step-eq' refl*

-- | If exec n succeeds, we have a star execution
exec-to-star : ∀ {n prog s s'} →
               exec n prog s ≡ just s' →
               Star prog s s'
exec-to-star {zero} refl = refl*
exec-to-star {suc n} {prog} {s} {s'} eq with step prog s | inspect (step prog) s
exec-to-star {suc n} {prog} {s} {s'} () | nothing | _
exec-to-star {suc n} {prog} {s} {s'} eq | just s₁ | [ step-eq ]
  with halted s₁ | inspect halted s₁
-- Case: halted s₁ = true → exec returns s₁
exec-to-star {suc n} {prog} {s} {.s₁} refl | just s₁ | [ step-eq ] | true | [ h₁-eq ]
  = exec-to-star-step-halted step-eq h₁-eq
-- Case: halted s₁ = false → continue execution
exec-to-star {suc n} {prog} {s} {s'} eq | just s₁ | [ step-eq ] | false | [ h₁-eq ]
  = exec-to-star-continue (halted s) refl eq step-eq h₁-eq
  where
    -- Helper to avoid nested with-clause type refinement issues
    exec-to-star-continue : ∀ (b : Bool) → halted s ≡ b →
      exec n prog s₁ ≡ just s' →
      step prog s ≡ just s₁ →
      halted s₁ ≡ false →
      Star prog s s'
    exec-to-star-continue true h-eq _ step-eq' h₁-false rewrite h-eq =
      -- step prog s ≡ just s (after rewrite), and step-eq' : just s ≡ just s₁
      -- So s₁ ≡ s, and halted s₁ ≡ halted s ≡ true, contradicting h₁-false
      let s₁≡s = sym (just-injective step-eq')
          halted-s₁-true : halted s₁ ≡ true
          halted-s₁-true = trans (cong halted s₁≡s) h-eq
          absurd : true ≡ false
          absurd = trans (sym halted-s₁-true) h₁-false
      in ⊥-elim (true≢false absurd)
        where
          true≢false : true ≡ false → ⊥
          true≢false ()
    exec-to-star-continue false h-eq rec-eq step-eq' h₁-false =
      step* h-eq step-eq' (exec-to-star {n} {prog} {s₁} {s'} rec-eq)

-- | If exec-until-pc succeeds, we have a star execution
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
-- StarResult: Execution result with Star instead of exec
--
-- This record captures the properties of successful IR execution
-- in a Star-friendly way, enabling trivial composition via star-trans.
--
-- Note: RISC-V uses a0 for both input and output (unlike x86's rdi/rax)
------------------------------------------------------------------------

open import Data.Nat using (_+_; _>_)

-- | Result of executing IR code with Star semantics
record StarResult (prog : Program) (s s' : State) (result-val : Word) : Set where
  field
    star-exec   : Star prog s s'           -- Execution reaches s'
    not-halted  : halted s' ≡ false        -- Still running (not halted)
    a0-correct  : readReg (regs s') a0 ≡ result-val  -- Output in a0

open StarResult public

-- | Convert exec-based result to StarResult
exec-to-star-result : ∀ {n prog s s' result-val} →
    exec n prog s ≡ just s' →
    halted s' ≡ false →
    readReg (regs s') a0 ≡ result-val →
    StarResult prog s s' result-val
exec-to-star-result {n} {prog} {s} {s'} exec-eq h-false a0-eq = record
  { star-exec = exec-to-star {n} {prog} {s} {s'} exec-eq
  ; not-halted = h-false
  ; a0-correct = a0-eq
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
    readReg (regs s₃) a0 ≡ v₂ →
    StarResult prog s₁ s₃ v₂
compose-star-results r₁ star₂ h₃ a0₃ = record
  { star-exec = star-trans (star-exec r₁) star₂
  ; not-halted = h₃
  ; a0-correct = a0₃
  }

------------------------------------------------------------------------
-- Reverse Bridge: Star to exec
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

-- | Star-length is additive under star-trans
star-length-trans : ∀ {prog s₁ s₂ s₃}
                    (p₁ : Star prog s₁ s₂) (p₂ : Star prog s₂ s₃) →
                    star-length (star-trans p₁ p₂) ≡ star-length p₁ +ℕ star-length p₂
star-length-trans refl* p₂ = refl
star-length-trans (step* h step-eq rest) p₂ = cong suc (star-length-trans rest p₂)

-- | Helper: if exec succeeds on a halted state, it returns that state
exec-on-halted : ∀ {n prog s s'} →
                 halted s ≡ true →
                 exec n prog s ≡ just s' →
                 s ≡ s'
exec-on-halted {zero} h refl = refl
exec-on-halted {suc n} {prog} {s} {s'} h eq
  rewrite step-on-halted prog s h | h = just-injective eq

-- | Helper: exec on halted state returns that state unchanged
exec-n-halted : ∀ (m : ℕ) (prog : Program) (s : State) →
                halted s ≡ true →
                exec m prog s ≡ just s
exec-n-halted zero _ s _ = refl
exec-n-halted (suc m) prog s h
  rewrite step-on-halted prog s h | h = refl

-- | Helper: exec respects step when step returns just
-- RISC-V semantics: exec (suc n) steps once, checks halted, recurses if false
exec-step-helper : ∀ {n prog s s₁ s'} →
                   halted s ≡ false →
                   step prog s ≡ just s₁ →
                   exec n prog s₁ ≡ just s' →
                   exec (suc n) prog s ≡ just s'
exec-step-helper {n} {prog} {s} {s₁} {s'} h-false step-eq rec
  with step prog s | step-eq
... | just .s₁ | refl with halted s₁ | inspect halted s₁
...   | true  | [ h₁-true ] = trans (sym (exec-n-halted n prog s₁ h₁-true)) rec
...   | false | _ = rec

-- | General helper: exec respects step regardless of halted s
exec-step-helper-gen : ∀ {n prog s s₁ s'} →
                       step prog s ≡ just s₁ →
                       exec n prog s₁ ≡ just s' →
                       exec (suc n) prog s ≡ just s'
exec-step-helper-gen {n} {prog} {s} {s₁} {s'} step-eq rec
  with step prog s | step-eq
... | just .s₁ | refl with halted s₁ | inspect halted s₁
...   | true  | [ h₁-true ] = trans (sym (exec-n-halted n prog s₁ h₁-true)) rec
...   | false | _ = rec

-- | Helper: Star execution with extra fuel still reaches halted state
star-to-exec-extend : ∀ {prog s s'} (star : Star prog s s') (m : ℕ) →
  halted s' ≡ true →
  exec (star-length star +ℕ m) prog s ≡ just s'
star-to-exec-extend refl* m halt-eq = exec-n-halted m _ _ halt-eq
star-to-exec-extend (step* {s' = s₁} h-false step-eq rest) m halt-eq =
  exec-step-helper h-false step-eq (star-to-exec-extend rest m halt-eq)

-- | Execute with at least star-length fuel reaches s'
star-to-exec-ge : ∀ {prog₁ s₁ s₁'} (star₁ : Star prog₁ s₁ s₁') (k : ℕ) →
                  halted s₁' ≡ true →
                  star-length star₁ ≤ k →
                  exec k prog₁ s₁ ≡ just s₁'
star-to-exec-ge refl* k halt-eq₁ _ = exec-n-halted k _ _ halt-eq₁
star-to-exec-ge (step* {s' = s₂} h-false step-eq₁ rest) (suc k) halt-eq₁ (s≤s le₁) =
  exec-step-helper h-false step-eq₁ (star-to-exec-ge rest k halt-eq₁ le₁)
star-to-exec-ge (step* _ _ _) zero _ ()

-- | Once halted, more fuel doesn't change result
-- Proved directly by induction on n (avoids Star with-abstraction issues)
exec-halted-extend : ∀ (n m : ℕ) (prog : List Instr) (s s' : State) →
  exec n prog s ≡ just s' →
  halted s' ≡ true →
  exec (n +ℕ m) prog s ≡ just s'
exec-halted-extend zero m prog s s' refl halt-eq = exec-n-halted m prog s halt-eq
exec-halted-extend (suc n) m prog s s' exec-eq halt-eq with step prog s | inspect (step prog) s
... | nothing | _ with () ← exec-eq  -- exec would return nothing
... | just s₁ | [ step-eq ] with halted s₁ | inspect halted s₁
-- Case: halted s₁ = true, so exec returns s₁ immediately
-- Need to show: exec (suc (n+m)) prog s ≡ just s'
-- In this context: step prog s = just s₁, halted s₁ = true
-- So exec (suc (n+m)) prog s = exec (n+m) prog s₁ = just s₁ = just s'
...   | true | [ h₁-eq ] =
  let s₁≡s' = just-injective exec-eq
      rec = exec-n-halted (n +ℕ m) prog s₁ h₁-eq
      rec' = subst (λ x → exec (n +ℕ m) prog s₁ ≡ just x) s₁≡s' rec
  in trans (sym (exec-n-halted (n +ℕ m) prog s₁ h₁-eq)) rec'
-- Case: halted s₁ = false, so exec continues recursively
...   | false | [ h₁-eq ] = exec-halted-extend n m prog s₁ s' exec-eq halt-eq

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
--
-- Key lemma for exec-chain: if Star reaches s' (not halted),
-- and exec m from s' reaches s'', then exec (star-length + m) reaches s''.
------------------------------------------------------------------------

-- | Chain Star with additional exec when intermediate state is not halted
-- This is the core lemma that enables exec-chain via Star.
star-to-exec-chain : ∀ {prog s s' s''} →
  (star : Star prog s s') →
  halted s' ≡ false →
  (m : ℕ) →
  exec m prog s' ≡ just s'' →
  exec (star-length star +ℕ m) prog s ≡ just s''
star-to-exec-chain refl* h-false m exec-m = exec-m
star-to-exec-chain (step* {s' = s₁} h-false-s step-eq rest) h-false m exec-m =
  exec-step-helper h-false-s step-eq (star-to-exec-chain rest h-false m exec-m)

------------------------------------------------------------------------
-- Usage Pattern: Composing IR proofs with Star
--
-- Old approach (fuel arithmetic):
--   exec (len-f + len-g) prog s ≡ just s'
--   requires: exec-chain lemmas, fuel arithmetic proofs
--
-- New approach (Star transitivity):
--   Star prog s s₁  -- from running f
--   Star prog s₁ s₂ -- from running g (RISC-V: no transfer needed!)
--   ───────────────────────────────────────
--   Star prog s s₂  -- by star-trans
--
-- Note: Unlike x86-64, RISC-V uses a0 for BOTH input and output,
-- so compose doesn't need a transfer instruction between f and g!
------------------------------------------------------------------------
