------------------------------------------------------------------------
-- Once.Backend.X86.Correct.SequenceHelpers
--
-- Sequence execution helpers for x86-64 code generation correctness proofs.
-- Contains: exec lemmas, chaining lemmas, non-halting subprogram execution,
-- and complex setup/middle/final helpers for pair, case, etc.
--
-- Depends on Foundation. Used by MutualRecursion.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.SequenceHelpers where

-- Re-export Foundation
open import Once.Backend.X86.Correct.Foundation public

open import Once.Type
open import Once.IR
open import Once.Semantics

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State
open Once.Backend.X86.Semantics.Flags
open import Once.Backend.X86.CodeGen

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _∸_; _≡ᵇ_; _<_; _≤_; s≤s; z≤n) renaming (_+_ to _+ℕ_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-sum)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans; subst; subst₂; module ≡-Reasoning; inspect) renaming ([_] to ⟦_⟧ᵢ)
open ≡-Reasoning

open import Data.Nat.Properties using (≡ᵇ⇒≡; ≡⇒≡ᵇ; +-comm; +-assoc; +-identityʳ; m+[n∸m]≡n; ∸-+-assoc)

------------------------------------------------------------------------
-- Exec Lemmas
------------------------------------------------------------------------

-- | Exec returns immediately when step returns halted state
exec-on-halted-step : ∀ (n : ℕ) (prog : List Instr) (s s' : State) →
  step prog s ≡ just s' →
  halted s' ≡ true →
  exec (suc n) prog s ≡ just s'
exec-on-halted-step n prog s s' step-eq halt-eq with step prog s
exec-on-halted-step n prog s s' refl halt-eq | just .s' with halted s'
exec-on-halted-step n prog s s' refl refl | just .s' | true = refl

-- | Exec continues recursively when step returns non-halted state
exec-on-non-halted-step : ∀ (n : ℕ) (prog : List Instr) (s s' : State) →
  step prog s ≡ just s' →
  halted s' ≡ false →
  exec (suc n) prog s ≡ exec n prog s'
exec-on-non-halted-step n prog s s' step-eq halt-eq with step prog s
exec-on-non-halted-step n prog s s' refl halt-eq | just .s' with halted s'
exec-on-non-halted-step n prog s s' refl refl | just .s' | false = refl

-- | Single-step non-halting execution: execute exactly 1 step without halting
-- Key lemma for sub-program execution where we don't want to halt
exec-one-step-nonhalt : ∀ (prog : List Instr) (s s' : State) →
  step prog s ≡ just s' →
  halted s' ≡ false →
  exec 1 prog s ≡ just s'
exec-one-step-nonhalt prog s s' step-eq halt-eq =
  trans (exec-on-non-halted-step 0 prog s s' step-eq halt-eq) refl

-- | Single-step execution: execute exactly 1 step (works for both halted and non-halted results)
-- This is the general version that doesn't require halted s' ≡ false
exec-one-step : ∀ (prog : List Instr) (s s' : State) →
  step prog s ≡ just s' →
  exec 1 prog s ≡ just s'
exec-one-step prog s s' step-eq with step prog s
... | nothing with () ← step-eq
exec-one-step prog s s' step-eq | just s1 with halted s1 | step-eq
... | true | refl = refl
... | false | refl = refl

-- | Two-step non-halting execution: execute exactly 2 steps without halting
exec-two-steps-nonhalt : ∀ (prog : List Instr) (s s1 s2 : State) →
  step prog s ≡ just s1 →
  halted s1 ≡ false →
  step prog s1 ≡ just s2 →
  halted s2 ≡ false →
  exec 2 prog s ≡ just s2
exec-two-steps-nonhalt prog s s1 s2 step1 h1 step2 h2 =
  trans (exec-on-non-halted-step 1 prog s s1 step1 h1)
        (exec-one-step-nonhalt prog s1 s2 step2 h2)

-- | Three-step non-halting execution
exec-three-steps-nonhalt : ∀ (prog : List Instr) (s s1 s2 s3 : State) →
  step prog s ≡ just s1 → halted s1 ≡ false →
  step prog s1 ≡ just s2 → halted s2 ≡ false →
  step prog s2 ≡ just s3 → halted s3 ≡ false →
  exec 3 prog s ≡ just s3
exec-three-steps-nonhalt prog s s1 s2 s3 step1 h1 step2 h2 step3 h3 =
  trans (exec-on-non-halted-step 2 prog s s1 step1 h1)
        (exec-two-steps-nonhalt prog s1 s2 s3 step2 h2 step3 h3)

exec-four-steps-nonhalt : ∀ (prog : List Instr) (s s1 s2 s3 s4 : State) →
  step prog s ≡ just s1 → halted s1 ≡ false →
  step prog s1 ≡ just s2 → halted s2 ≡ false →
  step prog s2 ≡ just s3 → halted s3 ≡ false →
  step prog s3 ≡ just s4 → halted s4 ≡ false →
  exec 4 prog s ≡ just s4
exec-four-steps-nonhalt prog s s1 s2 s3 s4 step1 h1 step2 h2 step3 h3 step4 h4 =
  trans (exec-on-non-halted-step 3 prog s s1 step1 h1)
        (exec-three-steps-nonhalt prog s1 s2 s3 s4 step2 h2 step3 h3 step4 h4)

exec-five-steps-nonhalt : ∀ (prog : List Instr) (s s1 s2 s3 s4 s5 : State) →
  step prog s ≡ just s1 → halted s1 ≡ false →
  step prog s1 ≡ just s2 → halted s2 ≡ false →
  step prog s2 ≡ just s3 → halted s3 ≡ false →
  step prog s3 ≡ just s4 → halted s4 ≡ false →
  step prog s4 ≡ just s5 → halted s5 ≡ false →
  exec 5 prog s ≡ just s5
exec-five-steps-nonhalt prog s s1 s2 s3 s4 s5 step1 h1 step2 h2 step3 h3 step4 h4 step5 h5 =
  trans (exec-on-non-halted-step 4 prog s s1 step1 h1)
        (exec-four-steps-nonhalt prog s1 s2 s3 s4 s5 step2 h2 step3 h3 step4 h4 step5 h5)

------------------------------------------------------------------------
-- Non-halting sub-program execution (for compose proofs)
-- These execute IR code within a larger program without requiring halt
------------------------------------------------------------------------

-- | Execute id in a larger program (non-halting)
-- compile-x86 id = [mov rax, rdi]
-- After 1 step: pc=1, rax=encode x, halted=false
run-id-nonhalt : ∀ {A} (rest : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) rdi ≡ encode x →
  ∃[ s' ] (exec 1 (compile-x86 {A} {A} id ++ rest) s ≡ just s'
         × halted s' ≡ false
         × pc s' ≡ 1
         × readReg (regs s') rax ≡ encode x)
run-id-nonhalt {A} rest x s h-false pc-0 rdi-eq = s' , exec-eq , h' , pc' , rax-eq
  where
    prog : Program
    prog = compile-x86 {A} {A} id ++ rest

    -- State after mov rax, rdi
    s' : State
    s' = record s { regs = writeReg (regs s) rax (readReg (regs s) rdi)
                  ; pc = pc s +ℕ 1 }

    -- Step proof
    step-eq : step prog s ≡ just s'
    step-eq = trans (step-exec-0 (mov (reg rax) (reg rdi)) rest s h-false pc-0)
                    (execMov-reg-reg s rax rdi)

    h' : halted s' ≡ false
    h' = h-false

    pc' : pc s' ≡ 1
    pc' = cong (λ p → p +ℕ 1) pc-0

    exec-eq : exec 1 prog s ≡ just s'
    exec-eq = exec-one-step-nonhalt prog s s' step-eq h'

    rax-eq : readReg (regs s') rax ≡ encode x
    rax-eq = trans (readReg-writeReg-same (regs s) rax (readReg (regs s) rdi)) rdi-eq

-- | Execute terminal in a larger program (non-halting)
-- compile-x86 terminal = [mov rax, 0]
-- After 1 step: pc=1, rax=0=encode tt, halted=false
run-terminal-nonhalt : ∀ {A} (rest : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  ∃[ s' ] (exec 1 (compile-x86 {A} {Unit} terminal ++ rest) s ≡ just s'
         × halted s' ≡ false
         × pc s' ≡ 1
         × readReg (regs s') rax ≡ encode {Unit} tt)
run-terminal-nonhalt {A} rest x s h-false pc-0 = s' , exec-eq , h' , pc' , rax-eq
  where
    prog : Program
    prog = compile-x86 {A} {Unit} terminal ++ rest

    s' : State
    s' = record s { regs = writeReg (regs s) rax 0
                  ; pc = pc s +ℕ 1 }

    step-eq : step prog s ≡ just s'
    step-eq = trans (step-exec-0 (mov (reg rax) (imm 0)) rest s h-false pc-0)
                    (execMov-reg-imm s rax 0)

    h' : halted s' ≡ false
    h' = h-false

    pc' : pc s' ≡ 1
    pc' = cong (λ p → p +ℕ 1) pc-0

    exec-eq : exec 1 prog s ≡ just s'
    exec-eq = exec-one-step-nonhalt prog s s' step-eq h'

    rax-eq : readReg (regs s') rax ≡ encode tt
    rax-eq = trans (readReg-writeReg-same (regs s) rax 0) (sym encode-unit)

-- | Helper: true ≡ false is absurd
true≢false : true ≡ false → ⊥
true≢false ()

-- | Exec chaining: if exec n produces s' (not halted), then exec m on s' produces s'',
-- then exec (n + m) produces s''
-- This is key for composing sub-program executions
-- Proof by induction on n
exec-chain : ∀ (n m : ℕ) (prog : List Instr) (s s' s'' : State) →
  exec n prog s ≡ just s' →
  halted s' ≡ false →
  exec m prog s' ≡ just s'' →
  exec (n +ℕ m) prog s ≡ just s''
-- Base case: n=0, so exec 0 prog s = just s, thus s' = s
exec-chain zero m prog s .s s'' refl h-false exec-m = exec-m
-- Inductive case: n = suc n'
-- Match on the step and halted values that exec uses
exec-chain (suc n') m prog s s' s'' exec-n h-false exec-m with step prog s
-- Step fails: exec (suc n') returns nothing, contradicts exec-n
... | nothing with () ← exec-n
-- Step succeeds with state s1
... | just s1 with halted s1 in eq-halt
-- s1 is halted: exec returns s1 = s', but halted s' = false contradicts halted s1 = true
...   | true with refl ← exec-n = ⊥-elim (true≢false (trans (sym eq-halt) h-false))
-- s1 is not halted: exec (suc n') prog s = exec n' prog s1
...   | false =
  -- At this point: exec (suc n') prog s = exec n' prog s1
  -- And exec-n : exec n' prog s1 ≡ just s'
  -- IH: exec (n' +ℕ m) prog s1 ≡ just s''
  -- Goal: exec (suc (n' +ℕ m)) prog s ≡ just s''
  -- Since step prog s = just s1 and halted s1 = false,
  -- exec (suc (n' +ℕ m)) prog s = exec (n' +ℕ m) prog s1
  exec-chain n' m prog s1 s' s'' exec-n h-false exec-m

-- | Fetching at the end of a prefix returns the first element of suffix
-- fetch (prefix ++ i ∷ rest) (length prefix) ≡ just i
fetch-at-prefix-end : ∀ (prefix : Program) (i : Instr) (rest : Program) →
  fetch (prefix ++ i ∷ rest) (length prefix) ≡ just i
fetch-at-prefix-end [] i rest = refl
fetch-at-prefix-end (x ∷ prefix) i rest = fetch-at-prefix-end prefix i rest

-- | Execute transfer instruction (mov rdi, rax) at position N in a program
-- Used between sub-programs in compose to transfer result to input
exec-transfer-at : ∀ (prefix : Program) (suffix : Program) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  ∃[ s' ] (step (prefix ++ mov (reg rdi) (reg rax) ∷ suffix) s ≡ just s'
         × halted s' ≡ false
         × pc s' ≡ length prefix +ℕ 1
         × readReg (regs s') rdi ≡ readReg (regs s) rax
         × readReg (regs s') rax ≡ readReg (regs s) rax)
exec-transfer-at prefix suffix s h-false pc-eq = s' , step-eq , h' , pc' , rdi-eq , rax-eq
  where
    prog : Program
    prog = prefix ++ mov (reg rdi) (reg rax) ∷ suffix

    s' : State
    s' = record s { regs = writeReg (regs s) rdi (readReg (regs s) rax)
                  ; pc = pc s +ℕ 1 }

    fetch-eq : fetch prog (pc s) ≡ just (mov (reg rdi) (reg rax))
    fetch-eq = subst (λ p → fetch prog p ≡ just (mov (reg rdi) (reg rax)))
                     (sym pc-eq) (fetch-at-prefix-end prefix (mov (reg rdi) (reg rax)) suffix)

    step-eq : step prog s ≡ just s'
    step-eq = trans (step-exec prog s (mov (reg rdi) (reg rax)) h-false fetch-eq)
                    (execMov-reg-reg s rdi rax)

    h' : halted s' ≡ false
    h' = h-false

    pc' : pc s' ≡ length prefix +ℕ 1
    pc' = cong (λ p → p +ℕ 1) pc-eq

    rdi-eq : readReg (regs s') rdi ≡ readReg (regs s) rax
    rdi-eq = readReg-writeReg-same (regs s) rdi (readReg (regs s) rax)

    rax-eq : readReg (regs s') rax ≡ readReg (regs s) rax
    rax-eq = readReg-writeReg-rdi-rax (regs s) (readReg (regs s) rax)

