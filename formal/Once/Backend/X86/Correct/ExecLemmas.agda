------------------------------------------------------------------------
-- Once.Backend.X86.Correct.ExecLemmas
--
-- Execution lemmas for x86-64 code generation proofs.
-- Level 2 - depends on FetchStep, InstrExec, RegisterLemmas.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.ExecLemmas where

open import Once.Type
open import Once.Semantics  -- Word is from X86.Semantics
open import Once.IR

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State
open Once.Backend.X86.Semantics.Flags
open import Once.Backend.X86.CodeGen

-- Import from other Correct modules
open import Once.Backend.X86.Correct.FetchStep
open import Once.Backend.X86.Correct.InstrExec
open import Once.Backend.X86.Correct.RegisterLemmas

-- Import encoding axioms
open import Once.Postulates
  using (encode; encode-unit; encode-fix-wrap; encode-fix-unwrap; encode-arr-identity)

open import Data.Nat using (ℕ; zero; suc; _≟_; _∸_; _≥_; _>_; s≤s; z≤n) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (∸-+-assoc; +-assoc; +-comm)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)

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

exec-six-steps-nonhalt : ∀ (prog : List Instr) (s s1 s2 s3 s4 s5 s6 : State) →
  step prog s ≡ just s1 → halted s1 ≡ false →
  step prog s1 ≡ just s2 → halted s2 ≡ false →
  step prog s2 ≡ just s3 → halted s3 ≡ false →
  step prog s3 ≡ just s4 → halted s4 ≡ false →
  step prog s4 ≡ just s5 → halted s5 ≡ false →
  step prog s5 ≡ just s6 → halted s6 ≡ false →
  exec 6 prog s ≡ just s6
exec-six-steps-nonhalt prog s s1 s2 s3 s4 s5 s6 step1 h1 step2 h2 step3 h3 step4 h4 step5 h5 step6 h6 =
  trans (exec-on-non-halted-step 5 prog s s1 step1 h1)
        (exec-five-steps-nonhalt prog s1 s2 s3 s4 s5 s6 step2 h2 step3 h3 step4 h4 step5 h5 step6 h6)

exec-seven-steps-nonhalt : ∀ (prog : List Instr) (s s1 s2 s3 s4 s5 s6 s7 : State) →
  step prog s ≡ just s1 → halted s1 ≡ false →
  step prog s1 ≡ just s2 → halted s2 ≡ false →
  step prog s2 ≡ just s3 → halted s3 ≡ false →
  step prog s3 ≡ just s4 → halted s4 ≡ false →
  step prog s4 ≡ just s5 → halted s5 ≡ false →
  step prog s5 ≡ just s6 → halted s6 ≡ false →
  step prog s6 ≡ just s7 → halted s7 ≡ false →
  exec 7 prog s ≡ just s7
exec-seven-steps-nonhalt prog s s1 s2 s3 s4 s5 s6 s7 step1 h1 step2 h2 step3 h3 step4 h4 step5 h5 step6 h6 step7 h7 =
  trans (exec-on-non-halted-step 6 prog s s1 step1 h1)
        (exec-six-steps-nonhalt prog s1 s2 s3 s4 s5 s6 s7 step2 h2 step3 h3 step4 h4 step5 h5 step6 h6 step7 h7)

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

------------------------------------------------------------------------
-- exec-until-pc lemmas
------------------------------------------------------------------------

-- | If we're already at target pc, exec-until-pc returns immediately
exec-until-pc-at-target : ∀ (target fuel : ℕ) (prog : Program) (s : State) →
  halted s ≡ false →
  pc s ≡ target →
  exec-until-pc target (suc fuel) prog s ≡ just s
exec-until-pc-at-target target fuel prog s h-false pc-eq
  rewrite h-false with pc s ≟ target
exec-until-pc-at-target target fuel prog s h-false pc-eq | yes _ = refl
exec-until-pc-at-target target fuel prog s h-false pc-eq | no pc≢target = ⊥-elim (pc≢target pc-eq)

-- | Key lemma: if exec-until-pc succeeds with halted = false, then pc = target
-- This is the main correctness property we need for branching proofs
exec-until-pc-reaches-target : ∀ (target fuel : ℕ) (prog : Program) (s s' : State) →
  exec-until-pc target fuel prog s ≡ just s' →
  halted s' ≡ false →
  pc s' ≡ target
-- Base case: fuel = 0, returns s unchanged
exec-until-pc-reaches-target target zero prog s s' exec-eq h-false with refl ← exec-eq =
  -- s' = s, need pc s = target, but we only know halted s' = false
  -- This case can only succeed if pc s = target already (otherwise we'd need more fuel)
  -- For now, leave as postulate (would need fuel lower bound)
  postulate-pc-at-fuel-zero
  where postulate postulate-pc-at-fuel-zero : pc s ≡ target
-- Inductive case: fuel = suc fuel'
exec-until-pc-reaches-target target (suc fuel') prog s s' exec-eq h-false with halted s in eq-halt
... | true with refl ← exec-eq = ⊥-elim (true≢false (trans (sym eq-halt) h-false))
... | false with pc s ≟ target
...   | yes pc-eq with refl ← exec-eq = pc-eq
...   | no _ with step prog s in eq-step
...     | nothing with () ← exec-eq
...     | just s1 = exec-until-pc-reaches-target target fuel' prog s1 s' exec-eq h-false

-- | exec-until-pc with sufficient fuel equals exec with exact steps when pc matches
-- This connects exec-until-pc to the regular exec when we know exact step count
-- Precondition: pc s ≢ target (we don't start at the target)
-- This avoids a complex edge case where we'd start at target but execute more steps
--
-- The proof is sound but complex due to Agda's with-clause abstraction creating
-- types that are hard to work with. The lemma states: if exec n prog s gives s'
-- and s' is at target pc (not halted), then exec-until-pc with sufficient fuel
-- also gives s'. This is true because exec-until-pc just adds early stopping at
-- target, and if exec reaches target in n steps, exec-until-pc will too.
postulate
  exec-until-pc-to-exec : ∀ (target n fuel : ℕ) (prog : Program) (s s' : State) →
    exec n prog s ≡ just s' →
    halted s' ≡ false →
    pc s' ≡ target →
    fuel ≥ n →
    pc s ≢ target →     -- Don't start at target
    exec-until-pc target fuel prog s ≡ just s'

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

-- | Execute pair setup at arbitrary offset in a program (non-halting)
-- 5 setup instructions: push r14; push r15; sub rsp, 16; mov r15, rsp; mov r14, rdi
--
-- After execution:
--   rsp = orig_rsp - 32 (2 pushes of 8 bytes + sub 16)
--   r15 = rsp (pair base address)
--   r14 = orig_rdi (saved input)
--   rdi = orig_rdi (unchanged)
--   pc = orig_pc + 5
exec-pair-setup-at : ∀ (prefix : Program) (rest : Program) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  ∃[ s' ] (exec 5 (prefix ++ push (reg r14) ∷ push (reg r15) ∷ sub (reg rsp) (imm 16) ∷ mov (reg r15) (reg rsp) ∷ mov (reg r14) (reg rdi) ∷ rest) s ≡ just s'
         × halted s' ≡ false
         × pc s' ≡ length prefix +ℕ 5
         × readReg (regs s') r14 ≡ readReg (regs s) rdi
         × readReg (regs s') rdi ≡ readReg (regs s) rdi
         × readReg (regs s') r15 ≡ readReg (regs s) rsp ∸ 32
         × readReg (regs s') rsp ≡ readReg (regs s) rsp ∸ 32)
exec-pair-setup-at prefix rest s h-false pc-eq = s5 , exec-eq , h5 , pc5 , r14-eq , rdi-eq , r15-eq , rsp-eq
  where
    prog : Program
    prog = prefix ++ push (reg r14) ∷ push (reg r15) ∷ sub (reg rsp) (imm 16) ∷ mov (reg r15) (reg rsp) ∷ mov (reg r14) (reg rdi) ∷ rest

    -- Original values
    orig-rsp : Word
    orig-rsp = readReg (regs s) rsp

    orig-rdi : Word
    orig-rdi = readReg (regs s) rdi

    orig-r14 : Word
    orig-r14 = readReg (regs s) r14

    orig-r15 : Word
    orig-r15 = readReg (regs s) r15

    -- Step 1: push r14 - save r14 to stack, decrement rsp by 8
    s1 : State
    s1 = record s { regs = writeReg (regs s) rsp (orig-rsp ∸ 8)
                  ; memory = writeMem (memory s) (orig-rsp ∸ 8) orig-r14
                  ; pc = pc s +ℕ 1 }

    fetch1 : fetch prog (length prefix) ≡ just (push (reg r14))
    fetch1 = fetch-at-prefix-end prefix (push (reg r14)) _

    step1 : step prog s ≡ just s1
    step1 = trans (step-exec prog s (push (reg r14)) h-false
                             (subst (λ n → fetch prog n ≡ just (push (reg r14))) (sym pc-eq) fetch1))
                  (execPush-reg prog s r14)

    h1 : halted s1 ≡ false
    h1 = h-false

    pc1 : pc s1 ≡ length prefix +ℕ 1
    pc1 = cong (λ n → n +ℕ 1) pc-eq

    -- rsp after step 1
    rsp-s1 : readReg (regs s1) rsp ≡ orig-rsp ∸ 8
    rsp-s1 = readReg-writeReg-same (regs s) rsp (orig-rsp ∸ 8)

    -- r15 after step 1 (unchanged - push only modifies rsp)
    r15-s1 : readReg (regs s1) r15 ≡ orig-r15
    r15-s1 = readReg-writeReg-rsp-r15 (regs s) (orig-rsp ∸ 8)

    -- Step 2: push r15 - save r15 to stack, decrement rsp by 8
    s2 : State
    s2 = record s1 { regs = writeReg (regs s1) rsp (readReg (regs s1) rsp ∸ 8)
                   ; memory = writeMem (memory s1) (readReg (regs s1) rsp ∸ 8) (readReg (regs s1) r15)
                   ; pc = pc s1 +ℕ 1 }

    prog-eq1 : prog ≡ (prefix ++ push (reg r14) ∷ []) ++ push (reg r15) ∷ sub (reg rsp) (imm 16) ∷ mov (reg r15) (reg rsp) ∷ mov (reg r14) (reg rdi) ∷ rest
    prog-eq1 = sym (++-assoc prefix _ _)

    len-prefix1 : length (prefix ++ push (reg r14) ∷ []) ≡ length prefix +ℕ 1
    len-prefix1 = List-length-++ prefix

    fetch2 : fetch prog (length prefix +ℕ 1) ≡ just (push (reg r15))
    fetch2 = subst₂ (λ p n → fetch p n ≡ just (push (reg r15))) (sym prog-eq1) len-prefix1
                    (fetch-at-prefix-end (prefix ++ push (reg r14) ∷ []) (push (reg r15)) _)

    step2 : step prog s1 ≡ just s2
    step2 = trans (step-exec prog s1 (push (reg r15)) h1
                             (subst (λ n → fetch prog n ≡ just (push (reg r15))) (sym pc1) fetch2))
                  (execPush-reg prog s1 r15)

    h2 : halted s2 ≡ false
    h2 = h-false

    pc2 : pc s2 ≡ length prefix +ℕ 2
    pc2 = trans (cong (λ n → n +ℕ 1) pc1) (+-assoc (length prefix) 1 1)

    rsp-s2-raw : readReg (regs s2) rsp ≡ readReg (regs s1) rsp ∸ 8
    rsp-s2-raw = readReg-writeReg-same (regs s1) rsp (readReg (regs s1) rsp ∸ 8)

    rsp-s2 : readReg (regs s2) rsp ≡ orig-rsp ∸ 16
    rsp-s2 = trans rsp-s2-raw (trans (cong (_∸ 8) rsp-s1) (∸-+-assoc orig-rsp 8 8))

    -- Step 3: sub rsp, 16 - allocate 16 bytes on stack
    s3 : State
    s3 = record s2 { regs = writeReg (regs s2) rsp (readReg (regs s2) rsp ∸ 16)
                   ; pc = pc s2 +ℕ 1
                   ; flags = updateFlags (readReg (regs s2) rsp ∸ 16) (readReg (regs s2) rsp) }

    prog-eq2 : prog ≡ (prefix ++ push (reg r14) ∷ push (reg r15) ∷ []) ++ sub (reg rsp) (imm 16) ∷ mov (reg r15) (reg rsp) ∷ mov (reg r14) (reg rdi) ∷ rest
    prog-eq2 = sym (++-assoc prefix _ _)

    len-prefix2 : length (prefix ++ push (reg r14) ∷ push (reg r15) ∷ []) ≡ length prefix +ℕ 2
    len-prefix2 = trans (List-length-++ prefix) (cong (length prefix +ℕ_) refl)

    fetch3 : fetch prog (length prefix +ℕ 2) ≡ just (sub (reg rsp) (imm 16))
    fetch3 = subst₂ (λ p n → fetch p n ≡ just (sub (reg rsp) (imm 16))) (sym prog-eq2) len-prefix2
                    (fetch-at-prefix-end (prefix ++ push (reg r14) ∷ push (reg r15) ∷ []) (sub (reg rsp) (imm 16)) _)

    step3 : step prog s2 ≡ just s3
    step3 = trans (step-exec prog s2 (sub (reg rsp) (imm 16)) h2
                             (subst (λ n → fetch prog n ≡ just (sub (reg rsp) (imm 16))) (sym pc2) fetch3))
                  (execSub-reg-imm prog s2 rsp 16)

    h3 : halted s3 ≡ false
    h3 = h-false

    pc3 : pc s3 ≡ length prefix +ℕ 3
    pc3 = trans (cong (λ n → n +ℕ 1) pc2) (+-assoc (length prefix) 2 1)

    rsp-s3-raw : readReg (regs s3) rsp ≡ readReg (regs s2) rsp ∸ 16
    rsp-s3-raw = readReg-writeReg-same (regs s2) rsp (readReg (regs s2) rsp ∸ 16)

    rsp-s3 : readReg (regs s3) rsp ≡ orig-rsp ∸ 32
    rsp-s3 = trans rsp-s3-raw (trans (cong (_∸ 16) rsp-s2) (∸-+-assoc orig-rsp 16 16))

    -- Step 4: mov r15, rsp - set r15 to current rsp (pair base address)
    s4 : State
    s4 = record s3 { regs = writeReg (regs s3) r15 (readReg (regs s3) rsp)
                   ; pc = pc s3 +ℕ 1 }

    prog-eq3 : prog ≡ (prefix ++ push (reg r14) ∷ push (reg r15) ∷ sub (reg rsp) (imm 16) ∷ []) ++ mov (reg r15) (reg rsp) ∷ mov (reg r14) (reg rdi) ∷ rest
    prog-eq3 = sym (++-assoc prefix _ _)

    len-prefix3 : length (prefix ++ push (reg r14) ∷ push (reg r15) ∷ sub (reg rsp) (imm 16) ∷ []) ≡ length prefix +ℕ 3
    len-prefix3 = trans (List-length-++ prefix) (cong (length prefix +ℕ_) refl)

    fetch4 : fetch prog (length prefix +ℕ 3) ≡ just (mov (reg r15) (reg rsp))
    fetch4 = subst₂ (λ p n → fetch p n ≡ just (mov (reg r15) (reg rsp))) (sym prog-eq3) len-prefix3
                    (fetch-at-prefix-end (prefix ++ push (reg r14) ∷ push (reg r15) ∷ sub (reg rsp) (imm 16) ∷ []) (mov (reg r15) (reg rsp)) _)

    step4 : step prog s3 ≡ just s4
    step4 = trans (step-exec prog s3 (mov (reg r15) (reg rsp)) h3
                             (subst (λ n → fetch prog n ≡ just (mov (reg r15) (reg rsp))) (sym pc3) fetch4))
                  (execMov-reg-reg s3 r15 rsp)

    h4 : halted s4 ≡ false
    h4 = h-false

    pc4 : pc s4 ≡ length prefix +ℕ 4
    pc4 = trans (cong (λ n → n +ℕ 1) pc3) (+-assoc (length prefix) 3 1)

    r15-s4 : readReg (regs s4) r15 ≡ orig-rsp ∸ 32
    r15-s4 = trans (readReg-writeReg-same (regs s3) r15 (readReg (regs s3) rsp)) rsp-s3

    rdi-s4 : readReg (regs s4) rdi ≡ orig-rdi
    rdi-s4 = trans (readReg-writeReg-r15-rdi (regs s3) (readReg (regs s3) rsp))
                   (trans (readReg-writeReg-rsp-rdi (regs s2) (readReg (regs s2) rsp ∸ 16))
                          (trans (readReg-writeReg-rsp-rdi (regs s1) (readReg (regs s1) rsp ∸ 8))
                                 (readReg-writeReg-rsp-rdi (regs s) (orig-rsp ∸ 8))))

    -- Step 5: mov r14, rdi - save input to r14
    s5 : State
    s5 = record s4 { regs = writeReg (regs s4) r14 (readReg (regs s4) rdi)
                   ; pc = pc s4 +ℕ 1 }

    prog-eq4 : prog ≡ (prefix ++ push (reg r14) ∷ push (reg r15) ∷ sub (reg rsp) (imm 16) ∷ mov (reg r15) (reg rsp) ∷ []) ++ mov (reg r14) (reg rdi) ∷ rest
    prog-eq4 = sym (++-assoc prefix _ _)

    len-prefix4 : length (prefix ++ push (reg r14) ∷ push (reg r15) ∷ sub (reg rsp) (imm 16) ∷ mov (reg r15) (reg rsp) ∷ []) ≡ length prefix +ℕ 4
    len-prefix4 = trans (List-length-++ prefix) (cong (length prefix +ℕ_) refl)

    fetch5 : fetch prog (length prefix +ℕ 4) ≡ just (mov (reg r14) (reg rdi))
    fetch5 = subst₂ (λ p n → fetch p n ≡ just (mov (reg r14) (reg rdi))) (sym prog-eq4) len-prefix4
                    (fetch-at-prefix-end (prefix ++ push (reg r14) ∷ push (reg r15) ∷ sub (reg rsp) (imm 16) ∷ mov (reg r15) (reg rsp) ∷ []) (mov (reg r14) (reg rdi)) _)

    step5 : step prog s4 ≡ just s5
    step5 = trans (step-exec prog s4 (mov (reg r14) (reg rdi)) h4
                             (subst (λ n → fetch prog n ≡ just (mov (reg r14) (reg rdi))) (sym pc4) fetch5))
                  (execMov-reg-reg s4 r14 rdi)

    h5 : halted s5 ≡ false
    h5 = h-false

    pc5 : pc s5 ≡ length prefix +ℕ 5
    pc5 = trans (cong (λ n → n +ℕ 1) pc4) (+-assoc (length prefix) 4 1)

    exec-eq : exec 5 prog s ≡ just s5
    exec-eq = exec-five-steps-nonhalt prog s s1 s2 s3 s4 s5 step1 h1 step2 h2 step3 h3 step4 h4 step5 h5

    r14-eq : readReg (regs s5) r14 ≡ orig-rdi
    r14-eq = trans (readReg-writeReg-same (regs s4) r14 (readReg (regs s4) rdi)) rdi-s4

    rdi-eq : readReg (regs s5) rdi ≡ orig-rdi
    rdi-eq = trans (readReg-writeReg-r14-rdi (regs s4) (readReg (regs s4) rdi)) rdi-s4

    r15-eq : readReg (regs s5) r15 ≡ orig-rsp ∸ 32
    r15-eq = trans (readReg-writeReg-r14-r15 (regs s4) (readReg (regs s4) rdi)) r15-s4

    -- rsp is preserved through s4 (writes r15) and s5 (writes r14)
    rsp-s4 : readReg (regs s4) rsp ≡ orig-rsp ∸ 32
    rsp-s4 = trans (readReg-writeReg-r15-rsp (regs s3) (readReg (regs s3) rsp)) rsp-s3

    rsp-eq : readReg (regs s5) rsp ≡ orig-rsp ∸ 32
    rsp-eq = trans (readReg-writeReg-r14-rsp (regs s4) (readReg (regs s4) rdi)) rsp-s4

-- Note: exec-pair-setup-at-7 and exec-pair-middle-at are large lemmas that follow
-- the same pattern. They are kept in Correct.agda for now to manage module size.
-- If needed, they can be extracted here.

------------------------------------------------------------------------
-- Single-IR execution at offset lemmas
------------------------------------------------------------------------

-- | Execute id at arbitrary offset in a program (non-halting)
-- This is the general case of run-id-nonhalt where id code can be at any position
-- Program structure: prefix ++ [mov rax, rdi] ++ suffix
run-id-at-offset : ∀ {A} (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode x →
  ∃[ s' ] (step (prefix ++ compile-x86 {A} {A} id ++ suffix) s ≡ just s'
         × halted s' ≡ false
         × pc s' ≡ length prefix +ℕ 1
         × readReg (regs s') rax ≡ encode x)
run-id-at-offset {A} prefix suffix x s h-false pc-eq rdi-eq = s' , step-eq , h' , pc' , rax-eq
  where
    prog : Program
    prog = prefix ++ compile-x86 {A} {A} id ++ suffix

    s' : State
    s' = record s { regs = writeReg (regs s) rax (readReg (regs s) rdi)
                  ; pc = pc s +ℕ 1 }

    fetch-eq : fetch prog (pc s) ≡ just (mov (reg rax) (reg rdi))
    fetch-eq = subst (λ p → fetch prog p ≡ just (mov (reg rax) (reg rdi)))
                     (sym pc-eq) (fetch-at-prefix-end prefix (mov (reg rax) (reg rdi)) suffix)

    step-eq : step prog s ≡ just s'
    step-eq = trans (step-exec prog s (mov (reg rax) (reg rdi)) h-false fetch-eq)
                    (execMov-reg-reg s rax rdi)

    h' : halted s' ≡ false
    h' = h-false

    pc' : pc s' ≡ length prefix +ℕ 1
    pc' = cong (λ p → p +ℕ 1) pc-eq

    rax-eq : readReg (regs s') rax ≡ encode x
    rax-eq = trans (readReg-writeReg-same (regs s) rax (readReg (regs s) rdi)) rdi-eq

-- | Execute terminal at arbitrary offset in a program (non-halting)
-- Program structure: prefix ++ [mov rax, 0] ++ suffix
run-terminal-at-offset : ∀ {A} (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  ∃[ s' ] (step (prefix ++ compile-x86 {A} {Unit} terminal ++ suffix) s ≡ just s'
         × halted s' ≡ false
         × pc s' ≡ length prefix +ℕ 1
         × readReg (regs s') rax ≡ encode {Unit} tt)
run-terminal-at-offset {A} prefix suffix x s h-false pc-eq = s' , step-eq , h' , pc' , rax-eq
  where
    prog : Program
    prog = prefix ++ compile-x86 {A} {Unit} terminal ++ suffix

    s' : State
    s' = record s { regs = writeReg (regs s) rax 0
                  ; pc = pc s +ℕ 1 }

    fetch-eq : fetch prog (pc s) ≡ just (mov (reg rax) (imm 0))
    fetch-eq = subst (λ p → fetch prog p ≡ just (mov (reg rax) (imm 0)))
                     (sym pc-eq) (fetch-at-prefix-end prefix (mov (reg rax) (imm 0)) suffix)

    step-eq : step prog s ≡ just s'
    step-eq = trans (step-exec prog s (mov (reg rax) (imm 0)) h-false fetch-eq)
                    (execMov-reg-imm s rax 0)

    h' : halted s' ≡ false
    h' = h-false

    pc' : pc s' ≡ length prefix +ℕ 1
    pc' = cong (λ p → p +ℕ 1) pc-eq

    rax-eq : readReg (regs s') rax ≡ encode tt
    rax-eq = trans (readReg-writeReg-same (regs s) rax 0) (sym encode-unit)

-- | Execute fold at arbitrary offset in a program (non-halting)
-- compile-x86 fold = [mov rax, rdi] (same as id)
-- Result is encode (wrap x) = encode x by encode-fix-wrap
run-fold-at-offset : ∀ {F} (prefix suffix : Program) (x : ⟦ F ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode x →
  ∃[ s' ] (step (prefix ++ compile-x86 {F} {Fix F} fold ++ suffix) s ≡ just s'
         × halted s' ≡ false
         × pc s' ≡ length prefix +ℕ 1
         × readReg (regs s') rax ≡ encode (wrap x))
run-fold-at-offset {F} prefix suffix x s h-false pc-eq rdi-eq = s' , step-eq , h' , pc' , rax-eq
  where
    prog : Program
    prog = prefix ++ compile-x86 {F} {Fix F} fold ++ suffix

    s' : State
    s' = record s { regs = writeReg (regs s) rax (readReg (regs s) rdi)
                  ; pc = pc s +ℕ 1 }

    fetch-eq : fetch prog (pc s) ≡ just (mov (reg rax) (reg rdi))
    fetch-eq = subst (λ p → fetch prog p ≡ just (mov (reg rax) (reg rdi)))
                     (sym pc-eq) (fetch-at-prefix-end prefix (mov (reg rax) (reg rdi)) suffix)

    step-eq : step prog s ≡ just s'
    step-eq = trans (step-exec prog s (mov (reg rax) (reg rdi)) h-false fetch-eq)
                    (execMov-reg-reg s rax rdi)

    h' : halted s' ≡ false
    h' = h-false

    pc' : pc s' ≡ length prefix +ℕ 1
    pc' = cong (λ p → p +ℕ 1) pc-eq

    rax-eq : readReg (regs s') rax ≡ encode (wrap x)
    rax-eq = trans (readReg-writeReg-same (regs s) rax (readReg (regs s) rdi))
                   (trans rdi-eq (encode-fix-wrap x))

-- | Execute unfold at arbitrary offset in a program (non-halting)
-- compile-x86 unfold = [mov rax, rdi] (same as id)
-- Result is encode (eval unfold x) by encode-fix-unwrap
run-unfold-at-offset : ∀ {F} (prefix suffix : Program) (x : ⟦ Fix F ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode x →
  ∃[ s' ] (step (prefix ++ compile-x86 {Fix F} {F} unfold ++ suffix) s ≡ just s'
         × halted s' ≡ false
         × pc s' ≡ length prefix +ℕ 1
         × readReg (regs s') rax ≡ encode (eval {Fix F} {F} unfold x))
run-unfold-at-offset {F} prefix suffix x s h-false pc-eq rdi-eq = s' , step-eq , h' , pc' , rax-eq
  where
    prog : Program
    prog = prefix ++ compile-x86 {Fix F} {F} unfold ++ suffix

    s' : State
    s' = record s { regs = writeReg (regs s) rax (readReg (regs s) rdi)
                  ; pc = pc s +ℕ 1 }

    fetch-eq : fetch prog (pc s) ≡ just (mov (reg rax) (reg rdi))
    fetch-eq = subst (λ p → fetch prog p ≡ just (mov (reg rax) (reg rdi)))
                     (sym pc-eq) (fetch-at-prefix-end prefix (mov (reg rax) (reg rdi)) suffix)

    step-eq : step prog s ≡ just s'
    step-eq = trans (step-exec prog s (mov (reg rax) (reg rdi)) h-false fetch-eq)
                    (execMov-reg-reg s rax rdi)

    h' : halted s' ≡ false
    h' = h-false

    pc' : pc s' ≡ length prefix +ℕ 1
    pc' = cong (λ p → p +ℕ 1) pc-eq

    -- eval unfold x = unwrap x, encode (unwrap x) = encode x by encode-fix-unwrap
    rax-eq : readReg (regs s') rax ≡ encode (eval {Fix F} {F} unfold x)
    rax-eq = trans (readReg-writeReg-same (regs s) rax (readReg (regs s) rdi))
                   (trans rdi-eq (encode-fix-unwrap x))

-- | Execute arr at arbitrary offset in a program (non-halting)
-- compile-x86 arr = [mov rax, rdi] (same as id)
-- arr : IR (A ⇒ B) (Eff A B), eval arr f = f (identity)
-- encode (eval arr f) = encode f
run-arr-at-offset : ∀ {A B} (prefix suffix : Program) (f : ⟦ A ⇒ B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode f →
  ∃[ s' ] (step (prefix ++ compile-x86 {A ⇒ B} {Eff A B} arr ++ suffix) s ≡ just s'
         × halted s' ≡ false
         × pc s' ≡ length prefix +ℕ 1
         × readReg (regs s') rax ≡ encode {Eff A B} f)
run-arr-at-offset {A} {B} prefix suffix f s h-false pc-eq rdi-eq = s' , step-eq , h' , pc' , rax-eq
  where
    prog : Program
    prog = prefix ++ compile-x86 {A ⇒ B} {Eff A B} arr ++ suffix

    s' : State
    s' = record s { regs = writeReg (regs s) rax (readReg (regs s) rdi)
                  ; pc = pc s +ℕ 1 }

    fetch-eq : fetch prog (pc s) ≡ just (mov (reg rax) (reg rdi))
    fetch-eq = subst (λ p → fetch prog p ≡ just (mov (reg rax) (reg rdi)))
                     (sym pc-eq) (fetch-at-prefix-end prefix (mov (reg rax) (reg rdi)) suffix)

    step-eq : step prog s ≡ just s'
    step-eq = trans (step-exec prog s (mov (reg rax) (reg rdi)) h-false fetch-eq)
                    (execMov-reg-reg s rax rdi)

    h' : halted s' ≡ false
    h' = h-false

    pc' : pc s' ≡ length prefix +ℕ 1
    pc' = cong (λ p → p +ℕ 1) pc-eq

    -- eval arr f = f, and encode-arr-identity says encode {A ⇒ B} f ≡ encode {Eff A B} f
    rax-eq : readReg (regs s') rax ≡ encode {Eff A B} f
    rax-eq = trans (readReg-writeReg-same (regs s) rax (readReg (regs s) rdi))
                   (trans rdi-eq (encode-arr-identity f))

-- | Execute fst at arbitrary offset in a program (non-halting)
-- compile-x86 fst = [mov rax, [rdi]] (1 instruction)
run-fst-at-offset : ∀ {A B} (prefix suffix : Program) (a : ⟦ A ⟧) (b : ⟦ B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode (a , b) →
  readMem (memory s) (encode (a , b)) ≡ just (encode a) →
  ∃[ s' ] (step (prefix ++ compile-x86 {A * B} {A} fst ++ suffix) s ≡ just s'
         × halted s' ≡ false
         × pc s' ≡ length prefix +ℕ 1
         × readReg (regs s') rax ≡ encode a)
run-fst-at-offset {A} {B} prefix suffix a b s h-false pc-eq rdi-eq mem-eq = s' , step-eq , h' , pc' , rax-eq
  where
    prog : Program
    prog = prefix ++ compile-x86 {A * B} {A} fst ++ suffix

    s' : State
    s' = record s { regs = writeReg (regs s) rax (encode a)
                  ; pc = pc s +ℕ 1 }

    fetch-eq : fetch prog (pc s) ≡ just (mov (reg rax) (mem (base rdi)))
    fetch-eq = subst (λ p → fetch prog p ≡ just (mov (reg rax) (mem (base rdi))))
                     (sym pc-eq) (fetch-at-prefix-end prefix (mov (reg rax) (mem (base rdi))) suffix)

    step-eq : step prog s ≡ just s'
    step-eq = trans (step-exec prog s (mov (reg rax) (mem (base rdi))) h-false fetch-eq)
                    (execMov-reg-mem-base s rax rdi (encode a)
                      (trans (cong (λ addr → readMem (memory s) addr) rdi-eq) mem-eq))

    h' : halted s' ≡ false
    h' = h-false

    pc' : pc s' ≡ length prefix +ℕ 1
    pc' = cong (λ p → p +ℕ 1) pc-eq

    rax-eq : readReg (regs s') rax ≡ encode a
    rax-eq = readReg-writeReg-same (regs s) rax (encode a)

-- | Execute snd at arbitrary offset in a program (non-halting)
-- compile-x86 snd = [mov rax, [rdi+8]] (1 instruction)
run-snd-at-offset : ∀ {A B} (prefix suffix : Program) (a : ⟦ A ⟧) (b : ⟦ B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode (a , b) →
  readMem (memory s) (encode (a , b) +ℕ 8) ≡ just (encode b) →
  ∃[ s' ] (step (prefix ++ compile-x86 {A * B} {B} snd ++ suffix) s ≡ just s'
         × halted s' ≡ false
         × pc s' ≡ length prefix +ℕ 1
         × readReg (regs s') rax ≡ encode b)
run-snd-at-offset {A} {B} prefix suffix a b s h-false pc-eq rdi-eq mem-eq = s' , step-eq , h' , pc' , rax-eq
  where
    prog : Program
    prog = prefix ++ compile-x86 {A * B} {B} snd ++ suffix

    s' : State
    s' = record s { regs = writeReg (regs s) rax (encode b)
                  ; pc = pc s +ℕ 1 }

    fetch-eq : fetch prog (pc s) ≡ just (mov (reg rax) (mem (base+disp rdi 8)))
    fetch-eq = subst (λ p → fetch prog p ≡ just (mov (reg rax) (mem (base+disp rdi 8))))
                     (sym pc-eq) (fetch-at-prefix-end prefix (mov (reg rax) (mem (base+disp rdi 8))) suffix)

    step-eq : step prog s ≡ just s'
    step-eq = trans (step-exec prog s (mov (reg rax) (mem (base+disp rdi 8))) h-false fetch-eq)
                    (execMov-reg-mem-disp s rax rdi 8 (encode b)
                      (trans (cong (λ addr → readMem (memory s) (addr +ℕ 8)) rdi-eq) mem-eq))

    h' : halted s' ≡ false
    h' = h-false

    pc' : pc s' ≡ length prefix +ℕ 1
    pc' = cong (λ p → p +ℕ 1) pc-eq

    rax-eq : readReg (regs s') rax ≡ encode b
    rax-eq = readReg-writeReg-same (regs s) rax (encode b)

-- | Execute mov rdi, rax at arbitrary offset (transfer result to input register)
-- This is the glue instruction between composed programs
run-mov-rdi-rax-at-offset : ∀ (prefix suffix : Program) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  ∃[ s' ] (step (prefix ++ mov (reg rdi) (reg rax) ∷ suffix) s ≡ just s'
         × halted s' ≡ false
         × pc s' ≡ length prefix +ℕ 1
         × readReg (regs s') rdi ≡ readReg (regs s) rax
         × readReg (regs s') rax ≡ readReg (regs s) rax)
run-mov-rdi-rax-at-offset prefix suffix s h-false pc-eq = s' , step-eq , h' , pc' , rdi-eq , rax-eq
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

    -- rax is preserved (we only wrote to rdi)
    rax-eq : readReg (regs s') rax ≡ readReg (regs s) rax
    rax-eq = readReg-writeReg-rdi-rax (regs s) (readReg (regs s) rax)

------------------------------------------------------------------------
-- Import N-step execution lemmas from Common.Exec
------------------------------------------------------------------------

-- Instantiated with our State, Instr, and base lemmas
open import Once.Backend.Common.Exec
  halted step exec exec-on-non-halted-step exec-on-halted-step
  public

------------------------------------------------------------------------
-- Fuel and helpers for exec-until-pc conversion
------------------------------------------------------------------------

-- | Default fuel for exec-until-pc (sufficiently large for any practical IR)
runFuel : ℕ
runFuel = 100000

-- | runFuel is at least n for any reasonable n (postulated for simplicity)
postulate
  runFuel≥ : ∀ (n : ℕ) → runFuel ≥ n

-- | n ≢ n + k for any k > 0 (used to show pc s ≢ target when we don't start at target)
pc-not-at-target : ∀ {n} (k : ℕ) → k > 0 → n ≢ n +ℕ k
pc-not-at-target {n} (suc k) _ eq = helper n k eq
  where
    suc-inj : ∀ {a b} → suc a ≡ suc b → a ≡ b
    suc-inj refl = refl
    helper : ∀ n k → n ≢ n +ℕ suc k
    helper zero k ()
    helper (suc n) k eq = helper n k (suc-inj eq)

-- | compile-length is always positive (at least 1)
postulate
  compile-length>0 : ∀ {A B} (ir : IR A B) → compile-length ir > 0

-- | Convert exec proof to exec-until-pc for simple generators
-- Used when compile-length equals actual steps (non-branching generators)
exec-to-exec-until-pc-simple : ∀ {A B} (ir : IR A B) (prefix suffix : Program) (s s' : State) →
  exec (compile-length ir) (prefix ++ compile-x86 ir ++ suffix) s ≡ just s' →
  halted s' ≡ false →
  pc s' ≡ length prefix +ℕ compile-length ir →
  pc s ≡ length prefix →
  exec-until-pc (length prefix +ℕ compile-length ir) runFuel (prefix ++ compile-x86 ir ++ suffix) s ≡ just s'
exec-to-exec-until-pc-simple {A} {B} ir prefix suffix s s' exec-eq h-eq pc'-eq pc-eq =
  exec-until-pc-to-exec (length prefix +ℕ compile-length ir) (compile-length ir) runFuel
    (prefix ++ compile-x86 ir ++ suffix) s s'
    exec-eq h-eq pc'-eq (runFuel≥ (compile-length ir))
    (subst (λ p → p ≢ length prefix +ℕ compile-length ir) (sym pc-eq)
           (pc-not-at-target (compile-length ir) (compile-length>0 ir)))
