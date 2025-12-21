------------------------------------------------------------------------
-- Once.Backend.X86.Correct.E2ETrace
--
-- Full Trace-Through E2E Proof
--
-- Proves execution of apply ∘ ⟨curry fst, id⟩ by tracing through
-- ALL instruction executions step-by-step.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.E2ETrace where

open import Once.Type
open import Once.IR
open import Once.Semantics hiding (code-ptr; env-addr; semantics)

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State
open Once.Backend.X86.Semantics.Flags
open import Once.Backend.X86.CodeGen

open import Once.Postulates using (encode; encode-unit)
open import Once.Backend.X86.Correct.Star
  using (Star; refl*; step*; star-trans; ⟨_,_⟩◅_; exec-halted-extend)
open import Once.Backend.X86.Correct.RegisterLemmas
open import Once.Backend.X86.Correct.FetchStep
open import Once.Backend.X86.Correct.InstrExec
open import Once.Backend.X86.Correct.ExecLemmas

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _∸_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-assoc; +-comm; +-identityʳ)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)

------------------------------------------------------------------------
-- Full Trace-Through E2E Proof
------------------------------------------------------------------------
--
-- This proof traces through ALL instruction executions for:
--   apply ∘ ⟨curry fst, id⟩
--
-- Execution flow (28 steps):
--   0-10: Pair setup + curry (creates closure with code-ptr=11)
--   10→18: jmp skips thunk
--   18-27: Complete pairing + composition connector
--   28-33: Apply setup + call
--   33→11: call jumps to thunk
--   11-17: Thunk execution + ret (halt)
--
-- We use Unit as the concrete type for explicit encoding.

-- | Full E2E trace proof
-- Proves execution of apply ∘ ⟨curry fst, id⟩ on unit input
-- without using any postulates for the execution itself.
module E2E-Trace where
  open import Data.Nat.Properties using (+-assoc; +-comm; +-identityʳ)

  -- The expression under test
  e2e-expr : IR Unit Unit
  e2e-expr = apply ∘ ⟨ curry fst , id ⟩

  -- The compiled program
  prog : Program
  prog = compile-x86 e2e-expr

  -- Input encoding: unit = 0
  input-val : Word
  input-val = 0

  -- Initial state with sufficient stack space
  -- We need stack space for: pair allocation, closure allocation, thunk pair
  init-rsp : Word
  init-rsp = 1000  -- Plenty of stack space

  -- Initial state (write rsp first, then rdi, so rdi proof uses readReg-writeReg-same)
  s0 : State
  s0 = record initState
    { regs = writeReg (writeReg emptyRegFile rsp init-rsp) rdi input-val
    ; pc = 0
    }

  -- Verify initial state properties
  s0-halted : halted s0 ≡ false
  s0-halted = refl

  s0-pc : pc s0 ≡ 0
  s0-pc = refl

  s0-rdi : readReg (regs s0) rdi ≡ input-val
  s0-rdi = readReg-writeReg-same (writeReg emptyRegFile rsp init-rsp) rdi input-val

  s0-rsp : readReg (regs s0) rsp ≡ init-rsp
  s0-rsp = refl

  ------------------------------------------------------------------------
  -- Phase 1: Pair setup (instructions 0-4)
  ------------------------------------------------------------------------

  -- Fetch proofs: the program has expected instructions at each position
  -- Since prog = compile-x86 (apply ∘ ⟨curry fst, id⟩), and compile-x86 ⟨..⟩ starts
  -- with push r14, push r15, etc., these are all refl.
  prog-fetch-0 : fetch prog 0 ≡ just (push (reg r14))
  prog-fetch-0 = refl

  prog-fetch-1 : fetch prog 1 ≡ just (push (reg r15))
  prog-fetch-1 = refl

  prog-fetch-2 : fetch prog 2 ≡ just (push (reg rbp))
  prog-fetch-2 = refl

  prog-fetch-3 : fetch prog 3 ≡ just (mov (reg rbp) (reg rsp))
  prog-fetch-3 = refl

  prog-fetch-4 : fetch prog 4 ≡ just (sub (reg rsp) (imm 16))
  prog-fetch-4 = refl

  prog-fetch-5 : fetch prog 5 ≡ just (mov (reg r15) (reg rsp))
  prog-fetch-5 = refl

  prog-fetch-6 : fetch prog 6 ≡ just (mov (reg r14) (reg rdi))
  prog-fetch-6 = refl

  -- Instruction 0: push r14
  -- Decrements rsp by 8, stores r14 at new rsp
  s1 : State
  s1 = record s0
    { regs = writeReg (regs s0) rsp (readReg (regs s0) rsp ∸ 8)
    ; memory = writeMem (memory s0) (readReg (regs s0) rsp ∸ 8) (readReg (regs s0) r14)
    ; pc = pc s0 +ℕ 1
    }

  step-0 : step prog s0 ≡ just s1
  step-0 = trans (step-exec prog s0 (push (reg r14)) s0-halted prog-fetch-0) (execPush-reg prog s0 r14)

  s1-halted : halted s1 ≡ false
  s1-halted = refl

  s1-pc : pc s1 ≡ 1
  s1-pc = refl

  s1-rsp : readReg (regs s1) rsp ≡ init-rsp ∸ 8
  s1-rsp = refl

  -- Instruction 1: push r15
  s2 : State
  s2 = record s1
    { regs = writeReg (regs s1) rsp (readReg (regs s1) rsp ∸ 8)
    ; memory = writeMem (memory s1) (readReg (regs s1) rsp ∸ 8) (readReg (regs s1) r15)
    ; pc = pc s1 +ℕ 1
    }

  step-1 : step prog s1 ≡ just s2
  step-1 = trans (step-exec prog s1 (push (reg r15)) s1-halted prog-fetch-1) (execPush-reg prog s1 r15)

  s2-halted : halted s2 ≡ false
  s2-halted = refl

  s2-pc : pc s2 ≡ 2
  s2-pc = refl

  s2-rsp : readReg (regs s2) rsp ≡ init-rsp ∸ 16
  s2-rsp = refl

  -- Instruction 2: push rbp
  s3 : State
  s3 = record s2
    { regs = writeReg (regs s2) rsp (readReg (regs s2) rsp ∸ 8)
    ; memory = writeMem (memory s2) (readReg (regs s2) rsp ∸ 8) (readReg (regs s2) rbp)
    ; pc = pc s2 +ℕ 1
    }

  step-2 : step prog s2 ≡ just s3
  step-2 = trans (step-exec prog s2 (push (reg rbp)) s2-halted prog-fetch-2) (execPush-reg prog s2 rbp)

  s3-halted : halted s3 ≡ false
  s3-halted = refl

  s3-pc : pc s3 ≡ 3
  s3-pc = refl

  s3-rsp : readReg (regs s3) rsp ≡ init-rsp ∸ 24
  s3-rsp = refl

  -- Instruction 3: mov rbp, rsp
  s4 : State
  s4 = record s3
    { regs = writeReg (regs s3) rbp (readReg (regs s3) rsp)
    ; pc = pc s3 +ℕ 1
    }

  step-3 : step prog s3 ≡ just s4
  step-3 = trans (step-exec prog s3 (mov (reg rbp) (reg rsp)) s3-halted prog-fetch-3) (execMov-reg-reg s3 rbp rsp)

  s4-halted : halted s4 ≡ false
  s4-halted = refl

  s4-pc : pc s4 ≡ 4
  s4-pc = refl

  s4-rbp : readReg (regs s4) rbp ≡ init-rsp ∸ 24
  s4-rbp = refl

  s4-rsp : readReg (regs s4) rsp ≡ init-rsp ∸ 24
  s4-rsp = refl

  -- Instruction 4: sub rsp, 16
  s5 : State
  s5 = record s4
    { regs = writeReg (regs s4) rsp (readReg (regs s4) rsp ∸ 16)
    ; pc = pc s4 +ℕ 1
    ; flags = updateFlags (readReg (regs s4) rsp ∸ 16) (readReg (regs s4) rsp)
    }

  step-4 : step prog s4 ≡ just s5
  step-4 = trans (step-exec prog s4 (sub (reg rsp) (imm 16)) s4-halted prog-fetch-4) (execSub-reg-imm prog s4 rsp 16)

  s5-halted : halted s5 ≡ false
  s5-halted = refl

  s5-pc : pc s5 ≡ 5
  s5-pc = refl

  s5-rsp : readReg (regs s5) rsp ≡ init-rsp ∸ 40
  s5-rsp = refl

  -- Instruction 5: mov r15, rsp
  s6 : State
  s6 = record s5
    { regs = writeReg (regs s5) r15 (readReg (regs s5) rsp)
    ; pc = pc s5 +ℕ 1
    }

  step-5 : step prog s5 ≡ just s6
  step-5 = trans (step-exec prog s5 (mov (reg r15) (reg rsp)) s5-halted prog-fetch-5) (execMov-reg-reg s5 r15 rsp)

  s6-halted : halted s6 ≡ false
  s6-halted = refl

  s6-pc : pc s6 ≡ 6
  s6-pc = refl

  s6-r15 : readReg (regs s6) r15 ≡ init-rsp ∸ 40
  s6-r15 = refl

  s6-rsp : readReg (regs s6) rsp ≡ init-rsp ∸ 40
  s6-rsp = refl

  -- Instruction 6: mov r14, rdi
  s7 : State
  s7 = record s6
    { regs = writeReg (regs s6) r14 (readReg (regs s6) rdi)
    ; pc = pc s6 +ℕ 1
    }

  step-6 : step prog s6 ≡ just s7
  step-6 = trans (step-exec prog s6 (mov (reg r14) (reg rdi)) s6-halted prog-fetch-6) (execMov-reg-reg s6 r14 rdi)

  s7-halted : halted s7 ≡ false
  s7-halted = refl

  s7-pc : pc s7 ≡ 7
  s7-pc = refl

  -- rdi hasn't been written since s0, so this normalizes
  s7-r14 : readReg (regs s7) r14 ≡ input-val
  s7-r14 = refl

  -- r15 hasn't been written since s6
  s7-r15 : readReg (regs s7) r15 ≡ init-rsp ∸ 40
  s7-r15 = refl

  ------------------------------------------------------------------------
  -- Phase 2: Curry closure creation (instructions 7-12)
  ------------------------------------------------------------------------

  -- Fetch proofs for curry instructions
  prog-fetch-7 : fetch prog 7 ≡ just (sub (reg rsp) (imm 16))
  prog-fetch-7 = refl

  prog-fetch-8 : fetch prog 8 ≡ just (mov (mem (base rsp)) (reg rdi))
  prog-fetch-8 = refl

  prog-fetch-9 : fetch prog 9 ≡ just (lea r9 (rip+disp 4))
  prog-fetch-9 = refl

  prog-fetch-10 : fetch prog 10 ≡ just (mov (mem (base+disp rsp 8)) (reg r9))
  prog-fetch-10 = refl

  prog-fetch-11 : fetch prog 11 ≡ just (mov (reg rax) (reg rsp))
  prog-fetch-11 = refl

  prog-fetch-12 : fetch prog 12 ≡ just (jmp 7)
  prog-fetch-12 = refl

  -- Instruction 7: sub rsp, 16 (allocate closure)
  s8 : State
  s8 = record s7
    { regs = writeReg (regs s7) rsp (readReg (regs s7) rsp ∸ 16)
    ; pc = pc s7 +ℕ 1
    ; flags = updateFlags (readReg (regs s7) rsp ∸ 16) (readReg (regs s7) rsp)
    }

  step-7 : step prog s7 ≡ just s8
  step-7 = trans (step-exec prog s7 (sub (reg rsp) (imm 16)) s7-halted prog-fetch-7) (execSub-reg-imm prog s7 rsp 16)

  s8-halted : halted s8 ≡ false
  s8-halted = refl

  s8-pc : pc s8 ≡ 8
  s8-pc = refl

  s8-rsp : readReg (regs s8) rsp ≡ init-rsp ∸ 56
  s8-rsp = refl

  -- Instruction 8: mov [rsp], rdi (store env = input)
  s9 : State
  s9 = record s8
    { memory = writeMem (memory s8) (readReg (regs s8) rsp) (readReg (regs s8) rdi)
    ; pc = pc s8 +ℕ 1
    }

  step-8 : step prog s8 ≡ just s9
  step-8 = trans (step-exec prog s8 (mov (mem (base rsp)) (reg rdi)) s8-halted prog-fetch-8) (execMov-mem-base-reg prog s8 rsp rdi)

  s9-halted : halted s9 ≡ false
  s9-halted = refl

  s9-pc : pc s9 ≡ 9
  s9-pc = refl

  s9-closure-env : readMem (memory s9) (init-rsp ∸ 56) ≡ just input-val
  s9-closure-env = refl

  -- Instruction 9: lea r9, [rip+4]
  -- effectiveAddr computes pc + 4 = 9 + 4 = 13
  s10 : State
  s10 = record s9
    { regs = writeReg (regs s9) r9 (effectiveAddr s9 (rip+disp 4))
    ; pc = pc s9 +ℕ 1
    }

  step-9 : step prog s9 ≡ just s10
  step-9 = trans (step-exec prog s9 (lea r9 (rip+disp 4)) s9-halted prog-fetch-9) (execLea prog s9 r9 (rip+disp 4))

  s10-halted : halted s10 ≡ false
  s10-halted = refl

  s10-pc : pc s10 ≡ 10
  s10-pc = refl

  s10-r9 : readReg (regs s10) r9 ≡ 13
  s10-r9 = refl

  -- Instruction 10: mov [rsp+8], r9 (store code-ptr)
  s11 : State
  s11 = record s10
    { memory = writeMem (memory s10) (readReg (regs s10) rsp +ℕ 8) (readReg (regs s10) r9)
    ; pc = pc s10 +ℕ 1
    }

  step-10 : step prog s10 ≡ just s11
  step-10 = trans (step-exec prog s10 (mov (mem (base+disp rsp 8)) (reg r9)) s10-halted prog-fetch-10) (execMov-mem-disp-reg prog s10 rsp r9 8)

  s11-halted : halted s11 ≡ false
  s11-halted = refl

  s11-pc : pc s11 ≡ 11
  s11-pc = refl

  s11-closure-ptr : readMem (memory s11) (init-rsp ∸ 56 +ℕ 8) ≡ just 13
  s11-closure-ptr = refl

  -- Instruction 11: mov rax, rsp
  s12 : State
  s12 = record s11
    { regs = writeReg (regs s11) rax (readReg (regs s11) rsp)
    ; pc = pc s11 +ℕ 1
    }

  step-11 : step prog s11 ≡ just s12
  step-11 = trans (step-exec prog s11 (mov (reg rax) (reg rsp)) s11-halted prog-fetch-11) (execMov-reg-reg s11 rax rsp)

  s12-halted : halted s12 ≡ false
  s12-halted = refl

  s12-pc : pc s12 ≡ 12
  s12-pc = refl

  s12-rax : readReg (regs s12) rax ≡ init-rsp ∸ 56
  s12-rax = refl

  -- Instruction 12: jmp 7 (PC-relative: pc = 12+1+7 = 20)
  s13 : State
  s13 = record s12 { pc = pc s12 +ℕ 1 +ℕ 7 }

  step-12 : step prog s12 ≡ just s13
  step-12 = trans (step-exec prog s12 (jmp 7) s12-halted prog-fetch-12) (execJmp prog s12 7)

  s13-halted : halted s13 ≡ false
  s13-halted = refl

  s13-pc : pc s13 ≡ 20
  s13-pc = refl

  ------------------------------------------------------------------------
  -- Phase 3: Complete pairing (instructions 20-29)
  -- Thunk code is at 13-19, but we skip it via jmp
  -- We land at position 20 (end label for curry)
  ------------------------------------------------------------------------

  -- Fetch proofs for Phase 3 instructions
  -- Note: label instruction stores label VALUE (end-label = 12 + 1 = 13), not position
  prog-fetch-20 : fetch prog 20 ≡ just (label 13)
  prog-fetch-20 = refl

  prog-fetch-21 : fetch prog 21 ≡ just (mov (mem (base r15)) (reg rax))
  prog-fetch-21 = refl

  prog-fetch-22 : fetch prog 22 ≡ just (mov (reg rdi) (reg r14))
  prog-fetch-22 = refl

  prog-fetch-23 : fetch prog 23 ≡ just (mov (reg rax) (reg rdi))
  prog-fetch-23 = refl

  prog-fetch-24 : fetch prog 24 ≡ just (mov (mem (base+disp r15 8)) (reg rax))
  prog-fetch-24 = refl

  prog-fetch-25 : fetch prog 25 ≡ just (mov (reg rax) (reg r15))
  prog-fetch-25 = refl

  prog-fetch-26 : fetch prog 26 ≡ just (mov (reg rsp) (reg rbp))
  prog-fetch-26 = refl

  prog-fetch-27 : fetch prog 27 ≡ just (pop rbp)
  prog-fetch-27 = refl

  prog-fetch-28 : fetch prog 28 ≡ just (pop r15)
  prog-fetch-28 = refl

  prog-fetch-29 : fetch prog 29 ≡ just (pop r14)
  prog-fetch-29 = refl

  -- Instruction 20: label 13 (no-op, the end-label for curry)
  s14 : State
  s14 = record s13 { pc = pc s13 +ℕ 1 }

  step-13 : step prog s13 ≡ just s14
  step-13 = trans (step-exec prog s13 (label 13) s13-halted prog-fetch-20) (execLabel prog s13 13)

  s14-halted : halted s14 ≡ false
  s14-halted = refl

  s14-pc : pc s14 ≡ 21
  s14-pc = refl

  -- Track register values in s14 (unchanged from s13 except pc)
  s14-rax : readReg (regs s14) rax ≡ init-rsp ∸ 56
  s14-rax = refl

  s14-r15 : readReg (regs s14) r15 ≡ init-rsp ∸ 40
  s14-r15 = refl

  -- Instruction 21: mov [r15], rax (store closure in pair.fst)
  s15 : State
  s15 = record s14
    { memory = writeMem (memory s14) (readReg (regs s14) r15) (readReg (regs s14) rax)
    ; pc = pc s14 +ℕ 1
    }

  step-14 : step prog s14 ≡ just s15
  step-14 = trans (step-exec prog s14 (mov (mem (base r15)) (reg rax)) s14-halted prog-fetch-21)
                  (execMov-mem-base-reg prog s14 r15 rax)

  s15-halted : halted s15 ≡ false
  s15-halted = refl

  s15-pc : pc s15 ≡ 22
  s15-pc = refl

  s15-pair-fst : readMem (memory s15) (init-rsp ∸ 40) ≡ just (init-rsp ∸ 56)
  s15-pair-fst = refl

  -- Instruction 22: mov rdi, r14 (restore input)
  s16 : State
  s16 = record s15
    { regs = writeReg (regs s15) rdi (readReg (regs s15) r14)
    ; pc = pc s15 +ℕ 1
    }

  step-15 : step prog s15 ≡ just s16
  step-15 = trans (step-exec prog s15 (mov (reg rdi) (reg r14)) s15-halted prog-fetch-22)
                  (execMov-reg-reg s15 rdi r14)

  s16-halted : halted s16 ≡ false
  s16-halted = refl

  s16-pc : pc s16 ≡ 23
  s16-pc = refl

  s16-rdi : readReg (regs s16) rdi ≡ input-val
  s16-rdi = refl

  -- Track r14 in s16 (unchanged from s15)
  s16-r14 : readReg (regs s16) r14 ≡ input-val
  s16-r14 = refl

  -- Instruction 23: mov rax, rdi (compile-x86 id)
  s17 : State
  s17 = record s16
    { regs = writeReg (regs s16) rax (readReg (regs s16) rdi)
    ; pc = pc s16 +ℕ 1
    }

  step-16 : step prog s16 ≡ just s17
  step-16 = trans (step-exec prog s16 (mov (reg rax) (reg rdi)) s16-halted prog-fetch-23)
                  (execMov-reg-reg s16 rax rdi)

  s17-halted : halted s17 ≡ false
  s17-halted = refl

  s17-pc : pc s17 ≡ 24
  s17-pc = refl

  s17-rax : readReg (regs s17) rax ≡ input-val
  s17-rax = refl

  -- Track r15 in s17 for the next memory write
  s17-r15 : readReg (regs s17) r15 ≡ init-rsp ∸ 40
  s17-r15 = refl

  -- Instruction 24: mov [r15+8], rax (store input in pair.snd)
  s18 : State
  s18 = record s17
    { memory = writeMem (memory s17) (readReg (regs s17) r15 +ℕ 8) (readReg (regs s17) rax)
    ; pc = pc s17 +ℕ 1
    }

  step-17 : step prog s17 ≡ just s18
  step-17 = trans (step-exec prog s17 (mov (mem (base+disp r15 8)) (reg rax)) s17-halted prog-fetch-24)
                  (execMov-mem-disp-reg prog s17 r15 rax 8)

  s18-halted : halted s18 ≡ false
  s18-halted = refl

  s18-pc : pc s18 ≡ 25
  s18-pc = refl

  s18-pair-snd : readMem (memory s18) (init-rsp ∸ 40 +ℕ 8) ≡ just input-val
  s18-pair-snd = refl

  -- Track r15 in s18
  s18-r15 : readReg (regs s18) r15 ≡ init-rsp ∸ 40
  s18-r15 = refl

  -- Instruction 25: mov rax, r15 (return pair pointer)
  s19 : State
  s19 = record s18
    { regs = writeReg (regs s18) rax (readReg (regs s18) r15)
    ; pc = pc s18 +ℕ 1
    }

  step-18 : step prog s18 ≡ just s19
  step-18 = trans (step-exec prog s18 (mov (reg rax) (reg r15)) s18-halted prog-fetch-25)
                  (execMov-reg-reg s18 rax r15)

  s19-halted : halted s19 ≡ false
  s19-halted = refl

  s19-pc : pc s19 ≡ 26
  s19-pc = refl

  s19-rax : readReg (regs s19) rax ≡ init-rsp ∸ 40
  s19-rax = refl

  -- Track rbp in s19 for the stack restore
  s19-rbp : readReg (regs s19) rbp ≡ init-rsp ∸ 24
  s19-rbp = refl

  -- Instruction 26: mov rsp, rbp (restore stack via frame pointer)
  s20 : State
  s20 = record s19
    { regs = writeReg (regs s19) rsp (readReg (regs s19) rbp)
    ; pc = pc s19 +ℕ 1
    }

  step-19 : step prog s19 ≡ just s20
  step-19 = trans (step-exec prog s19 (mov (reg rsp) (reg rbp)) s19-halted prog-fetch-26)
                  (execMov-reg-reg s19 rsp rbp)

  s20-halted : halted s20 ≡ false
  s20-halted = refl

  s20-pc : pc s20 ≡ 27
  s20-pc = refl

  -- After mov rsp, rbp: rsp = init-rsp - 24
  s20-rsp : readReg (regs s20) rsp ≡ init-rsp ∸ 24
  s20-rsp = refl

  -- Track rax in s20 (unchanged)
  s20-rax : readReg (regs s20) rax ≡ init-rsp ∸ 40
  s20-rax = refl

  -- Memory at rsp (= init-rsp - 24) contains saved rbp value
  -- We saved the OLD rbp value at position init-rsp - 24
  -- At the time of push rbp, rsp was init-rsp - 16, so we pushed there
  -- After push, rsp became init-rsp - 24
  -- So memory at init-rsp - 24 has the original rbp value (0)
  s20-mem-at-rsp : readMem (memory s20) (init-rsp ∸ 24) ≡ just 0
  s20-mem-at-rsp = refl

  -- Instruction 27: pop rbp
  s21 : State
  s21 = record s20
    { regs = writeReg (writeReg (regs s20) rbp 0) rsp (readReg (regs s20) rsp +ℕ 8)
    ; pc = pc s20 +ℕ 1
    }

  step-20 : step prog s20 ≡ just s21
  step-20 = trans (step-exec prog s20 (pop rbp) s20-halted prog-fetch-27)
                  (execPop prog s20 rbp 0 s20-mem-at-rsp)

  s21-halted : halted s21 ≡ false
  s21-halted = refl

  s21-pc : pc s21 ≡ 28
  s21-pc = refl

  -- After pop rbp: rsp = (init-rsp - 24) + 8 = init-rsp - 16
  s21-rsp : readReg (regs s21) rsp ≡ init-rsp ∸ 16
  s21-rsp = refl

  -- Track rax in s21 (unchanged by pop)
  s21-rax : readReg (regs s21) rax ≡ init-rsp ∸ 40
  s21-rax = refl

  -- Memory at new rsp (= init-rsp - 16) contains saved r15
  -- We saved r15 at position init-rsp - 16 (it was the initial rsp at that point)
  -- r15 was 0 at the start
  s21-mem-at-rsp : readMem (memory s21) (init-rsp ∸ 16) ≡ just 0
  s21-mem-at-rsp = refl

  -- Instruction 28: pop r15
  s22 : State
  s22 = record s21
    { regs = writeReg (writeReg (regs s21) r15 0) rsp (readReg (regs s21) rsp +ℕ 8)
    ; pc = pc s21 +ℕ 1
    }

  step-21 : step prog s21 ≡ just s22
  step-21 = trans (step-exec prog s21 (pop r15) s21-halted prog-fetch-28)
                  (execPop prog s21 r15 0 s21-mem-at-rsp)

  s22-halted : halted s22 ≡ false
  s22-halted = refl

  s22-pc : pc s22 ≡ 29
  s22-pc = refl

  -- After pop r15: rsp = (init-rsp - 16) + 8 = init-rsp - 8
  s22-rsp : readReg (regs s22) rsp ≡ init-rsp ∸ 8
  s22-rsp = refl

  -- Track rax in s22 (unchanged)
  s22-rax : readReg (regs s22) rax ≡ init-rsp ∸ 40
  s22-rax = refl

  -- Memory at new rsp (= init-rsp - 8) contains saved r14
  -- r14 was 0 at the start
  s22-mem-at-rsp : readMem (memory s22) (init-rsp ∸ 8) ≡ just 0
  s22-mem-at-rsp = refl

  -- Instruction 29: pop r14
  s23 : State
  s23 = record s22
    { regs = writeReg (writeReg (regs s22) r14 0) rsp (readReg (regs s22) rsp +ℕ 8)
    ; pc = pc s22 +ℕ 1
    }

  step-22 : step prog s22 ≡ just s23
  step-22 = trans (step-exec prog s22 (pop r14) s22-halted prog-fetch-29)
                  (execPop prog s22 r14 0 s22-mem-at-rsp)

  s23-halted : halted s23 ≡ false
  s23-halted = refl

  s23-pc : pc s23 ≡ 30
  s23-pc = refl

  -- After pop r14: rsp = init-rsp
  s23-rsp : readReg (regs s23) rsp ≡ init-rsp
  s23-rsp = refl

  s23-rax : readReg (regs s23) rax ≡ init-rsp ∸ 40
  s23-rax = refl

  ------------------------------------------------------------------------
  -- Phase 4: Composition connector (instruction 30)
  ------------------------------------------------------------------------

  -- Fetch proof for instruction 30
  prog-fetch-30 : fetch prog 30 ≡ just (mov (reg rdi) (reg rax))
  prog-fetch-30 = refl

  -- Instruction 30: mov rdi, rax (pass pair to apply)
  s24 : State
  s24 = record s23
    { regs = writeReg (regs s23) rdi (readReg (regs s23) rax)
    ; pc = pc s23 +ℕ 1
    }

  step-23 : step prog s23 ≡ just s24
  step-23 = trans (step-exec prog s23 (mov (reg rdi) (reg rax)) s23-halted prog-fetch-30)
                  (execMov-reg-reg s23 rdi rax)

  s24-halted : halted s24 ≡ false
  s24-halted = refl

  s24-pc : pc s24 ≡ 31
  s24-pc = refl

  s24-rdi : readReg (regs s24) rdi ≡ init-rsp ∸ 40
  s24-rdi = refl

  ------------------------------------------------------------------------
  -- Phase 5: Apply (instructions 31-36)
  ------------------------------------------------------------------------

  -- Fetch proofs for apply instructions
  prog-fetch-31 : fetch prog 31 ≡ just (mov (reg r15) (mem (base rdi)))
  prog-fetch-31 = refl

  prog-fetch-32 : fetch prog 32 ≡ just (mov (reg rsi) (mem (base+disp rdi 8)))
  prog-fetch-32 = refl

  prog-fetch-33 : fetch prog 33 ≡ just (mov (reg r12) (mem (base r15)))
  prog-fetch-33 = refl

  prog-fetch-34 : fetch prog 34 ≡ just (mov (reg r15) (mem (base+disp r15 8)))
  prog-fetch-34 = refl

  prog-fetch-35 : fetch prog 35 ≡ just (mov (reg rdi) (reg rsi))
  prog-fetch-35 = refl

  prog-fetch-36 : fetch prog 36 ≡ just (call (reg r15))
  prog-fetch-36 = refl

  -- Memory at pair.fst (init-rsp - 40) contains closure address (init-rsp - 56)
  s24-mem-pair-fst : readMem (memory s24) (init-rsp ∸ 40) ≡ just (init-rsp ∸ 56)
  s24-mem-pair-fst = refl

  -- Instruction 31: mov r15, [rdi] (load closure from pair.fst)
  s25 : State
  s25 = record s24
    { regs = writeReg (regs s24) r15 (init-rsp ∸ 56)
    ; pc = pc s24 +ℕ 1
    }

  step-24 : step prog s24 ≡ just s25
  step-24 = trans (step-exec prog s24 (mov (reg r15) (mem (base rdi))) s24-halted prog-fetch-31)
                  (execMov-reg-mem prog s24 r15 (base rdi) (init-rsp ∸ 56) s24-mem-pair-fst)

  s25-halted : halted s25 ≡ false
  s25-halted = refl

  s25-pc : pc s25 ≡ 32
  s25-pc = refl

  s25-r15 : readReg (regs s25) r15 ≡ init-rsp ∸ 56
  s25-r15 = refl

  -- Memory at pair.snd (init-rsp - 32) contains input-val
  s25-mem-pair-snd : readMem (memory s25) (init-rsp ∸ 40 +ℕ 8) ≡ just input-val
  s25-mem-pair-snd = refl

  -- Instruction 32: mov rsi, [rdi+8] (load argument from pair.snd)
  s26 : State
  s26 = record s25
    { regs = writeReg (regs s25) rsi input-val
    ; pc = pc s25 +ℕ 1
    }

  step-25 : step prog s25 ≡ just s26
  step-25 = trans (step-exec prog s25 (mov (reg rsi) (mem (base+disp rdi 8))) s25-halted prog-fetch-32)
                  (execMov-reg-mem prog s25 rsi (base+disp rdi 8) input-val s25-mem-pair-snd)

  s26-halted : halted s26 ≡ false
  s26-halted = refl

  s26-pc : pc s26 ≡ 33
  s26-pc = refl

  s26-rsi : readReg (regs s26) rsi ≡ input-val
  s26-rsi = refl

  -- Memory at closure.env (init-rsp - 56) contains input-val (saved rdi at curry time)
  s26-mem-closure-env : readMem (memory s26) (init-rsp ∸ 56) ≡ just input-val
  s26-mem-closure-env = refl

  -- Instruction 33: mov r12, [r15] (load env from closure.fst)
  s27 : State
  s27 = record s26
    { regs = writeReg (regs s26) r12 input-val
    ; pc = pc s26 +ℕ 1
    }

  step-26 : step prog s26 ≡ just s27
  step-26 = trans (step-exec prog s26 (mov (reg r12) (mem (base r15))) s26-halted prog-fetch-33)
                  (execMov-reg-mem prog s26 r12 (base r15) input-val s26-mem-closure-env)

  s27-halted : halted s27 ≡ false
  s27-halted = refl

  s27-pc : pc s27 ≡ 34
  s27-pc = refl

  s27-r12 : readReg (regs s27) r12 ≡ input-val
  s27-r12 = refl

  -- Memory at closure.code-ptr (init-rsp - 48) contains 13 (thunk entry)
  s27-mem-closure-ptr : readMem (memory s27) (init-rsp ∸ 56 +ℕ 8) ≡ just 13
  s27-mem-closure-ptr = refl

  -- Instruction 34: mov r15, [r15+8] (load code-ptr from closure.snd)
  s28 : State
  s28 = record s27
    { regs = writeReg (regs s27) r15 13
    ; pc = pc s27 +ℕ 1
    }

  step-27 : step prog s27 ≡ just s28
  step-27 = trans (step-exec prog s27 (mov (reg r15) (mem (base+disp r15 8))) s27-halted prog-fetch-34)
                  (execMov-reg-mem prog s27 r15 (base+disp r15 8) 13 s27-mem-closure-ptr)

  s28-halted : halted s28 ≡ false
  s28-halted = refl

  s28-pc : pc s28 ≡ 35
  s28-pc = refl

  s28-r15 : readReg (regs s28) r15 ≡ 13
  s28-r15 = refl

  -- Track rsi in s28 (unchanged)
  s28-rsi : readReg (regs s28) rsi ≡ input-val
  s28-rsi = refl

  -- Instruction 35: mov rdi, rsi (move argument to rdi)
  s29 : State
  s29 = record s28
    { regs = writeReg (regs s28) rdi (readReg (regs s28) rsi)
    ; pc = pc s28 +ℕ 1
    }

  step-28 : step prog s28 ≡ just s29
  step-28 = trans (step-exec prog s28 (mov (reg rdi) (reg rsi)) s28-halted prog-fetch-35)
                  (execMov-reg-reg s28 rdi rsi)

  s29-halted : halted s29 ≡ false
  s29-halted = refl

  s29-pc : pc s29 ≡ 36
  s29-pc = refl

  s29-rdi : readReg (regs s29) rdi ≡ input-val
  s29-rdi = refl

  s29-r12 : readReg (regs s29) r12 ≡ input-val
  s29-r12 = refl

  s29-r15 : readReg (regs s29) r15 ≡ 13
  s29-r15 = refl

  ------------------------------------------------------------------------
  -- Phase 6: Apply call (instruction 36) - JUMPS TO THUNK!
  ------------------------------------------------------------------------

  -- Instruction 36: call r15 (jumps to position 13 = thunk entry!)
  -- call reads r15 (= 13) and jumps there
  s30 : State
  s30 = record s29 { pc = 13 }

  step-29 : step prog s29 ≡ just s30
  step-29 = trans (step-exec prog s29 (call (reg r15)) s29-halted prog-fetch-36)
                  (execCall-reg prog s29 r15)

  s30-halted : halted s30 ≡ false
  s30-halted = refl

  s30-pc : pc s30 ≡ 13
  s30-pc = refl

  ------------------------------------------------------------------------
  -- Phase 7: Thunk execution (instructions 13-19)
  ------------------------------------------------------------------------

  -- Track rsp, r12, rdi entering thunk
  s30-rsp : readReg (regs s30) rsp ≡ init-rsp
  s30-rsp = refl

  s30-r12 : readReg (regs s30) r12 ≡ input-val
  s30-r12 = refl

  s30-rdi : readReg (regs s30) rdi ≡ input-val
  s30-rdi = refl

  -- Fetch proofs for thunk instructions (positions 13-19)
  prog-fetch-13 : fetch prog 13 ≡ just (label 6)
  prog-fetch-13 = refl

  prog-fetch-14 : fetch prog 14 ≡ just (sub (reg rsp) (imm 16))
  prog-fetch-14 = refl

  prog-fetch-15 : fetch prog 15 ≡ just (mov (mem (base rsp)) (reg r12))
  prog-fetch-15 = refl

  prog-fetch-16 : fetch prog 16 ≡ just (mov (mem (base+disp rsp 8)) (reg rdi))
  prog-fetch-16 = refl

  prog-fetch-17 : fetch prog 17 ≡ just (mov (reg rdi) (reg rsp))
  prog-fetch-17 = refl

  prog-fetch-18 : fetch prog 18 ≡ just (mov (reg rax) (mem (base rdi)))
  prog-fetch-18 = refl

  prog-fetch-19 : fetch prog 19 ≡ just ret
  prog-fetch-19 = refl

  -- Instruction 13: label 6 (thunk entry, no-op)
  s31 : State
  s31 = record s30 { pc = pc s30 +ℕ 1 }

  step-30 : step prog s30 ≡ just s31
  step-30 = trans (step-exec prog s30 (label 6) s30-halted prog-fetch-13) (execLabel prog s30 6)

  s31-halted : halted s31 ≡ false
  s31-halted = refl

  s31-pc : pc s31 ≡ 14
  s31-pc = refl

  -- Track rsp, r12, rdi in s31 (unchanged from s30)
  s31-rsp : readReg (regs s31) rsp ≡ init-rsp
  s31-rsp = refl

  s31-r12 : readReg (regs s31) r12 ≡ input-val
  s31-r12 = refl

  s31-rdi : readReg (regs s31) rdi ≡ input-val
  s31-rdi = refl

  -- Instruction 14: sub rsp, 16 (allocate thunk pair)
  s32 : State
  s32 = record s31
    { regs = writeReg (regs s31) rsp (readReg (regs s31) rsp ∸ 16)
    ; pc = pc s31 +ℕ 1
    ; flags = updateFlags (readReg (regs s31) rsp ∸ 16) (readReg (regs s31) rsp)
    }

  step-31 : step prog s31 ≡ just s32
  step-31 = trans (step-exec prog s31 (sub (reg rsp) (imm 16)) s31-halted prog-fetch-14)
                  (execSub-reg-imm prog s31 rsp 16)

  s32-halted : halted s32 ≡ false
  s32-halted = refl

  s32-pc : pc s32 ≡ 15
  s32-pc = refl

  s32-rsp : readReg (regs s32) rsp ≡ init-rsp ∸ 16
  s32-rsp = refl

  s32-r12 : readReg (regs s32) r12 ≡ input-val
  s32-r12 = refl

  s32-rdi : readReg (regs s32) rdi ≡ input-val
  s32-rdi = refl

  -- Instruction 15: mov [rsp], r12 (store env in pair.fst)
  s33 : State
  s33 = record s32
    { memory = writeMem (memory s32) (readReg (regs s32) rsp) (readReg (regs s32) r12)
    ; pc = pc s32 +ℕ 1
    }

  step-32 : step prog s32 ≡ just s33
  step-32 = trans (step-exec prog s32 (mov (mem (base rsp)) (reg r12)) s32-halted prog-fetch-15)
                  (execMov-mem-base-reg prog s32 rsp r12)

  s33-halted : halted s33 ≡ false
  s33-halted = refl

  s33-pc : pc s33 ≡ 16
  s33-pc = refl

  s33-rsp : readReg (regs s33) rsp ≡ init-rsp ∸ 16
  s33-rsp = refl

  s33-rdi : readReg (regs s33) rdi ≡ input-val
  s33-rdi = refl

  -- Instruction 16: mov [rsp+8], rdi (store arg in pair.snd)
  s34 : State
  s34 = record s33
    { memory = writeMem (memory s33) (readReg (regs s33) rsp +ℕ 8) (readReg (regs s33) rdi)
    ; pc = pc s33 +ℕ 1
    }

  step-33 : step prog s33 ≡ just s34
  step-33 = trans (step-exec prog s33 (mov (mem (base+disp rsp 8)) (reg rdi)) s33-halted prog-fetch-16)
                  (execMov-mem-disp-reg prog s33 rsp rdi 8)

  s34-halted : halted s34 ≡ false
  s34-halted = refl

  s34-pc : pc s34 ≡ 17
  s34-pc = refl

  s34-rsp : readReg (regs s34) rsp ≡ init-rsp ∸ 16
  s34-rsp = refl

  -- Instruction 17: mov rdi, rsp (rdi = pair pointer)
  s35 : State
  s35 = record s34
    { regs = writeReg (regs s34) rdi (readReg (regs s34) rsp)
    ; pc = pc s34 +ℕ 1
    }

  step-34 : step prog s34 ≡ just s35
  step-34 = trans (step-exec prog s34 (mov (reg rdi) (reg rsp)) s34-halted prog-fetch-17)
                  (execMov-reg-reg s34 rdi rsp)

  s35-halted : halted s35 ≡ false
  s35-halted = refl

  s35-pc : pc s35 ≡ 18
  s35-pc = refl

  s35-rdi : readReg (regs s35) rdi ≡ init-rsp ∸ 16
  s35-rdi = refl

  -- Memory at pair.fst (rdi = init-rsp - 16) contains r12 = input-val
  s35-mem-pair-fst : readMem (memory s35) (init-rsp ∸ 16) ≡ just input-val
  s35-mem-pair-fst = refl

  -- Instruction 18: mov rax, [rdi] (fst - loads env = input!)
  s36 : State
  s36 = record s35
    { regs = writeReg (regs s35) rax input-val
    ; pc = pc s35 +ℕ 1
    }

  step-35 : step prog s35 ≡ just s36
  step-35 = trans (step-exec prog s35 (mov (reg rax) (mem (base rdi))) s35-halted prog-fetch-18)
                  (execMov-reg-mem prog s35 rax (base rdi) input-val s35-mem-pair-fst)

  s36-halted : halted s36 ≡ false
  s36-halted = refl

  s36-pc : pc s36 ≡ 19
  s36-pc = refl

  s36-rax : readReg (regs s36) rax ≡ input-val
  s36-rax = refl

  -- Instruction 19: ret (halts execution)
  s-final : State
  s-final = record s36 { halted = true }

  step-36 : step prog s36 ≡ just s-final
  step-36 = trans (step-exec prog s36 ret s36-halted prog-fetch-19) (execRet prog s36)

  s-final-halted : halted s-final ≡ true
  s-final-halted = refl

  s-final-rax : readReg (regs s-final) rax ≡ input-val
  s-final-rax = refl

  ------------------------------------------------------------------------
  -- Final theorem: E2E correctness
  ------------------------------------------------------------------------

  -- Chain all 37 steps together using exec
  -- We need a chain lemma or we build it step by step

  -- Helper: chain two steps
  -- Uses exec-step-helper with h1-false derived from step-implies-not-halted
  exec-chain-2 : ∀ n prog s1 s2 s3 →
    step prog s1 ≡ just s2 →
    halted s2 ≡ false →
    exec n prog s2 ≡ just s3 →
    exec (suc n) prog s1 ≡ just s3
  exec-chain-2 n prog s1 s2 s3 step-eq h2-false exec-eq =
    exec-step-helper h1-false step-eq exec-eq
    where
      h1-false = step-implies-not-halted prog s1 s2 step-eq h2-false

  -- Execute from any halted state: returns immediately
  -- step prog s returns just s when halted s = true (by definition of step)
  exec-halted-gen : ∀ n prog s →
    halted s ≡ true →
    exec n prog s ≡ just s
  exec-halted-gen zero prog s h = refl
  exec-halted-gen (suc n) prog s h with halted s | h
  exec-halted-gen (suc n) prog s refl | true | refl = refl  -- step returns just s, halted is true, done

  -- Helper: chain ending in halted state (for final step)
  -- This is just exec-one-step from ExecLemmas
  exec-chain-halt : ∀ prog s1 s2 →
    step prog s1 ≡ just s2 →
    halted s2 ≡ true →
    exec 1 prog s1 ≡ just s2
  exec-chain-halt prog s1 s2 step-eq h2-true = exec-one-step prog s1 s2 step-eq

  -- Build the chain of 37 execution steps
  -- The individual step proofs above guarantee each step succeeds
  exec-all : exec 37 prog s0 ≡ just s-final
  exec-all =
    exec-chain-2 36 prog s0 s1 s-final step-0 s1-halted
      (exec-chain-2 35 prog s1 s2 s-final step-1 s2-halted
        (exec-chain-2 34 prog s2 s3 s-final step-2 s3-halted
          (exec-chain-2 33 prog s3 s4 s-final step-3 s4-halted
            (exec-chain-2 32 prog s4 s5 s-final step-4 s5-halted
              (exec-chain-2 31 prog s5 s6 s-final step-5 s6-halted
                (exec-chain-2 30 prog s6 s7 s-final step-6 s7-halted
                  (exec-chain-2 29 prog s7 s8 s-final step-7 s8-halted
                    (exec-chain-2 28 prog s8 s9 s-final step-8 s9-halted
                      (exec-chain-2 27 prog s9 s10 s-final step-9 s10-halted
                        (exec-chain-2 26 prog s10 s11 s-final step-10 s11-halted
                          (exec-chain-2 25 prog s11 s12 s-final step-11 s12-halted
                            (exec-chain-2 24 prog s12 s13 s-final step-12 s13-halted
                              (exec-chain-2 23 prog s13 s14 s-final step-13 s14-halted
                                (exec-chain-2 22 prog s14 s15 s-final step-14 s15-halted
                                  (exec-chain-2 21 prog s15 s16 s-final step-15 s16-halted
                                    (exec-chain-2 20 prog s16 s17 s-final step-16 s17-halted
                                      (exec-chain-2 19 prog s17 s18 s-final step-17 s18-halted
                                        (exec-chain-2 18 prog s18 s19 s-final step-18 s19-halted
                                          (exec-chain-2 17 prog s19 s20 s-final step-19 s20-halted
                                            (exec-chain-2 16 prog s20 s21 s-final step-20 s21-halted
                                              (exec-chain-2 15 prog s21 s22 s-final step-21 s22-halted
                                                (exec-chain-2 14 prog s22 s23 s-final step-22 s23-halted
                                                  (exec-chain-2 13 prog s23 s24 s-final step-23 s24-halted
                                                    (exec-chain-2 12 prog s24 s25 s-final step-24 s25-halted
                                                      (exec-chain-2 11 prog s25 s26 s-final step-25 s26-halted
                                                        (exec-chain-2 10 prog s26 s27 s-final step-26 s27-halted
                                                          (exec-chain-2 9 prog s27 s28 s-final step-27 s28-halted
                                                            (exec-chain-2 8 prog s28 s29 s-final step-28 s29-halted
                                                              (exec-chain-2 7 prog s29 s30 s-final step-29 s30-halted
                                                                (exec-chain-2 6 prog s30 s31 s-final step-30 s31-halted
                                                                  (exec-chain-2 5 prog s31 s32 s-final step-31 s32-halted
                                                                    (exec-chain-2 4 prog s32 s33 s-final step-32 s33-halted
                                                                      (exec-chain-2 3 prog s33 s34 s-final step-33 s34-halted
                                                                        (exec-chain-2 2 prog s34 s35 s-final step-34 s35-halted
                                                                          (exec-chain-2 1 prog s35 s36 s-final step-35 s36-halted
                                                                            (exec-chain-halt prog s36 s-final step-36 s-final-halted))))))))))))))))))))))))))))))))))))

  ------------------------------------------------------------------------
  -- Star-based alternative: MUCH cleaner!
  --
  -- Instead of 37 nested exec-chain-2 calls, we just chain steps with ⟨_,_⟩◅_
  -- The Star relation captures multi-step execution without fuel counting.
  ------------------------------------------------------------------------

  star-all : Star prog s0 s-final
  star-all =
    ⟨ s0-halted  , step-0 ⟩◅
    ⟨ s1-halted  , step-1 ⟩◅
    ⟨ s2-halted  , step-2 ⟩◅
    ⟨ s3-halted  , step-3 ⟩◅
    ⟨ s4-halted  , step-4 ⟩◅
    ⟨ s5-halted  , step-5 ⟩◅
    ⟨ s6-halted  , step-6 ⟩◅
    ⟨ s7-halted  , step-7 ⟩◅
    ⟨ s8-halted  , step-8 ⟩◅
    ⟨ s9-halted  , step-9 ⟩◅
    ⟨ s10-halted , step-10 ⟩◅
    ⟨ s11-halted , step-11 ⟩◅
    ⟨ s12-halted , step-12 ⟩◅
    ⟨ s13-halted , step-13 ⟩◅
    ⟨ s14-halted , step-14 ⟩◅
    ⟨ s15-halted , step-15 ⟩◅
    ⟨ s16-halted , step-16 ⟩◅
    ⟨ s17-halted , step-17 ⟩◅
    ⟨ s18-halted , step-18 ⟩◅
    ⟨ s19-halted , step-19 ⟩◅
    ⟨ s20-halted , step-20 ⟩◅
    ⟨ s21-halted , step-21 ⟩◅
    ⟨ s22-halted , step-22 ⟩◅
    ⟨ s23-halted , step-23 ⟩◅
    ⟨ s24-halted , step-24 ⟩◅
    ⟨ s25-halted , step-25 ⟩◅
    ⟨ s26-halted , step-26 ⟩◅
    ⟨ s27-halted , step-27 ⟩◅
    ⟨ s28-halted , step-28 ⟩◅
    ⟨ s29-halted , step-29 ⟩◅
    ⟨ s30-halted , step-30 ⟩◅
    ⟨ s31-halted , step-31 ⟩◅
    ⟨ s32-halted , step-32 ⟩◅
    ⟨ s33-halted , step-33 ⟩◅
    ⟨ s34-halted , step-34 ⟩◅
    ⟨ s35-halted , step-35 ⟩◅
    ⟨ s36-halted , step-36 ⟩◅
    refl*

  -- The main theorem: running the compiled program produces correct result
  e2e-correct : ∃[ s ] (run prog s0 ≡ just s
                      × halted s ≡ true
                      × readReg (regs s) rax ≡ input-val)
  e2e-correct = s-final , run-eq , s-final-halted , s-final-rax
    where
      -- run uses 10000 steps of fuel, which is more than enough for 37 steps
      -- exec 37 prog s0 ≡ just s-final, and s-final is halted
      -- So exec 10000 prog s0 ≡ just s-final as well
      run-eq : run prog s0 ≡ just s-final
      run-eq = exec-extends 37 9963 prog s0 s-final exec-all s-final-halted
        where
          -- Helper: if exec n terminates with halted state, exec (n + m) gives same result
          -- This is exec-halted-extend from the module level
          exec-extends : ∀ n m prog s s' →
            exec n prog s ≡ just s' →
            halted s' ≡ true →
            exec (n +ℕ m) prog s ≡ just s'
          exec-extends = exec-halted-extend

-- End of E2E-Trace module
