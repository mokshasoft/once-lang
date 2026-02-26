------------------------------------------------------------------------
-- Once.Target.X86.ExecLemmas
--
-- Foundation lemmas for x86 execution proofs.
--
-- ARCHITECTURE: Star-based proofs (not fuel-based)
--
-- This module provides lemmas about:
--   1. Register read/write properties
--   2. execInstr behavior for each instruction type
--   3. step behavior (what Star proofs need)
--
-- Star proofs use step directly via star-single/star-trans.
-- No fuel management, no exec postulates needed.
------------------------------------------------------------------------

module Once.Target.X86.ExecLemmas where

open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Data.Empty using (⊥-elim)

open import Once.Target.X86.Syntax as X86
  using (Reg; rax; rbx; rcx; rdx; rsi; rdi; rbp; rsp; r8; r9; r10; r11; r12; r13; r14; r15;
         Mem; base; base+disp;
         Operand; reg; mem; imm;
         Instr; mov; Program; slot-size)

open import Once.Target.X86.Semantics as X86Sem
  using (Word; RegFile; Memory; State; step; step-not-halted;
         execInstr; readOperand; writeOperand; effectiveAddr)
  renaming (readReg to x86-readReg; writeReg to x86-writeReg;
            readMem to x86-readMem; writeMem to x86-writeMem)

open import Once.CCC.Fetch using (fetch; fetch-0; fetch-append-right)

-- Import Star relation for execution proofs
open import Once.CCC.Target.X86.Correct.Star using (Star; star-single)

------------------------------------------------------------------------
-- Register Read/Write Properties
------------------------------------------------------------------------

-- | Reading after writing same register returns the written value
-- This is definitional for each register (pattern matching on Reg)
readReg-writeReg-same : ∀ (rf : RegFile) (r : Reg) (v : Word) →
  x86-readReg (x86-writeReg rf r v) r ≡ v
readReg-writeReg-same rf rax v = refl
readReg-writeReg-same rf rbx v = refl
readReg-writeReg-same rf rcx v = refl
readReg-writeReg-same rf rdx v = refl
readReg-writeReg-same rf rsi v = refl
readReg-writeReg-same rf rdi v = refl
readReg-writeReg-same rf rbp v = refl
readReg-writeReg-same rf rsp v = refl
readReg-writeReg-same rf r8  v = refl
readReg-writeReg-same rf r9  v = refl
readReg-writeReg-same rf r10 v = refl
readReg-writeReg-same rf r11 v = refl
readReg-writeReg-same rf r12 v = refl
readReg-writeReg-same rf r13 v = refl
readReg-writeReg-same rf r14 v = refl
readReg-writeReg-same rf r15 v = refl

-- | Writing to one register preserves another register's value
-- Pattern match on both registers: 16×16 = 256 cases
-- Diagonal cases (r₁ = r₂) are impossible, off-diagonal are refl
readReg-writeReg-diff : ∀ (rf : RegFile) (r₁ r₂ : Reg) (v : Word) →
  r₁ ≢ r₂ →
  x86-readReg (x86-writeReg rf r₁ v) r₂ ≡ x86-readReg rf r₂
-- rax as destination
readReg-writeReg-diff rf rax rax v neq = ⊥-elim (neq refl)
readReg-writeReg-diff rf rax rbx v neq = refl
readReg-writeReg-diff rf rax rcx v neq = refl
readReg-writeReg-diff rf rax rdx v neq = refl
readReg-writeReg-diff rf rax rsi v neq = refl
readReg-writeReg-diff rf rax rdi v neq = refl
readReg-writeReg-diff rf rax rbp v neq = refl
readReg-writeReg-diff rf rax rsp v neq = refl
readReg-writeReg-diff rf rax r8  v neq = refl
readReg-writeReg-diff rf rax r9  v neq = refl
readReg-writeReg-diff rf rax r10 v neq = refl
readReg-writeReg-diff rf rax r11 v neq = refl
readReg-writeReg-diff rf rax r12 v neq = refl
readReg-writeReg-diff rf rax r13 v neq = refl
readReg-writeReg-diff rf rax r14 v neq = refl
readReg-writeReg-diff rf rax r15 v neq = refl
-- rbx as destination
readReg-writeReg-diff rf rbx rax v neq = refl
readReg-writeReg-diff rf rbx rbx v neq = ⊥-elim (neq refl)
readReg-writeReg-diff rf rbx rcx v neq = refl
readReg-writeReg-diff rf rbx rdx v neq = refl
readReg-writeReg-diff rf rbx rsi v neq = refl
readReg-writeReg-diff rf rbx rdi v neq = refl
readReg-writeReg-diff rf rbx rbp v neq = refl
readReg-writeReg-diff rf rbx rsp v neq = refl
readReg-writeReg-diff rf rbx r8  v neq = refl
readReg-writeReg-diff rf rbx r9  v neq = refl
readReg-writeReg-diff rf rbx r10 v neq = refl
readReg-writeReg-diff rf rbx r11 v neq = refl
readReg-writeReg-diff rf rbx r12 v neq = refl
readReg-writeReg-diff rf rbx r13 v neq = refl
readReg-writeReg-diff rf rbx r14 v neq = refl
readReg-writeReg-diff rf rbx r15 v neq = refl
-- rcx as destination
readReg-writeReg-diff rf rcx rax v neq = refl
readReg-writeReg-diff rf rcx rbx v neq = refl
readReg-writeReg-diff rf rcx rcx v neq = ⊥-elim (neq refl)
readReg-writeReg-diff rf rcx rdx v neq = refl
readReg-writeReg-diff rf rcx rsi v neq = refl
readReg-writeReg-diff rf rcx rdi v neq = refl
readReg-writeReg-diff rf rcx rbp v neq = refl
readReg-writeReg-diff rf rcx rsp v neq = refl
readReg-writeReg-diff rf rcx r8  v neq = refl
readReg-writeReg-diff rf rcx r9  v neq = refl
readReg-writeReg-diff rf rcx r10 v neq = refl
readReg-writeReg-diff rf rcx r11 v neq = refl
readReg-writeReg-diff rf rcx r12 v neq = refl
readReg-writeReg-diff rf rcx r13 v neq = refl
readReg-writeReg-diff rf rcx r14 v neq = refl
readReg-writeReg-diff rf rcx r15 v neq = refl
-- rdx as destination
readReg-writeReg-diff rf rdx rax v neq = refl
readReg-writeReg-diff rf rdx rbx v neq = refl
readReg-writeReg-diff rf rdx rcx v neq = refl
readReg-writeReg-diff rf rdx rdx v neq = ⊥-elim (neq refl)
readReg-writeReg-diff rf rdx rsi v neq = refl
readReg-writeReg-diff rf rdx rdi v neq = refl
readReg-writeReg-diff rf rdx rbp v neq = refl
readReg-writeReg-diff rf rdx rsp v neq = refl
readReg-writeReg-diff rf rdx r8  v neq = refl
readReg-writeReg-diff rf rdx r9  v neq = refl
readReg-writeReg-diff rf rdx r10 v neq = refl
readReg-writeReg-diff rf rdx r11 v neq = refl
readReg-writeReg-diff rf rdx r12 v neq = refl
readReg-writeReg-diff rf rdx r13 v neq = refl
readReg-writeReg-diff rf rdx r14 v neq = refl
readReg-writeReg-diff rf rdx r15 v neq = refl
-- rsi as destination
readReg-writeReg-diff rf rsi rax v neq = refl
readReg-writeReg-diff rf rsi rbx v neq = refl
readReg-writeReg-diff rf rsi rcx v neq = refl
readReg-writeReg-diff rf rsi rdx v neq = refl
readReg-writeReg-diff rf rsi rsi v neq = ⊥-elim (neq refl)
readReg-writeReg-diff rf rsi rdi v neq = refl
readReg-writeReg-diff rf rsi rbp v neq = refl
readReg-writeReg-diff rf rsi rsp v neq = refl
readReg-writeReg-diff rf rsi r8  v neq = refl
readReg-writeReg-diff rf rsi r9  v neq = refl
readReg-writeReg-diff rf rsi r10 v neq = refl
readReg-writeReg-diff rf rsi r11 v neq = refl
readReg-writeReg-diff rf rsi r12 v neq = refl
readReg-writeReg-diff rf rsi r13 v neq = refl
readReg-writeReg-diff rf rsi r14 v neq = refl
readReg-writeReg-diff rf rsi r15 v neq = refl
-- rdi as destination
readReg-writeReg-diff rf rdi rax v neq = refl
readReg-writeReg-diff rf rdi rbx v neq = refl
readReg-writeReg-diff rf rdi rcx v neq = refl
readReg-writeReg-diff rf rdi rdx v neq = refl
readReg-writeReg-diff rf rdi rsi v neq = refl
readReg-writeReg-diff rf rdi rdi v neq = ⊥-elim (neq refl)
readReg-writeReg-diff rf rdi rbp v neq = refl
readReg-writeReg-diff rf rdi rsp v neq = refl
readReg-writeReg-diff rf rdi r8  v neq = refl
readReg-writeReg-diff rf rdi r9  v neq = refl
readReg-writeReg-diff rf rdi r10 v neq = refl
readReg-writeReg-diff rf rdi r11 v neq = refl
readReg-writeReg-diff rf rdi r12 v neq = refl
readReg-writeReg-diff rf rdi r13 v neq = refl
readReg-writeReg-diff rf rdi r14 v neq = refl
readReg-writeReg-diff rf rdi r15 v neq = refl
-- rbp as destination
readReg-writeReg-diff rf rbp rax v neq = refl
readReg-writeReg-diff rf rbp rbx v neq = refl
readReg-writeReg-diff rf rbp rcx v neq = refl
readReg-writeReg-diff rf rbp rdx v neq = refl
readReg-writeReg-diff rf rbp rsi v neq = refl
readReg-writeReg-diff rf rbp rdi v neq = refl
readReg-writeReg-diff rf rbp rbp v neq = ⊥-elim (neq refl)
readReg-writeReg-diff rf rbp rsp v neq = refl
readReg-writeReg-diff rf rbp r8  v neq = refl
readReg-writeReg-diff rf rbp r9  v neq = refl
readReg-writeReg-diff rf rbp r10 v neq = refl
readReg-writeReg-diff rf rbp r11 v neq = refl
readReg-writeReg-diff rf rbp r12 v neq = refl
readReg-writeReg-diff rf rbp r13 v neq = refl
readReg-writeReg-diff rf rbp r14 v neq = refl
readReg-writeReg-diff rf rbp r15 v neq = refl
-- rsp as destination
readReg-writeReg-diff rf rsp rax v neq = refl
readReg-writeReg-diff rf rsp rbx v neq = refl
readReg-writeReg-diff rf rsp rcx v neq = refl
readReg-writeReg-diff rf rsp rdx v neq = refl
readReg-writeReg-diff rf rsp rsi v neq = refl
readReg-writeReg-diff rf rsp rdi v neq = refl
readReg-writeReg-diff rf rsp rbp v neq = refl
readReg-writeReg-diff rf rsp rsp v neq = ⊥-elim (neq refl)
readReg-writeReg-diff rf rsp r8  v neq = refl
readReg-writeReg-diff rf rsp r9  v neq = refl
readReg-writeReg-diff rf rsp r10 v neq = refl
readReg-writeReg-diff rf rsp r11 v neq = refl
readReg-writeReg-diff rf rsp r12 v neq = refl
readReg-writeReg-diff rf rsp r13 v neq = refl
readReg-writeReg-diff rf rsp r14 v neq = refl
readReg-writeReg-diff rf rsp r15 v neq = refl
-- r8 as destination
readReg-writeReg-diff rf r8 rax v neq = refl
readReg-writeReg-diff rf r8 rbx v neq = refl
readReg-writeReg-diff rf r8 rcx v neq = refl
readReg-writeReg-diff rf r8 rdx v neq = refl
readReg-writeReg-diff rf r8 rsi v neq = refl
readReg-writeReg-diff rf r8 rdi v neq = refl
readReg-writeReg-diff rf r8 rbp v neq = refl
readReg-writeReg-diff rf r8 rsp v neq = refl
readReg-writeReg-diff rf r8 r8  v neq = ⊥-elim (neq refl)
readReg-writeReg-diff rf r8 r9  v neq = refl
readReg-writeReg-diff rf r8 r10 v neq = refl
readReg-writeReg-diff rf r8 r11 v neq = refl
readReg-writeReg-diff rf r8 r12 v neq = refl
readReg-writeReg-diff rf r8 r13 v neq = refl
readReg-writeReg-diff rf r8 r14 v neq = refl
readReg-writeReg-diff rf r8 r15 v neq = refl
-- r9 as destination
readReg-writeReg-diff rf r9 rax v neq = refl
readReg-writeReg-diff rf r9 rbx v neq = refl
readReg-writeReg-diff rf r9 rcx v neq = refl
readReg-writeReg-diff rf r9 rdx v neq = refl
readReg-writeReg-diff rf r9 rsi v neq = refl
readReg-writeReg-diff rf r9 rdi v neq = refl
readReg-writeReg-diff rf r9 rbp v neq = refl
readReg-writeReg-diff rf r9 rsp v neq = refl
readReg-writeReg-diff rf r9 r8  v neq = refl
readReg-writeReg-diff rf r9 r9  v neq = ⊥-elim (neq refl)
readReg-writeReg-diff rf r9 r10 v neq = refl
readReg-writeReg-diff rf r9 r11 v neq = refl
readReg-writeReg-diff rf r9 r12 v neq = refl
readReg-writeReg-diff rf r9 r13 v neq = refl
readReg-writeReg-diff rf r9 r14 v neq = refl
readReg-writeReg-diff rf r9 r15 v neq = refl
-- r10 as destination
readReg-writeReg-diff rf r10 rax v neq = refl
readReg-writeReg-diff rf r10 rbx v neq = refl
readReg-writeReg-diff rf r10 rcx v neq = refl
readReg-writeReg-diff rf r10 rdx v neq = refl
readReg-writeReg-diff rf r10 rsi v neq = refl
readReg-writeReg-diff rf r10 rdi v neq = refl
readReg-writeReg-diff rf r10 rbp v neq = refl
readReg-writeReg-diff rf r10 rsp v neq = refl
readReg-writeReg-diff rf r10 r8  v neq = refl
readReg-writeReg-diff rf r10 r9  v neq = refl
readReg-writeReg-diff rf r10 r10 v neq = ⊥-elim (neq refl)
readReg-writeReg-diff rf r10 r11 v neq = refl
readReg-writeReg-diff rf r10 r12 v neq = refl
readReg-writeReg-diff rf r10 r13 v neq = refl
readReg-writeReg-diff rf r10 r14 v neq = refl
readReg-writeReg-diff rf r10 r15 v neq = refl
-- r11 as destination
readReg-writeReg-diff rf r11 rax v neq = refl
readReg-writeReg-diff rf r11 rbx v neq = refl
readReg-writeReg-diff rf r11 rcx v neq = refl
readReg-writeReg-diff rf r11 rdx v neq = refl
readReg-writeReg-diff rf r11 rsi v neq = refl
readReg-writeReg-diff rf r11 rdi v neq = refl
readReg-writeReg-diff rf r11 rbp v neq = refl
readReg-writeReg-diff rf r11 rsp v neq = refl
readReg-writeReg-diff rf r11 r8  v neq = refl
readReg-writeReg-diff rf r11 r9  v neq = refl
readReg-writeReg-diff rf r11 r10 v neq = refl
readReg-writeReg-diff rf r11 r11 v neq = ⊥-elim (neq refl)
readReg-writeReg-diff rf r11 r12 v neq = refl
readReg-writeReg-diff rf r11 r13 v neq = refl
readReg-writeReg-diff rf r11 r14 v neq = refl
readReg-writeReg-diff rf r11 r15 v neq = refl
-- r12 as destination
readReg-writeReg-diff rf r12 rax v neq = refl
readReg-writeReg-diff rf r12 rbx v neq = refl
readReg-writeReg-diff rf r12 rcx v neq = refl
readReg-writeReg-diff rf r12 rdx v neq = refl
readReg-writeReg-diff rf r12 rsi v neq = refl
readReg-writeReg-diff rf r12 rdi v neq = refl
readReg-writeReg-diff rf r12 rbp v neq = refl
readReg-writeReg-diff rf r12 rsp v neq = refl
readReg-writeReg-diff rf r12 r8  v neq = refl
readReg-writeReg-diff rf r12 r9  v neq = refl
readReg-writeReg-diff rf r12 r10 v neq = refl
readReg-writeReg-diff rf r12 r11 v neq = refl
readReg-writeReg-diff rf r12 r12 v neq = ⊥-elim (neq refl)
readReg-writeReg-diff rf r12 r13 v neq = refl
readReg-writeReg-diff rf r12 r14 v neq = refl
readReg-writeReg-diff rf r12 r15 v neq = refl
-- r13 as destination
readReg-writeReg-diff rf r13 rax v neq = refl
readReg-writeReg-diff rf r13 rbx v neq = refl
readReg-writeReg-diff rf r13 rcx v neq = refl
readReg-writeReg-diff rf r13 rdx v neq = refl
readReg-writeReg-diff rf r13 rsi v neq = refl
readReg-writeReg-diff rf r13 rdi v neq = refl
readReg-writeReg-diff rf r13 rbp v neq = refl
readReg-writeReg-diff rf r13 rsp v neq = refl
readReg-writeReg-diff rf r13 r8  v neq = refl
readReg-writeReg-diff rf r13 r9  v neq = refl
readReg-writeReg-diff rf r13 r10 v neq = refl
readReg-writeReg-diff rf r13 r11 v neq = refl
readReg-writeReg-diff rf r13 r12 v neq = refl
readReg-writeReg-diff rf r13 r13 v neq = ⊥-elim (neq refl)
readReg-writeReg-diff rf r13 r14 v neq = refl
readReg-writeReg-diff rf r13 r15 v neq = refl
-- r14 as destination
readReg-writeReg-diff rf r14 rax v neq = refl
readReg-writeReg-diff rf r14 rbx v neq = refl
readReg-writeReg-diff rf r14 rcx v neq = refl
readReg-writeReg-diff rf r14 rdx v neq = refl
readReg-writeReg-diff rf r14 rsi v neq = refl
readReg-writeReg-diff rf r14 rdi v neq = refl
readReg-writeReg-diff rf r14 rbp v neq = refl
readReg-writeReg-diff rf r14 rsp v neq = refl
readReg-writeReg-diff rf r14 r8  v neq = refl
readReg-writeReg-diff rf r14 r9  v neq = refl
readReg-writeReg-diff rf r14 r10 v neq = refl
readReg-writeReg-diff rf r14 r11 v neq = refl
readReg-writeReg-diff rf r14 r12 v neq = refl
readReg-writeReg-diff rf r14 r13 v neq = refl
readReg-writeReg-diff rf r14 r14 v neq = ⊥-elim (neq refl)
readReg-writeReg-diff rf r14 r15 v neq = refl
-- r15 as destination
readReg-writeReg-diff rf r15 rax v neq = refl
readReg-writeReg-diff rf r15 rbx v neq = refl
readReg-writeReg-diff rf r15 rcx v neq = refl
readReg-writeReg-diff rf r15 rdx v neq = refl
readReg-writeReg-diff rf r15 rsi v neq = refl
readReg-writeReg-diff rf r15 rdi v neq = refl
readReg-writeReg-diff rf r15 rbp v neq = refl
readReg-writeReg-diff rf r15 rsp v neq = refl
readReg-writeReg-diff rf r15 r8  v neq = refl
readReg-writeReg-diff rf r15 r9  v neq = refl
readReg-writeReg-diff rf r15 r10 v neq = refl
readReg-writeReg-diff rf r15 r11 v neq = refl
readReg-writeReg-diff rf r15 r12 v neq = refl
readReg-writeReg-diff rf r15 r13 v neq = refl
readReg-writeReg-diff rf r15 r14 v neq = refl
readReg-writeReg-diff rf r15 r15 v neq = ⊥-elim (neq refl)

------------------------------------------------------------------------
-- execInstr Lemmas
--
-- These prove what each instruction does to the state.
-- Star proofs use these via step-fetch-result.
------------------------------------------------------------------------

-- | mov from register to register effect
mov-reg-reg-result : ∀ (prog : Program) (s : State) (dst src : Reg) →
  execInstr prog s (mov (reg dst) (reg src)) ≡
  just (record s { regs = x86-writeReg (X86Sem.State.regs s) dst (x86-readReg (X86Sem.State.regs s) src)
                 ; pc = X86Sem.State.pc s +ℕ 1 })
mov-reg-reg-result prog s dst src = refl

-- | mov from immediate to register effect
mov-imm-reg-result : ∀ (prog : Program) (s : State) (dst : Reg) (n : ℕ) →
  execInstr prog s (mov (reg dst) (imm n)) ≡
  just (record s { regs = x86-writeReg (X86Sem.State.regs s) dst n
                 ; pc = X86Sem.State.pc s +ℕ 1 })
mov-imm-reg-result prog s dst n = refl

-- | mov from memory to register effect (when memory read succeeds)
mov-mem-reg-result : ∀ (prog : Program) (s : State) (dst : Reg) (m : Mem) (v : Word) →
  x86-readMem (X86Sem.State.memory s) (effectiveAddr s m) ≡ just v →
  execInstr prog s (mov (reg dst) (mem m)) ≡
  just (record s { regs = x86-writeReg (X86Sem.State.regs s) dst v
                 ; pc = X86Sem.State.pc s +ℕ 1 })
mov-mem-reg-result prog s dst m v mem-eq rewrite mem-eq = refl

------------------------------------------------------------------------
-- step Lemmas
--
-- These connect fetch + execInstr to step.
-- Star proofs need: step prog s ≡ just s'
------------------------------------------------------------------------

-- | step when halted = false and fetch succeeds
-- This is THE key lemma for Star proofs.
step-fetch-result : ∀ (prog : Program) (s : State) (instr : Instr) →
  X86Sem.State.halted s ≡ false →
  fetch prog (X86Sem.State.pc s) ≡ just instr →
  step prog s ≡ execInstr prog s instr
step-fetch-result prog s instr h-eq f-eq with X86Sem.State.halted s
step-fetch-result prog s instr refl f-eq | false with fetch prog (X86Sem.State.pc s)
step-fetch-result prog s instr refl refl | false | just .instr = refl

------------------------------------------------------------------------
-- Single-Instruction Step Results
--
-- For each simple IR, prove: step prog s ≡ just s'
-- These feed directly into star-single for Star proofs.
------------------------------------------------------------------------

-- | Expected state after mov rax, rdi
id-expected-state : State → State
id-expected-state s = record s
  { regs = x86-writeReg (X86Sem.State.regs s) rax (x86-readReg (X86Sem.State.regs s) rdi)
  ; pc = X86Sem.State.pc s +ℕ 1 }

-- | id-instrs = [mov rax, rdi]
id-instrs : Program
id-instrs = mov (reg rax) (reg rdi) ∷ []

-- | step on id-instrs produces the expected state
-- USE: star-single h-false (step-id s h-eq pc-eq)
step-id : ∀ (s : State) →
  X86Sem.State.halted s ≡ false →
  X86Sem.State.pc s ≡ 0 →
  step id-instrs s ≡ just (id-expected-state s)
step-id s h-eq pc-eq =
  let fetch-eq : fetch id-instrs (X86Sem.State.pc s) ≡ just (mov (reg rax) (reg rdi))
      fetch-eq = subst (λ n → fetch id-instrs n ≡ just (mov (reg rax) (reg rdi))) (sym pc-eq) refl
  in trans (step-fetch-result id-instrs s (mov (reg rax) (reg rdi)) h-eq fetch-eq)
           (mov-reg-reg-result id-instrs s rax rdi)

-- | rax after id contains what was in rdi
id-rax-result : ∀ (s : State) →
  x86-readReg (X86Sem.State.regs (id-expected-state s)) rax ≡
  x86-readReg (X86Sem.State.regs s) rdi
id-rax-result s = readReg-writeReg-same (X86Sem.State.regs s) rax
                    (x86-readReg (X86Sem.State.regs s) rdi)

------------------------------------------------------------------------
-- terminal: mov rax, 0
------------------------------------------------------------------------

terminal-expected-state : State → State
terminal-expected-state s = record s
  { regs = x86-writeReg (X86Sem.State.regs s) rax 0
  ; pc = X86Sem.State.pc s +ℕ 1 }

terminal-instrs : Program
terminal-instrs = mov (reg rax) (imm 0) ∷ []

step-terminal : ∀ (s : State) →
  X86Sem.State.halted s ≡ false →
  X86Sem.State.pc s ≡ 0 →
  step terminal-instrs s ≡ just (terminal-expected-state s)
step-terminal s h-eq pc-eq =
  let fetch-eq : fetch terminal-instrs (X86Sem.State.pc s) ≡ just (mov (reg rax) (imm 0))
      fetch-eq = subst (λ n → fetch terminal-instrs n ≡ just (mov (reg rax) (imm 0))) (sym pc-eq) refl
  in trans (step-fetch-result terminal-instrs s (mov (reg rax) (imm 0)) h-eq fetch-eq)
           (mov-imm-reg-result terminal-instrs s rax 0)

terminal-rax-result : ∀ (s : State) →
  x86-readReg (X86Sem.State.regs (terminal-expected-state s)) rax ≡ 0
terminal-rax-result s = readReg-writeReg-same (X86Sem.State.regs s) rax 0

------------------------------------------------------------------------
-- fst: mov rax, [rdi]
------------------------------------------------------------------------

fst-instrs : Program
fst-instrs = mov (reg rax) (mem (base rdi)) ∷ []

fst-expected-state : State → Word → State
fst-expected-state s v = record s
  { regs = x86-writeReg (X86Sem.State.regs s) rax v
  ; pc = X86Sem.State.pc s +ℕ 1 }

step-fst : ∀ (s : State) (v : Word) →
  X86Sem.State.halted s ≡ false →
  X86Sem.State.pc s ≡ 0 →
  x86-readMem (X86Sem.State.memory s) (x86-readReg (X86Sem.State.regs s) rdi) ≡ just v →
  step fst-instrs s ≡ just (fst-expected-state s v)
step-fst s v h-eq pc-eq mem-eq =
  let fetch-eq : fetch fst-instrs (X86Sem.State.pc s) ≡ just (mov (reg rax) (mem (base rdi)))
      fetch-eq = subst (λ n → fetch fst-instrs n ≡ just (mov (reg rax) (mem (base rdi)))) (sym pc-eq) refl
  in trans (step-fetch-result fst-instrs s (mov (reg rax) (mem (base rdi))) h-eq fetch-eq)
           (mov-mem-reg-result fst-instrs s rax (base rdi) v mem-eq)

fst-rax-result : ∀ (s : State) (v : Word) →
  x86-readReg (X86Sem.State.regs (fst-expected-state s v)) rax ≡ v
fst-rax-result s v = readReg-writeReg-same (X86Sem.State.regs s) rax v

------------------------------------------------------------------------
-- snd: mov rax, [rdi + 8]
------------------------------------------------------------------------

snd-instrs : Program
snd-instrs = mov (reg rax) (mem (base+disp rdi slot-size)) ∷ []

snd-expected-state : State → Word → State
snd-expected-state s v = record s
  { regs = x86-writeReg (X86Sem.State.regs s) rax v
  ; pc = X86Sem.State.pc s +ℕ 1 }

step-snd : ∀ (s : State) (v : Word) →
  X86Sem.State.halted s ≡ false →
  X86Sem.State.pc s ≡ 0 →
  x86-readMem (X86Sem.State.memory s) (x86-readReg (X86Sem.State.regs s) rdi +ℕ slot-size) ≡ just v →
  step snd-instrs s ≡ just (snd-expected-state s v)
step-snd s v h-eq pc-eq mem-eq =
  let fetch-eq : fetch snd-instrs (X86Sem.State.pc s) ≡ just (mov (reg rax) (mem (base+disp rdi slot-size)))
      fetch-eq = subst (λ n → fetch snd-instrs n ≡ just (mov (reg rax) (mem (base+disp rdi slot-size)))) (sym pc-eq) refl
  in trans (step-fetch-result snd-instrs s (mov (reg rax) (mem (base+disp rdi slot-size))) h-eq fetch-eq)
           (mov-mem-reg-result snd-instrs s rax (base+disp rdi slot-size) v mem-eq)

snd-rax-result : ∀ (s : State) (v : Word) →
  x86-readReg (X86Sem.State.regs (snd-expected-state s v)) rax ≡ v
snd-rax-result s v = readReg-writeReg-same (X86Sem.State.regs s) rax v

------------------------------------------------------------------------
-- compose-bridge: mov rdi, rax
--
-- This transfers the result of f (in rax) to rdi for g.
------------------------------------------------------------------------

compose-bridge : Program
compose-bridge = mov (reg rdi) (reg rax) ∷ []

-- | Expected state after mov rdi, rax
bridge-expected-state : State → State
bridge-expected-state s = record s
  { regs = x86-writeReg (X86Sem.State.regs s) rdi (x86-readReg (X86Sem.State.regs s) rax)
  ; pc = X86Sem.State.pc s +ℕ 1 }

-- | step on compose-bridge
step-bridge : ∀ (s : State) →
  X86Sem.State.halted s ≡ false →
  X86Sem.State.pc s ≡ 0 →
  step compose-bridge s ≡ just (bridge-expected-state s)
step-bridge s h-eq pc-eq =
  let fetch-eq : fetch compose-bridge (X86Sem.State.pc s) ≡ just (mov (reg rdi) (reg rax))
      fetch-eq = subst (λ n → fetch compose-bridge n ≡ just (mov (reg rdi) (reg rax))) (sym pc-eq) refl
  in trans (step-fetch-result compose-bridge s (mov (reg rdi) (reg rax)) h-eq fetch-eq)
           (mov-reg-reg-result compose-bridge s rdi rax)

-- | rdi after bridge contains what was in rax
bridge-rdi-result : ∀ (s : State) →
  x86-readReg (X86Sem.State.regs (bridge-expected-state s)) rdi ≡
  x86-readReg (X86Sem.State.regs s) rax
bridge-rdi-result s = readReg-writeReg-same (X86Sem.State.regs s) rdi
                        (x86-readReg (X86Sem.State.regs s) rax)

------------------------------------------------------------------------
-- Generalized Step Lemmas (for concatenated programs)
--
-- These lemmas work at any PC position where fetch succeeds.
-- Essential for compose proofs where PC ≠ 0.
------------------------------------------------------------------------

-- | General step lemma: if fetch returns an instruction, step executes it
-- This is step-fetch-result repackaged for direct use
step-at-fetch : ∀ (prog : Program) (s : State) (instr : Instr) (s' : State) →
  X86Sem.State.halted s ≡ false →
  fetch prog (X86Sem.State.pc s) ≡ just instr →
  execInstr prog s instr ≡ just s' →
  step prog s ≡ just s'
step-at-fetch prog s instr s' h-eq f-eq exec-eq =
  trans (step-fetch-result prog s instr h-eq f-eq) exec-eq

-- | Fetch from concatenated program: left part
fetch-++ : ∀ (prog1 prog2 : Program) (n : ℕ) (instr : Instr) →
  fetch prog1 n ≡ just instr →
  fetch (prog1 ++ prog2) n ≡ just instr
fetch-++ [] prog2 n instr ()
fetch-++ (i ∷ prog1) prog2 zero .i refl = refl
fetch-++ (i ∷ prog1) prog2 (suc n) instr eq = fetch-++ prog1 prog2 n instr eq

-- | Fetch from concatenated program: right part (needs offset)
-- fetch (prog1 ++ prog2) (length prog1 + n) = fetch prog2 n
fetch-++-right : ∀ (prog1 prog2 : Program) (n : ℕ) (instr : Instr) →
  fetch prog2 n ≡ just instr →
  fetch (prog1 ++ prog2) (length prog1 +ℕ n) ≡ just instr
fetch-++-right prog1 prog2 n instr eq = trans (fetch-append-right prog1 prog2 n) eq

------------------------------------------------------------------------
-- Compose Star Proof
--
-- For (g ∘ f), we execute: compile-ir f ++ compose-bridge ++ compile-ir g
--
-- The proof chains three Star relations using star-trans.
------------------------------------------------------------------------

-- Import star-trans for chaining
open import Once.CCC.Target.X86.Correct.Star using (star-trans; _◅◅_)

-- | Compose Star proof for id ∘ id (simplest case)
-- Program: [mov rax, rdi] ++ [mov rdi, rax] ++ [mov rax, rdi]
-- Steps: rax←rdi, rdi←rax, rax←rdi
-- Net effect: rax = rdi (identity)

-- Expected state after full compose
compose-id-id-expected : State → State
compose-id-id-expected s = record s
  { regs = x86-writeReg
            (x86-writeReg
              (x86-writeReg (X86Sem.State.regs s) rax (x86-readReg (X86Sem.State.regs s) rdi))
              rdi (x86-readReg (X86Sem.State.regs s) rdi))  -- after bridge: rdi = rax = original rdi
            rax (x86-readReg (X86Sem.State.regs s) rdi)     -- after second id: rax = rdi = original rdi
  ; pc = X86Sem.State.pc s +ℕ 3 }

-- Intermediate states
private
  s1-id : State → State
  s1-id s = record s
    { regs = x86-writeReg (X86Sem.State.regs s) rax (x86-readReg (X86Sem.State.regs s) rdi)
    ; pc = X86Sem.State.pc s +ℕ 1 }

  s2-bridge : State → State
  s2-bridge s =
    let s1 = s1-id s
    in record s1
      { regs = x86-writeReg (X86Sem.State.regs s1) rdi (x86-readReg (X86Sem.State.regs s1) rax)
      ; pc = X86Sem.State.pc s1 +ℕ 1 }

  s3-id : State → State
  s3-id s =
    let s2 = s2-bridge s
    in record s2
      { regs = x86-writeReg (X86Sem.State.regs s2) rax (x86-readReg (X86Sem.State.regs s2) rdi)
      ; pc = X86Sem.State.pc s2 +ℕ 1 }

-- | The program for id ∘ id
compose-id-id-prog : Program
compose-id-id-prog = id-instrs ++ compose-bridge ++ id-instrs

------------------------------------------------------------------------
-- Halted Preservation
--
-- Record updates that only change regs/pc preserve halted.
------------------------------------------------------------------------

-- | s1-id only updates regs and pc, so halted is preserved
s1-not-halted : ∀ (s : State) → X86Sem.State.halted s ≡ false →
  X86Sem.State.halted (s1-id s) ≡ false
s1-not-halted s h-eq = h-eq  -- definitional: record update preserves halted

-- | s2-bridge only updates regs and pc, so halted is preserved
s2-not-halted : ∀ (s : State) → X86Sem.State.halted s ≡ false →
  X86Sem.State.halted (s2-bridge s) ≡ false
s2-not-halted s h-eq = h-eq  -- definitional: record update preserves halted

------------------------------------------------------------------------
-- Step Lemmas for Concatenated Program
--
-- compose-id-id-prog = [mov rax,rdi; mov rdi,rax; mov rax,rdi]
-- We prove step at pc=0, pc=1, pc=2.
------------------------------------------------------------------------

-- | Helper: pc of s1-id
s1-pc : ∀ (s : State) → X86Sem.State.pc s ≡ 0 → X86Sem.State.pc (s1-id s) ≡ 1
s1-pc s pc-eq = cong (λ n → n +ℕ 1) pc-eq

-- | Helper: pc of s2-bridge
s2-pc : ∀ (s : State) → X86Sem.State.pc s ≡ 0 → X86Sem.State.pc (s2-bridge s) ≡ 2
s2-pc s pc-eq = cong (λ n → n +ℕ 1) (s1-pc s pc-eq)

-- | Step 1: at pc=0, execute mov rax, rdi
step-compose-1 : ∀ (s : State) →
  X86Sem.State.halted s ≡ false →
  X86Sem.State.pc s ≡ 0 →
  step compose-id-id-prog s ≡ just (s1-id s)
step-compose-1 s h-eq pc-eq =
  let -- fetch compose-id-id-prog 0 = just (mov rax, rdi)
      fetch-eq : fetch compose-id-id-prog (X86Sem.State.pc s) ≡ just (mov (reg rax) (reg rdi))
      fetch-eq = subst (λ n → fetch compose-id-id-prog n ≡ just (mov (reg rax) (reg rdi)))
                       (sym pc-eq) refl
  in trans (step-fetch-result compose-id-id-prog s (mov (reg rax) (reg rdi)) h-eq fetch-eq)
           (mov-reg-reg-result compose-id-id-prog s rax rdi)

-- | Step 2: at pc=1, execute mov rdi, rax
step-compose-2 : ∀ (s : State) →
  X86Sem.State.halted s ≡ false →
  X86Sem.State.pc s ≡ 0 →
  step compose-id-id-prog (s1-id s) ≡ just (s2-bridge s)
step-compose-2 s h-eq pc-eq =
  let s1 = s1-id s
      -- fetch compose-id-id-prog 1 = just (mov rdi, rax)
      fetch-eq : fetch compose-id-id-prog (X86Sem.State.pc s1) ≡ just (mov (reg rdi) (reg rax))
      fetch-eq = subst (λ n → fetch compose-id-id-prog n ≡ just (mov (reg rdi) (reg rax)))
                       (sym (s1-pc s pc-eq)) refl
  in trans (step-fetch-result compose-id-id-prog s1 (mov (reg rdi) (reg rax)) h-eq fetch-eq)
           (mov-reg-reg-result compose-id-id-prog s1 rdi rax)

-- | Step 3: at pc=2, execute mov rax, rdi
step-compose-3 : ∀ (s : State) →
  X86Sem.State.halted s ≡ false →
  X86Sem.State.pc s ≡ 0 →
  step compose-id-id-prog (s2-bridge s) ≡ just (s3-id s)
step-compose-3 s h-eq pc-eq =
  let s2 = s2-bridge s
      -- fetch compose-id-id-prog 2 = just (mov rax, rdi)
      fetch-eq : fetch compose-id-id-prog (X86Sem.State.pc s2) ≡ just (mov (reg rax) (reg rdi))
      fetch-eq = subst (λ n → fetch compose-id-id-prog n ≡ just (mov (reg rax) (reg rdi)))
                       (sym (s2-pc s pc-eq)) refl
  in trans (step-fetch-result compose-id-id-prog s2 (mov (reg rax) (reg rdi)) h-eq fetch-eq)
           (mov-reg-reg-result compose-id-id-prog s2 rax rdi)

-- | Full Star proof for id ∘ id
compose-id-id-star : ∀ (s : State) →
  X86Sem.State.halted s ≡ false →
  X86Sem.State.pc s ≡ 0 →
  Star compose-id-id-prog s (s3-id s)
compose-id-id-star s h-eq pc-eq =
  star-single h-eq (step-compose-1 s h-eq pc-eq) ◅◅
  star-single (s1-not-halted s h-eq) (step-compose-2 s h-eq pc-eq) ◅◅
  star-single (s2-not-halted s h-eq) (step-compose-3 s h-eq pc-eq)

-- | Result: after id ∘ id, rax = original rdi
compose-id-id-rax-result : ∀ (s : State) →
  x86-readReg (X86Sem.State.regs (s3-id s)) rax ≡
  x86-readReg (X86Sem.State.regs s) rdi
compose-id-id-rax-result s =
  -- rax of s3 = rdi of s2 = rax of s1 = rdi of s
  trans (readReg-writeReg-same (X86Sem.State.regs (s2-bridge s)) rax
          (x86-readReg (X86Sem.State.regs (s2-bridge s)) rdi))
        (trans (cong (λ rf → x86-readReg rf rdi)
                 (subst (λ x → x86-writeReg (X86Sem.State.regs (s1-id s)) rdi x ≡
                              X86Sem.State.regs (s2-bridge s))
                   (readReg-writeReg-same (X86Sem.State.regs s) rax
                     (x86-readReg (X86Sem.State.regs s) rdi))
                   refl))
              (readReg-writeReg-same
                (x86-writeReg (X86Sem.State.regs s) rax (x86-readReg (X86Sem.State.regs s) rdi))
                rdi (x86-readReg (X86Sem.State.regs s) rdi)))

------------------------------------------------------------------------
-- Star Proofs for Simple IRs
--
-- These prove: executing the compiled code reaches the expected state.
-- Usage: star-<ir> s h-eq pc-eq : Star <ir>-instrs s (<ir>-expected-state s)
------------------------------------------------------------------------

-- | id Star proof: mov rax, rdi reaches expected state in one step
id-star : ∀ (s : State) →
  X86Sem.State.halted s ≡ false →
  X86Sem.State.pc s ≡ 0 →
  Star id-instrs s (id-expected-state s)
id-star s h-eq pc-eq = star-single h-eq (step-id s h-eq pc-eq)

-- | terminal Star proof: mov rax, 0 reaches expected state in one step
terminal-star : ∀ (s : State) →
  X86Sem.State.halted s ≡ false →
  X86Sem.State.pc s ≡ 0 →
  Star terminal-instrs s (terminal-expected-state s)
terminal-star s h-eq pc-eq = star-single h-eq (step-terminal s h-eq pc-eq)

-- | fst Star proof: mov rax, [rdi] reaches expected state in one step
fst-star : ∀ (s : State) (v : Word) →
  X86Sem.State.halted s ≡ false →
  X86Sem.State.pc s ≡ 0 →
  x86-readMem (X86Sem.State.memory s) (x86-readReg (X86Sem.State.regs s) rdi) ≡ just v →
  Star fst-instrs s (fst-expected-state s v)
fst-star s v h-eq pc-eq mem-eq = star-single h-eq (step-fst s v h-eq pc-eq mem-eq)

-- | snd Star proof: mov rax, [rdi+8] reaches expected state in one step
snd-star : ∀ (s : State) (v : Word) →
  X86Sem.State.halted s ≡ false →
  X86Sem.State.pc s ≡ 0 →
  x86-readMem (X86Sem.State.memory s) (x86-readReg (X86Sem.State.regs s) rdi +ℕ slot-size) ≡ just v →
  Star snd-instrs s (snd-expected-state s v)
snd-star s v h-eq pc-eq mem-eq = star-single h-eq (step-snd s v h-eq pc-eq mem-eq)

------------------------------------------------------------------------
-- Summary
--
-- This module provides Star-based proofs for IR execution:
--
-- SIMPLE IR STAR PROOFS:
--   ✓ id-star       : Star id-instrs s (id-expected-state s)
--   ✓ terminal-star : Star terminal-instrs s (terminal-expected-state s)
--   ✓ fst-star      : Star fst-instrs s (fst-expected-state s v)
--   ✓ snd-star      : Star snd-instrs s (snd-expected-state s v)
--
-- COMPOSE STAR PROOFS (fully proven):
--   ✓ compose-id-id-star : Star compose-id-id-prog s (s3-id s)
--   ✓ compose-id-id-rax-result : rax (s3-id s) ≡ rdi s
--   ✓ step-compose-{1,2,3} : step at each PC position
--   ✓ s1-not-halted, s2-not-halted : halted preserved
--
-- COMPOSE INFRASTRUCTURE:
--   ✓ compose-bridge : [mov rdi, rax]
--   ✓ step-bridge, bridge-rdi-result
--   ✓ fetch-++ : fetch on left part of concatenated program
--   ✓ fetch-++-right : fetch on right part of concatenation
--
-- POSTULATES: None! All lemmas fully proven.
--
-- The compose framework shows the pattern for chaining Star proofs.
-- For general compose (g ∘ f), instantiate with specific f and g.
------------------------------------------------------------------------
