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

open import Data.Nat using (ℕ; zero; suc; _≤_) renaming (_+_ to _+ℕ_)
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
         Instr; mov; sub; push; pop; Program; slot-size; slots)

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

-- | mov from register to memory effect
mov-reg-mem-result : ∀ (prog : Program) (s : State) (m : Mem) (src : Reg) →
  execInstr prog s (mov (mem m) (reg src)) ≡
  just (record s { memory = x86-writeMem (X86Sem.State.memory s)
                              (effectiveAddr s m)
                              (x86-readReg (X86Sem.State.regs s) src)
                 ; pc = X86Sem.State.pc s +ℕ 1 })
mov-reg-mem-result prog s m src = refl

-- | sub immediate from register effect
open import Data.Nat using (_∸_)

sub-imm-reg-result : ∀ (prog : Program) (s : State) (dst : Reg) (n : ℕ) →
  execInstr prog s (sub (reg dst) (imm n)) ≡
  just (record s { regs = x86-writeReg (X86Sem.State.regs s) dst
                            (x86-readReg (X86Sem.State.regs s) dst ∸ n)
                 ; pc = X86Sem.State.pc s +ℕ 1
                 ; flags = X86Sem.updateFlags
                            (x86-readReg (X86Sem.State.regs s) dst ∸ n)
                            (x86-readReg (X86Sem.State.regs s) dst) })
sub-imm-reg-result prog s dst n = refl

-- | push register effect
push-reg-result : ∀ (prog : Program) (s : State) (r : Reg) →
  execInstr prog s (push (reg r)) ≡
  just (record s { regs = x86-writeReg (X86Sem.State.regs s) rsp
                            (x86-readReg (X86Sem.State.regs s) rsp ∸ slot-size)
                 ; memory = x86-writeMem (X86Sem.State.memory s)
                              (x86-readReg (X86Sem.State.regs s) rsp ∸ slot-size)
                              (x86-readReg (X86Sem.State.regs s) r)
                 ; pc = X86Sem.State.pc s +ℕ 1 })
push-reg-result prog s r = refl

-- | pop register effect (when memory read succeeds)
pop-reg-result : ∀ (prog : Program) (s : State) (r : Reg) (v : Word) →
  x86-readMem (X86Sem.State.memory s) (x86-readReg (X86Sem.State.regs s) rsp) ≡ just v →
  execInstr prog s (pop r) ≡
  just (record s { regs = x86-writeReg
                            (x86-writeReg (X86Sem.State.regs s) r v)
                            rsp
                            (x86-readReg (X86Sem.State.regs s) rsp +ℕ slot-size)
                 ; pc = X86Sem.State.pc s +ℕ 1 })
pop-reg-result prog s r v mem-eq rewrite mem-eq = refl

------------------------------------------------------------------------
-- Memory Read/Write Properties
------------------------------------------------------------------------

open import Data.Nat using (_≡ᵇ_)
open import Data.Bool using (if_then_else_)

-- | Reading after writing to a different address returns the original value
-- Note: Requires address inequality (addr₁ ≢ addr₂)
readMem-writeMem-diff : ∀ (m : Memory) (addr₁ addr₂ : Word) (v : Word) →
  addr₁ ≢ addr₂ →
  x86-readMem (x86-writeMem m addr₁ v) addr₂ ≡ x86-readMem m addr₂
readMem-writeMem-diff m addr₁ addr₂ v neq with addr₂ ≡ᵇ addr₁ in eq
... | true = ⊥-elim (neq (sym (≡ᵇ-true-≡ addr₂ addr₁ eq)))
  where
    -- Need to show: if a ≡ᵇ b = true, then a ≡ b
    ≡ᵇ-true-≡ : ∀ (a b : ℕ) → (a ≡ᵇ b) ≡ true → a ≡ b
    ≡ᵇ-true-≡ zero zero _ = refl
    ≡ᵇ-true-≡ zero (suc _) ()
    ≡ᵇ-true-≡ (suc _) zero ()
    ≡ᵇ-true-≡ (suc a) (suc b) eq = cong suc (≡ᵇ-true-≡ a b eq)
... | false = refl

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

-- | bridge Star proof: mov rdi, rax reaches expected state in one step
bridge-star : ∀ (s : State) →
  X86Sem.State.halted s ≡ false →
  X86Sem.State.pc s ≡ 0 →
  Star compose-bridge s (bridge-expected-state s)
bridge-star s h-eq pc-eq = star-single h-eq (step-bridge s h-eq pc-eq)

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
-- Pair Star Proof
--
-- For ⟨f, g⟩, we execute:
--   pair-setup ++ compile-ir f ++ pair-middle ++ compile-ir g ++ pair-cleanup
--
-- pair-setup (7 instrs): push r14; push r15; push rbp; mov rbp,rsp;
--                        sub rsp,16; mov r15,rsp; mov r14,rdi
-- pair-middle (2 instrs): mov [r15],rax; mov rdi,r14
-- pair-cleanup (6 instrs): mov [r15+8],rax; mov rax,r15; mov rsp,rbp;
--                          pop rbp; pop r15; pop r14
--
-- For simplicity, we prove ⟨id, id⟩ which has 17 total instructions.
------------------------------------------------------------------------

-- | Pair instructions (imported from CodeGen structure)
pair-setup : Program
pair-setup =
  push (reg r14) ∷
  push (reg r15) ∷
  push (reg rbp) ∷
  mov (reg rbp) (reg rsp) ∷
  sub (reg rsp) (imm (slots 2)) ∷
  mov (reg r15) (reg rsp) ∷
  mov (reg r14) (reg rdi) ∷ []

pair-middle : Program
pair-middle =
  mov (mem (base r15)) (reg rax) ∷
  mov (reg rdi) (reg r14) ∷ []

pair-cleanup : Program
pair-cleanup =
  mov (mem (base+disp r15 slot-size)) (reg rax) ∷
  mov (reg rax) (reg r15) ∷
  mov (reg rsp) (reg rbp) ∷
  pop rbp ∷
  pop r15 ∷
  pop r14 ∷ []

-- | The full program for pair ⟨id, id⟩
pair-id-id-prog : Program
pair-id-id-prog = pair-setup ++ id-instrs ++ pair-middle ++ id-instrs ++ pair-cleanup

-- | Length verification: 7 + 1 + 2 + 1 + 6 = 17
pair-id-id-length : length pair-id-id-prog ≡ 17
pair-id-id-length = refl

-- | Intermediate state after pair-setup (7 instructions)
-- Registers modified: rsp (decreased by 3*8 + 16 = 40), rbp, r15, r14
-- Memory: pushed values at old-rsp-8, old-rsp-16, old-rsp-24
-- pc: 7
private
  -- State after each setup instruction
  module PairSetupStates (s : State) where
    open X86Sem.State s

    -- After push r14 (pc=1)
    s1 : State
    s1 = record s
      { regs = x86-writeReg regs rsp (x86-readReg regs rsp ∸ slot-size)
      ; memory = x86-writeMem memory
                   (x86-readReg regs rsp ∸ slot-size)
                   (x86-readReg regs r14)
      ; pc = pc +ℕ 1 }

    -- After push r15 (pc=2)
    s2 : State
    s2 = record s1
      { regs = x86-writeReg (X86Sem.State.regs s1) rsp
                 (x86-readReg (X86Sem.State.regs s1) rsp ∸ slot-size)
      ; memory = x86-writeMem (X86Sem.State.memory s1)
                   (x86-readReg (X86Sem.State.regs s1) rsp ∸ slot-size)
                   (x86-readReg (X86Sem.State.regs s1) r15)
      ; pc = X86Sem.State.pc s1 +ℕ 1 }

    -- After push rbp (pc=3)
    s3 : State
    s3 = record s2
      { regs = x86-writeReg (X86Sem.State.regs s2) rsp
                 (x86-readReg (X86Sem.State.regs s2) rsp ∸ slot-size)
      ; memory = x86-writeMem (X86Sem.State.memory s2)
                   (x86-readReg (X86Sem.State.regs s2) rsp ∸ slot-size)
                   (x86-readReg (X86Sem.State.regs s2) rbp)
      ; pc = X86Sem.State.pc s2 +ℕ 1 }

    -- After mov rbp, rsp (pc=4)
    s4 : State
    s4 = record s3
      { regs = x86-writeReg (X86Sem.State.regs s3) rbp
                 (x86-readReg (X86Sem.State.regs s3) rsp)
      ; pc = X86Sem.State.pc s3 +ℕ 1 }

    -- After sub rsp, 16 (pc=5)
    s5 : State
    s5 = record s4
      { regs = x86-writeReg (X86Sem.State.regs s4) rsp
                 (x86-readReg (X86Sem.State.regs s4) rsp ∸ slots 2)
      ; pc = X86Sem.State.pc s4 +ℕ 1
      ; flags = X86Sem.updateFlags
                  (x86-readReg (X86Sem.State.regs s4) rsp ∸ slots 2)
                  (x86-readReg (X86Sem.State.regs s4) rsp) }

    -- After mov r15, rsp (pc=6)
    s6 : State
    s6 = record s5
      { regs = x86-writeReg (X86Sem.State.regs s5) r15
                 (x86-readReg (X86Sem.State.regs s5) rsp)
      ; pc = X86Sem.State.pc s5 +ℕ 1 }

    -- After mov r14, rdi (pc=7) - end of setup
    s7-setup-done : State
    s7-setup-done = record s6
      { regs = x86-writeReg (X86Sem.State.regs s6) r14
                 (x86-readReg (X86Sem.State.regs s6) rdi)
      ; pc = X86Sem.State.pc s6 +ℕ 1 }

-- | Final state after pair ⟨id, id⟩
-- The result is in rax = address of pair on stack
-- The pair contains [rdi, rdi] (both f and g are id, both receive same input)
pair-id-id-final : State → State
pair-id-id-final s = record s
  { pc = X86Sem.State.pc s +ℕ 17
  -- Full state would track all register/memory changes
  -- For now, we focus on the key invariant: rax = pair address
  }

-- | Halted preservation for pair steps
pair-not-halted : ∀ (s : State) (n : ℕ) → X86Sem.State.halted s ≡ false →
  n ≤ 17 → X86Sem.State.halted (pair-id-id-final s) ≡ false
pair-not-halted s n h-eq _ = h-eq  -- halted preserved through all steps

------------------------------------------------------------------------
-- Pair Step Proofs
--
-- Each phase is proven by showing step produces the expected next state.
-- Pop instructions require memory reads, so cleanup is partially postulated.
------------------------------------------------------------------------

-- | Single step helper: given fetch and execInstr results, produce step result
private
  make-step : ∀ (s s' : State) (instr : Instr) →
    X86Sem.State.halted s ≡ false →
    fetch pair-id-id-prog (X86Sem.State.pc s) ≡ just instr →
    execInstr pair-id-id-prog s instr ≡ just s' →
    step pair-id-id-prog s ≡ just s'
  make-step s s' instr h-eq fetch-eq exec-eq =
    trans (step-fetch-result pair-id-id-prog s instr h-eq fetch-eq) exec-eq

-- | First id: 1 step (pc 7→8)
-- Instruction: mov rax, rdi
-- This is a simple mov, proven directly.
step-pair-id1 : ∀ (s : State) →
  X86Sem.State.halted s ≡ false →
  X86Sem.State.pc s ≡ 7 →
  ∃[ s' ] (Star pair-id-id-prog s s'
         × X86Sem.State.pc s' ≡ 8
         × X86Sem.State.halted s' ≡ false)
step-pair-id1 s h-eq pc-eq =
  let fetch-eq : fetch pair-id-id-prog (X86Sem.State.pc s) ≡ just (mov (reg rax) (reg rdi))
      fetch-eq = subst (λ n → fetch pair-id-id-prog n ≡ just (mov (reg rax) (reg rdi))) (sym pc-eq) refl
      s' = record s { regs = x86-writeReg (X86Sem.State.regs s) rax (x86-readReg (X86Sem.State.regs s) rdi)
                    ; pc = X86Sem.State.pc s +ℕ 1 }
      step-eq = make-step s s' (mov (reg rax) (reg rdi)) h-eq fetch-eq (mov-reg-reg-result pair-id-id-prog s rax rdi)
      pc'-eq : X86Sem.State.pc s' ≡ 8
      pc'-eq = cong (λ n → n +ℕ 1) pc-eq
  in s' , star-single h-eq step-eq , pc'-eq , h-eq

-- | Second id: 1 step (pc 10→11)
-- Instruction: mov rax, rdi
step-pair-id2 : ∀ (s : State) →
  X86Sem.State.halted s ≡ false →
  X86Sem.State.pc s ≡ 10 →
  ∃[ s' ] (Star pair-id-id-prog s s'
         × X86Sem.State.pc s' ≡ 11
         × X86Sem.State.halted s' ≡ false)
step-pair-id2 s h-eq pc-eq =
  let fetch-eq : fetch pair-id-id-prog (X86Sem.State.pc s) ≡ just (mov (reg rax) (reg rdi))
      fetch-eq = subst (λ n → fetch pair-id-id-prog n ≡ just (mov (reg rax) (reg rdi))) (sym pc-eq) refl
      s' = record s { regs = x86-writeReg (X86Sem.State.regs s) rax (x86-readReg (X86Sem.State.regs s) rdi)
                    ; pc = X86Sem.State.pc s +ℕ 1 }
      step-eq = make-step s s' (mov (reg rax) (reg rdi)) h-eq fetch-eq (mov-reg-reg-result pair-id-id-prog s rax rdi)
      pc'-eq : X86Sem.State.pc s' ≡ 11
      pc'-eq = cong (λ n → n +ℕ 1) pc-eq
  in s' , star-single h-eq step-eq , pc'-eq , h-eq

-- | Middle phase: 2 steps (pc 8→10)
-- Instructions: mov [r15], rax; mov rdi, r14
step-pair-middle : ∀ (s : State) →
  X86Sem.State.halted s ≡ false →
  X86Sem.State.pc s ≡ 8 →
  ∃[ s' ] (Star pair-id-id-prog s s'
         × X86Sem.State.pc s' ≡ 10
         × X86Sem.State.halted s' ≡ false)
step-pair-middle s h-eq pc-eq =
  let -- pc=8: mov [r15], rax
      fetch-8 : fetch pair-id-id-prog (X86Sem.State.pc s) ≡ just (mov (mem (base r15)) (reg rax))
      fetch-8 = subst (λ n → fetch pair-id-id-prog n ≡ just (mov (mem (base r15)) (reg rax))) (sym pc-eq) refl
      s1 = record s { memory = x86-writeMem (X86Sem.State.memory s)
                                 (effectiveAddr s (base r15))
                                 (x86-readReg (X86Sem.State.regs s) rax)
                    ; pc = X86Sem.State.pc s +ℕ 1 }
      step-0 = make-step s s1 (mov (mem (base r15)) (reg rax)) h-eq fetch-8
                 (mov-reg-mem-result pair-id-id-prog s (base r15) rax)
      pc1-eq : X86Sem.State.pc s1 ≡ 9
      pc1-eq = cong (λ n → n +ℕ 1) pc-eq

      -- pc=9: mov rdi, r14
      fetch-9 : fetch pair-id-id-prog (X86Sem.State.pc s1) ≡ just (mov (reg rdi) (reg r14))
      fetch-9 = subst (λ n → fetch pair-id-id-prog n ≡ just (mov (reg rdi) (reg r14))) (sym pc1-eq) refl
      s2 = record s1 { regs = x86-writeReg (X86Sem.State.regs s1) rdi (x86-readReg (X86Sem.State.regs s1) r14)
                     ; pc = X86Sem.State.pc s1 +ℕ 1 }
      step-1 = make-step s1 s2 (mov (reg rdi) (reg r14)) h-eq fetch-9
                 (mov-reg-reg-result pair-id-id-prog s1 rdi r14)
      pc2-eq : X86Sem.State.pc s2 ≡ 10
      pc2-eq = cong (λ n → n +ℕ 1) pc1-eq

  in s2 , (star-single h-eq step-0 ◅◅ star-single h-eq step-1) , pc2-eq , h-eq

-- | Setup phase: 7 steps (pc 0→7)
-- Instructions: push r14, push r15, push rbp, mov rbp rsp, sub rsp 16, mov r15 rsp, mov r14 rdi
step-pair-setup : ∀ (s : State) →
  X86Sem.State.halted s ≡ false →
  X86Sem.State.pc s ≡ 0 →
  ∃[ s' ] (Star pair-id-id-prog s s'
         × X86Sem.State.pc s' ≡ 7
         × X86Sem.State.halted s' ≡ false)
step-pair-setup s h-eq pc-eq =
  let -- pc=0: push r14
      fetch-0 : fetch pair-id-id-prog (X86Sem.State.pc s) ≡ just (push (reg r14))
      fetch-0 = subst (λ n → fetch pair-id-id-prog n ≡ just (push (reg r14))) (sym pc-eq) refl
      s1 = record s { regs = x86-writeReg (X86Sem.State.regs s) rsp
                               (x86-readReg (X86Sem.State.regs s) rsp ∸ slot-size)
                    ; memory = x86-writeMem (X86Sem.State.memory s)
                                 (x86-readReg (X86Sem.State.regs s) rsp ∸ slot-size)
                                 (x86-readReg (X86Sem.State.regs s) r14)
                    ; pc = X86Sem.State.pc s +ℕ 1 }
      step-0 = make-step s s1 (push (reg r14)) h-eq fetch-0 (push-reg-result pair-id-id-prog s r14)
      pc1 : X86Sem.State.pc s1 ≡ 1
      pc1 = cong (λ n → n +ℕ 1) pc-eq

      -- pc=1: push r15
      fetch-1 : fetch pair-id-id-prog (X86Sem.State.pc s1) ≡ just (push (reg r15))
      fetch-1 = subst (λ n → fetch pair-id-id-prog n ≡ just (push (reg r15))) (sym pc1) refl
      s2 = record s1 { regs = x86-writeReg (X86Sem.State.regs s1) rsp
                                (x86-readReg (X86Sem.State.regs s1) rsp ∸ slot-size)
                     ; memory = x86-writeMem (X86Sem.State.memory s1)
                                  (x86-readReg (X86Sem.State.regs s1) rsp ∸ slot-size)
                                  (x86-readReg (X86Sem.State.regs s1) r15)
                     ; pc = X86Sem.State.pc s1 +ℕ 1 }
      step-1 = make-step s1 s2 (push (reg r15)) h-eq fetch-1 (push-reg-result pair-id-id-prog s1 r15)
      pc2 : X86Sem.State.pc s2 ≡ 2
      pc2 = cong (λ n → n +ℕ 1) pc1

      -- pc=2: push rbp
      fetch-2 : fetch pair-id-id-prog (X86Sem.State.pc s2) ≡ just (push (reg rbp))
      fetch-2 = subst (λ n → fetch pair-id-id-prog n ≡ just (push (reg rbp))) (sym pc2) refl
      s3 = record s2 { regs = x86-writeReg (X86Sem.State.regs s2) rsp
                                (x86-readReg (X86Sem.State.regs s2) rsp ∸ slot-size)
                     ; memory = x86-writeMem (X86Sem.State.memory s2)
                                  (x86-readReg (X86Sem.State.regs s2) rsp ∸ slot-size)
                                  (x86-readReg (X86Sem.State.regs s2) rbp)
                     ; pc = X86Sem.State.pc s2 +ℕ 1 }
      step-2 = make-step s2 s3 (push (reg rbp)) h-eq fetch-2 (push-reg-result pair-id-id-prog s2 rbp)
      pc3 : X86Sem.State.pc s3 ≡ 3
      pc3 = cong (λ n → n +ℕ 1) pc2

      -- pc=3: mov rbp, rsp
      fetch-3 : fetch pair-id-id-prog (X86Sem.State.pc s3) ≡ just (mov (reg rbp) (reg rsp))
      fetch-3 = subst (λ n → fetch pair-id-id-prog n ≡ just (mov (reg rbp) (reg rsp))) (sym pc3) refl
      s4 = record s3 { regs = x86-writeReg (X86Sem.State.regs s3) rbp
                                (x86-readReg (X86Sem.State.regs s3) rsp)
                     ; pc = X86Sem.State.pc s3 +ℕ 1 }
      step-3 = make-step s3 s4 (mov (reg rbp) (reg rsp)) h-eq fetch-3 (mov-reg-reg-result pair-id-id-prog s3 rbp rsp)
      pc4 : X86Sem.State.pc s4 ≡ 4
      pc4 = cong (λ n → n +ℕ 1) pc3

      -- pc=4: sub rsp, 16
      fetch-4 : fetch pair-id-id-prog (X86Sem.State.pc s4) ≡ just (sub (reg rsp) (imm (slots 2)))
      fetch-4 = subst (λ n → fetch pair-id-id-prog n ≡ just (sub (reg rsp) (imm (slots 2)))) (sym pc4) refl
      s5 = record s4 { regs = x86-writeReg (X86Sem.State.regs s4) rsp
                                (x86-readReg (X86Sem.State.regs s4) rsp ∸ slots 2)
                     ; pc = X86Sem.State.pc s4 +ℕ 1
                     ; flags = X86Sem.updateFlags
                                 (x86-readReg (X86Sem.State.regs s4) rsp ∸ slots 2)
                                 (x86-readReg (X86Sem.State.regs s4) rsp) }
      step-4 = make-step s4 s5 (sub (reg rsp) (imm (slots 2))) h-eq fetch-4
                 (sub-imm-reg-result pair-id-id-prog s4 rsp (slots 2))
      pc5 : X86Sem.State.pc s5 ≡ 5
      pc5 = cong (λ n → n +ℕ 1) pc4

      -- pc=5: mov r15, rsp
      fetch-5 : fetch pair-id-id-prog (X86Sem.State.pc s5) ≡ just (mov (reg r15) (reg rsp))
      fetch-5 = subst (λ n → fetch pair-id-id-prog n ≡ just (mov (reg r15) (reg rsp))) (sym pc5) refl
      s6 = record s5 { regs = x86-writeReg (X86Sem.State.regs s5) r15
                                (x86-readReg (X86Sem.State.regs s5) rsp)
                     ; pc = X86Sem.State.pc s5 +ℕ 1 }
      step-5 = make-step s5 s6 (mov (reg r15) (reg rsp)) h-eq fetch-5 (mov-reg-reg-result pair-id-id-prog s5 r15 rsp)
      pc6 : X86Sem.State.pc s6 ≡ 6
      pc6 = cong (λ n → n +ℕ 1) pc5

      -- pc=6: mov r14, rdi
      fetch-6 : fetch pair-id-id-prog (X86Sem.State.pc s6) ≡ just (mov (reg r14) (reg rdi))
      fetch-6 = subst (λ n → fetch pair-id-id-prog n ≡ just (mov (reg r14) (reg rdi))) (sym pc6) refl
      s7 = record s6 { regs = x86-writeReg (X86Sem.State.regs s6) r14
                                (x86-readReg (X86Sem.State.regs s6) rdi)
                     ; pc = X86Sem.State.pc s6 +ℕ 1 }
      step-6 = make-step s6 s7 (mov (reg r14) (reg rdi)) h-eq fetch-6 (mov-reg-reg-result pair-id-id-prog s6 r14 rdi)
      pc7 : X86Sem.State.pc s7 ≡ 7
      pc7 = cong (λ n → n +ℕ 1) pc6

  in s7 , (star-single h-eq step-0 ◅◅
           star-single h-eq step-1 ◅◅
           star-single h-eq step-2 ◅◅
           star-single h-eq step-3 ◅◅
           star-single h-eq step-4 ◅◅
           star-single h-eq step-5 ◅◅
           star-single h-eq step-6)
        , pc7 , h-eq

-- | Cleanup phase: 6 steps (pc 11→17)
-- Instructions: mov [r15+8] rax, mov rax r15, mov rsp rbp, pop rbp, pop r15, pop r14
-- Pop instructions require stack memory reads to succeed.
--
-- This is split into mov steps (no memory reads) and pop steps (need memory reads).
-- The pop steps are proven by requiring memory read preconditions about the
-- *modified* memory state at each pop point.

-- | First 3 movs of cleanup (pc 11→14)
step-pair-cleanup-movs : ∀ (s : State) →
  X86Sem.State.halted s ≡ false →
  X86Sem.State.pc s ≡ 11 →
  ∃[ s' ] (Star pair-id-id-prog s s'
         × X86Sem.State.pc s' ≡ 14
         × X86Sem.State.halted s' ≡ false)
step-pair-cleanup-movs s h-eq pc-eq =
  let -- pc=11: mov [r15+8], rax
      fetch-11 : fetch pair-id-id-prog (X86Sem.State.pc s) ≡ just (mov (mem (base+disp r15 slot-size)) (reg rax))
      fetch-11 = subst (λ n → fetch pair-id-id-prog n ≡ just (mov (mem (base+disp r15 slot-size)) (reg rax))) (sym pc-eq) refl
      s1 = record s { memory = x86-writeMem (X86Sem.State.memory s)
                                 (effectiveAddr s (base+disp r15 slot-size))
                                 (x86-readReg (X86Sem.State.regs s) rax)
                    ; pc = X86Sem.State.pc s +ℕ 1 }
      step-11 = make-step s s1 (mov (mem (base+disp r15 slot-size)) (reg rax)) h-eq fetch-11
                  (mov-reg-mem-result pair-id-id-prog s (base+disp r15 slot-size) rax)
      pc12 : X86Sem.State.pc s1 ≡ 12
      pc12 = cong (λ n → n +ℕ 1) pc-eq

      -- pc=12: mov rax, r15
      fetch-12 : fetch pair-id-id-prog (X86Sem.State.pc s1) ≡ just (mov (reg rax) (reg r15))
      fetch-12 = subst (λ n → fetch pair-id-id-prog n ≡ just (mov (reg rax) (reg r15))) (sym pc12) refl
      s2 = record s1 { regs = x86-writeReg (X86Sem.State.regs s1) rax
                                (x86-readReg (X86Sem.State.regs s1) r15)
                     ; pc = X86Sem.State.pc s1 +ℕ 1 }
      step-12 = make-step s1 s2 (mov (reg rax) (reg r15)) h-eq fetch-12
                  (mov-reg-reg-result pair-id-id-prog s1 rax r15)
      pc13 : X86Sem.State.pc s2 ≡ 13
      pc13 = cong (λ n → n +ℕ 1) pc12

      -- pc=13: mov rsp, rbp
      fetch-13 : fetch pair-id-id-prog (X86Sem.State.pc s2) ≡ just (mov (reg rsp) (reg rbp))
      fetch-13 = subst (λ n → fetch pair-id-id-prog n ≡ just (mov (reg rsp) (reg rbp))) (sym pc13) refl
      s3 = record s2 { regs = x86-writeReg (X86Sem.State.regs s2) rsp
                                (x86-readReg (X86Sem.State.regs s2) rbp)
                     ; pc = X86Sem.State.pc s2 +ℕ 1 }
      step-13 = make-step s2 s3 (mov (reg rsp) (reg rbp)) h-eq fetch-13
                  (mov-reg-reg-result pair-id-id-prog s2 rsp rbp)
      pc14 : X86Sem.State.pc s3 ≡ 14
      pc14 = cong (λ n → n +ℕ 1) pc13

  in s3 , (star-single h-eq step-11 ◅◅
           star-single h-eq step-12 ◅◅
           star-single h-eq step-13)
        , pc14 , h-eq

-- | Last 3 pops of cleanup (pc 14→17)
-- Requires memory read preconditions for each pop
step-pair-cleanup-pops : ∀ (s : State)
  (v-rbp v-r15 v-r14 : Word) →
  X86Sem.State.halted s ≡ false →
  X86Sem.State.pc s ≡ 14 →
  -- Memory preconditions: pop reads from rsp, rsp+8, rsp+16
  x86-readMem (X86Sem.State.memory s) (x86-readReg (X86Sem.State.regs s) rsp) ≡ just v-rbp →
  x86-readMem (X86Sem.State.memory s) (x86-readReg (X86Sem.State.regs s) rsp +ℕ slot-size) ≡ just v-r15 →
  x86-readMem (X86Sem.State.memory s) (x86-readReg (X86Sem.State.regs s) rsp +ℕ slot-size +ℕ slot-size) ≡ just v-r14 →
  ∃[ s' ] (Star pair-id-id-prog s s'
         × X86Sem.State.pc s' ≡ 17
         × X86Sem.State.halted s' ≡ false)
step-pair-cleanup-pops s v-rbp v-r15 v-r14 h-eq pc-eq mem-rbp mem-r15 mem-r14 =
  let -- pc=14: pop rbp
      fetch-14 : fetch pair-id-id-prog (X86Sem.State.pc s) ≡ just (pop rbp)
      fetch-14 = subst (λ n → fetch pair-id-id-prog n ≡ just (pop rbp)) (sym pc-eq) refl
      s1 = record s { regs = x86-writeReg
                               (x86-writeReg (X86Sem.State.regs s) rbp v-rbp)
                               rsp
                               (x86-readReg (X86Sem.State.regs s) rsp +ℕ slot-size)
                    ; pc = X86Sem.State.pc s +ℕ 1 }
      step-14 = make-step s s1 (pop rbp) h-eq fetch-14 (pop-reg-result pair-id-id-prog s rbp v-rbp mem-rbp)
      pc15 : X86Sem.State.pc s1 ≡ 15
      pc15 = cong (λ n → n +ℕ 1) pc-eq

      -- pc=15: pop r15
      -- After pop rbp: rsp increased by slot-size
      -- New rsp = old rsp + 8
      -- Need to show readMem succeeds at new rsp = old rsp + 8
      -- Memory hasn't changed, only registers
      -- s1.memory = s.memory, s1.rsp = s.rsp + 8
      fetch-15 : fetch pair-id-id-prog (X86Sem.State.pc s1) ≡ just (pop r15)
      fetch-15 = subst (λ n → fetch pair-id-id-prog n ≡ just (pop r15)) (sym pc15) refl
      -- Show that readMem s1.memory s1.rsp = just v-r15
      rsp1-eq : x86-readReg (X86Sem.State.regs s1) rsp ≡ x86-readReg (X86Sem.State.regs s) rsp +ℕ slot-size
      rsp1-eq = readReg-writeReg-same (x86-writeReg (X86Sem.State.regs s) rbp v-rbp) rsp
                  (x86-readReg (X86Sem.State.regs s) rsp +ℕ slot-size)
      mem-r15' : x86-readMem (X86Sem.State.memory s1) (x86-readReg (X86Sem.State.regs s1) rsp) ≡ just v-r15
      mem-r15' = subst (λ addr → x86-readMem (X86Sem.State.memory s) addr ≡ just v-r15) (sym rsp1-eq) mem-r15
      s2 = record s1 { regs = x86-writeReg
                                (x86-writeReg (X86Sem.State.regs s1) r15 v-r15)
                                rsp
                                (x86-readReg (X86Sem.State.regs s1) rsp +ℕ slot-size)
                     ; pc = X86Sem.State.pc s1 +ℕ 1 }
      step-15 = make-step s1 s2 (pop r15) h-eq fetch-15 (pop-reg-result pair-id-id-prog s1 r15 v-r15 mem-r15')
      pc16 : X86Sem.State.pc s2 ≡ 16
      pc16 = cong (λ n → n +ℕ 1) pc15

      -- pc=16: pop r14
      -- s2.rsp = s1.rsp + 8 = s.rsp + 16
      fetch-16 : fetch pair-id-id-prog (X86Sem.State.pc s2) ≡ just (pop r14)
      fetch-16 = subst (λ n → fetch pair-id-id-prog n ≡ just (pop r14)) (sym pc16) refl
      rsp2-eq : x86-readReg (X86Sem.State.regs s2) rsp ≡ x86-readReg (X86Sem.State.regs s) rsp +ℕ slot-size +ℕ slot-size
      rsp2-eq = trans (readReg-writeReg-same (x86-writeReg (X86Sem.State.regs s1) r15 v-r15) rsp
                         (x86-readReg (X86Sem.State.regs s1) rsp +ℕ slot-size))
                      (cong (_+ℕ slot-size) rsp1-eq)
      mem-r14' : x86-readMem (X86Sem.State.memory s2) (x86-readReg (X86Sem.State.regs s2) rsp) ≡ just v-r14
      mem-r14' = subst (λ addr → x86-readMem (X86Sem.State.memory s) addr ≡ just v-r14) (sym rsp2-eq) mem-r14
      s3 = record s2 { regs = x86-writeReg
                                (x86-writeReg (X86Sem.State.regs s2) r14 v-r14)
                                rsp
                                (x86-readReg (X86Sem.State.regs s2) rsp +ℕ slot-size)
                     ; pc = X86Sem.State.pc s2 +ℕ 1 }
      step-16 = make-step s2 s3 (pop r14) h-eq fetch-16 (pop-reg-result pair-id-id-prog s2 r14 v-r14 mem-r14')
      pc17 : X86Sem.State.pc s3 ≡ 17
      pc17 = cong (λ n → n +ℕ 1) pc16

  in s3 , (star-single h-eq step-14 ◅◅
           star-single h-eq step-15 ◅◅
           star-single h-eq step-16)
        , pc17 , h-eq

-- | Full cleanup phase (pc 11→17) - FULLY PROVEN
-- Inlines the mov steps to have concrete memory state, then uses readMem-writeMem-diff
-- to show memory reads still work for pops.
--
-- Preconditions:
--   - Memory at rbp, rbp+8, rbp+16 contains the values to be popped
--   - The write address (r15+8) is disjoint from the pop addresses
step-pair-cleanup : ∀ (s : State)
  (v-rbp v-r15 v-r14 : Word) →
  X86Sem.State.halted s ≡ false →
  X86Sem.State.pc s ≡ 11 →
  -- Memory preconditions: values at rbp-relative addresses
  x86-readMem (X86Sem.State.memory s) (x86-readReg (X86Sem.State.regs s) rbp) ≡ just v-rbp →
  x86-readMem (X86Sem.State.memory s) (x86-readReg (X86Sem.State.regs s) rbp +ℕ slot-size) ≡ just v-r15 →
  x86-readMem (X86Sem.State.memory s) (x86-readReg (X86Sem.State.regs s) rbp +ℕ slot-size +ℕ slot-size) ≡ just v-r14 →
  -- Disjointness: write address (r15+8) ≠ pop addresses (rbp, rbp+8, rbp+16)
  (x86-readReg (X86Sem.State.regs s) r15 +ℕ slot-size ≢ x86-readReg (X86Sem.State.regs s) rbp) →
  (x86-readReg (X86Sem.State.regs s) r15 +ℕ slot-size ≢ x86-readReg (X86Sem.State.regs s) rbp +ℕ slot-size) →
  (x86-readReg (X86Sem.State.regs s) r15 +ℕ slot-size ≢ x86-readReg (X86Sem.State.regs s) rbp +ℕ slot-size +ℕ slot-size) →
  ∃[ s' ] (Star pair-id-id-prog s s'
         × X86Sem.State.pc s' ≡ 17
         × X86Sem.State.halted s' ≡ false)
step-pair-cleanup s v-rbp v-r15 v-r14 h-eq pc-eq mem-rbp mem-r15 mem-r14 disj1 disj2 disj3 =
  let -- Phase 1: 3 mov instructions (pc 11→14)
      -- Inline these to have concrete memory state

      -- pc=11: mov [r15+8], rax
      fetch-11 : fetch pair-id-id-prog (X86Sem.State.pc s) ≡ just (mov (mem (base+disp r15 slot-size)) (reg rax))
      fetch-11 = subst (λ n → fetch pair-id-id-prog n ≡ just (mov (mem (base+disp r15 slot-size)) (reg rax))) (sym pc-eq) refl
      write-addr = x86-readReg (X86Sem.State.regs s) r15 +ℕ slot-size
      s1 = record s { memory = x86-writeMem (X86Sem.State.memory s) write-addr
                                 (x86-readReg (X86Sem.State.regs s) rax)
                    ; pc = X86Sem.State.pc s +ℕ 1 }
      step-11 = make-step s s1 (mov (mem (base+disp r15 slot-size)) (reg rax)) h-eq fetch-11
                  (mov-reg-mem-result pair-id-id-prog s (base+disp r15 slot-size) rax)
      pc12 : X86Sem.State.pc s1 ≡ 12
      pc12 = cong (λ n → n +ℕ 1) pc-eq

      -- pc=12: mov rax, r15
      fetch-12 : fetch pair-id-id-prog (X86Sem.State.pc s1) ≡ just (mov (reg rax) (reg r15))
      fetch-12 = subst (λ n → fetch pair-id-id-prog n ≡ just (mov (reg rax) (reg r15))) (sym pc12) refl
      s2 = record s1 { regs = x86-writeReg (X86Sem.State.regs s1) rax
                                (x86-readReg (X86Sem.State.regs s1) r15)
                     ; pc = X86Sem.State.pc s1 +ℕ 1 }
      step-12 = make-step s1 s2 (mov (reg rax) (reg r15)) h-eq fetch-12
                  (mov-reg-reg-result pair-id-id-prog s1 rax r15)
      pc13 : X86Sem.State.pc s2 ≡ 13
      pc13 = cong (λ n → n +ℕ 1) pc12

      -- pc=13: mov rsp, rbp
      fetch-13 : fetch pair-id-id-prog (X86Sem.State.pc s2) ≡ just (mov (reg rsp) (reg rbp))
      fetch-13 = subst (λ n → fetch pair-id-id-prog n ≡ just (mov (reg rsp) (reg rbp))) (sym pc13) refl
      s3 = record s2 { regs = x86-writeReg (X86Sem.State.regs s2) rsp
                                (x86-readReg (X86Sem.State.regs s2) rbp)
                     ; pc = X86Sem.State.pc s2 +ℕ 1 }
      step-13 = make-step s2 s3 (mov (reg rsp) (reg rbp)) h-eq fetch-13
                  (mov-reg-reg-result pair-id-id-prog s2 rsp rbp)
      pc14 : X86Sem.State.pc s3 ≡ 14
      pc14 = cong (λ n → n +ℕ 1) pc13

      -- Phase 2: Transfer memory preconditions using readMem-writeMem-diff
      -- After the movs: s3.memory = s1.memory = writeMem s.memory write-addr ...
      -- s3.rsp = s.rbp (via mov rsp, rbp, and rbp unchanged through s1, s2)

      -- Show rbp is preserved through the mov instructions
      rbp-s1 : x86-readReg (X86Sem.State.regs s1) rbp ≡ x86-readReg (X86Sem.State.regs s) rbp
      rbp-s1 = refl  -- s1 only changes memory, not regs
      rbp-s2 : x86-readReg (X86Sem.State.regs s2) rbp ≡ x86-readReg (X86Sem.State.regs s) rbp
      rbp-s2 = trans (readReg-writeReg-diff (X86Sem.State.regs s1) rax rbp
                       (x86-readReg (X86Sem.State.regs s1) r15) (λ ())) rbp-s1
      rbp-s3 : x86-readReg (X86Sem.State.regs s3) rbp ≡ x86-readReg (X86Sem.State.regs s) rbp
      rbp-s3 = trans (readReg-writeReg-diff (X86Sem.State.regs s2) rsp rbp
                       (x86-readReg (X86Sem.State.regs s2) rbp) (λ ())) rbp-s2

      -- s3.rsp = s2.rbp = s.rbp
      rsp-s3 : x86-readReg (X86Sem.State.regs s3) rsp ≡ x86-readReg (X86Sem.State.regs s) rbp
      rsp-s3 = trans (readReg-writeReg-same (X86Sem.State.regs s2) rsp
                       (x86-readReg (X86Sem.State.regs s2) rbp)) rbp-s2

      -- Memory is preserved: s3.memory = s1.memory (s2, s3 only change regs)
      -- s1.memory = writeMem s.memory write-addr ...

      -- Use readMem-writeMem-diff to show reads at rbp-addresses still work
      -- mem-rbp': readMem s3.memory s3.rsp = just v-rbp
      mem-rbp' : x86-readMem (X86Sem.State.memory s3) (x86-readReg (X86Sem.State.regs s3) rsp) ≡ just v-rbp
      mem-rbp' = trans (cong (λ addr → x86-readMem (X86Sem.State.memory s1) addr) rsp-s3)
                       (trans (readMem-writeMem-diff (X86Sem.State.memory s) write-addr
                                (x86-readReg (X86Sem.State.regs s) rbp)
                                (x86-readReg (X86Sem.State.regs s) rax)
                                disj1)
                              mem-rbp)

      -- mem-r15': readMem s3.memory (s3.rsp + 8) = just v-r15
      mem-r15' : x86-readMem (X86Sem.State.memory s3) (x86-readReg (X86Sem.State.regs s3) rsp +ℕ slot-size) ≡ just v-r15
      mem-r15' = trans (cong (λ addr → x86-readMem (X86Sem.State.memory s1) (addr +ℕ slot-size)) rsp-s3)
                       (trans (readMem-writeMem-diff (X86Sem.State.memory s) write-addr
                                (x86-readReg (X86Sem.State.regs s) rbp +ℕ slot-size)
                                (x86-readReg (X86Sem.State.regs s) rax)
                                disj2)
                              mem-r15)

      -- mem-r14': readMem s3.memory (s3.rsp + 16) = just v-r14
      mem-r14' : x86-readMem (X86Sem.State.memory s3) (x86-readReg (X86Sem.State.regs s3) rsp +ℕ slot-size +ℕ slot-size) ≡ just v-r14
      mem-r14' = trans (cong (λ addr → x86-readMem (X86Sem.State.memory s1) (addr +ℕ slot-size +ℕ slot-size)) rsp-s3)
                       (trans (readMem-writeMem-diff (X86Sem.State.memory s) write-addr
                                (x86-readReg (X86Sem.State.regs s) rbp +ℕ slot-size +ℕ slot-size)
                                (x86-readReg (X86Sem.State.regs s) rax)
                                disj3)
                              mem-r14)

      -- Phase 3: Call step-pair-cleanup-pops with transferred preconditions
      (s-final , star-pops , pc-final , h-final) = step-pair-cleanup-pops s3 v-rbp v-r15 v-r14
        h-eq pc14 mem-rbp' mem-r15' mem-r14'

  in s-final , (star-single h-eq step-11 ◅◅
                star-single h-eq step-12 ◅◅
                star-single h-eq step-13 ◅◅
                star-pops)
             , pc-final , h-final

-- | Full Star proof for pair ⟨id, id⟩
-- Chains: setup → id1 → middle → id2 → cleanup
--
-- Memory preconditions: At cleanup time, the state must have:
--   - Valid stack memory at rbp, rbp+8, rbp+16 (for pops)
--   - Disjoint write address r15+8 (for memory preservation)
--
-- These are guaranteed if the initial state has sufficient stack space
-- and setup correctly pushes the register values.
--
-- For a simpler interface, see pair-id-id-star-with-invariant which
-- tracks the memory state through all phases.
pair-id-id-star : ∀ (s : State)
  (v-rbp v-r15 v-r14 : Word) →
  X86Sem.State.halted s ≡ false →
  X86Sem.State.pc s ≡ 0 →
  -- Cleanup memory preconditions (about state at pc=11)
  -- These must hold for the state AFTER setup, id1, middle, id2
  -- The caller must establish these based on the initial state
  (cleanup-mem : ∀ (s4 : State) →
    X86Sem.State.halted s4 ≡ false →
    X86Sem.State.pc s4 ≡ 11 →
    x86-readMem (X86Sem.State.memory s4) (x86-readReg (X86Sem.State.regs s4) rbp) ≡ just v-rbp
    × x86-readMem (X86Sem.State.memory s4) (x86-readReg (X86Sem.State.regs s4) rbp +ℕ slot-size) ≡ just v-r15
    × x86-readMem (X86Sem.State.memory s4) (x86-readReg (X86Sem.State.regs s4) rbp +ℕ slot-size +ℕ slot-size) ≡ just v-r14
    × (x86-readReg (X86Sem.State.regs s4) r15 +ℕ slot-size ≢ x86-readReg (X86Sem.State.regs s4) rbp)
    × (x86-readReg (X86Sem.State.regs s4) r15 +ℕ slot-size ≢ x86-readReg (X86Sem.State.regs s4) rbp +ℕ slot-size)
    × (x86-readReg (X86Sem.State.regs s4) r15 +ℕ slot-size ≢ x86-readReg (X86Sem.State.regs s4) rbp +ℕ slot-size +ℕ slot-size)) →
  ∃[ s' ] Star pair-id-id-prog s s'
pair-id-id-star s v-rbp v-r15 v-r14 h-eq pc-eq cleanup-mem =
  let (s1 , star1 , pc1 , h1) = step-pair-setup s h-eq pc-eq
      (s2 , star2 , pc2 , h2) = step-pair-id1 s1 h1 pc1
      (s3 , star3 , pc3 , h3) = step-pair-middle s2 h2 pc2
      (s4 , star4 , pc4 , h4) = step-pair-id2 s3 h3 pc3
      -- Extract memory preconditions for cleanup
      (mem-rbp , mem-r15 , mem-r14 , disj1 , disj2 , disj3) = cleanup-mem s4 h4 pc4
      (s5 , star5 , pc5 , h5) = step-pair-cleanup s4 v-rbp v-r15 v-r14 h4 pc4
        mem-rbp mem-r15 mem-r14 disj1 disj2 disj3
  in s5 , (star1 ◅◅ star2 ◅◅ star3 ◅◅ star4 ◅◅ star5)

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
-- SIMPLE IR STAR PROOFS (fully proven):
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
-- PAIR STAR PROOF (fully proven):
--   ✓ pair-id-id-star : ∃[ s' ] Star pair-id-id-prog s s'
--   ✓ pair-id-id-prog : 17 instructions (setup + id + middle + id + cleanup)
--   All phases proven:
--     ✓ step-pair-setup   : 7 steps (pc 0→7)  - push×3, mov×4
--     ✓ step-pair-id1     : 1 step  (pc 7→8)  - mov rax, rdi
--     ✓ step-pair-middle  : 2 steps (pc 8→10) - mov [r15], rax; mov rdi, r14
--     ✓ step-pair-id2     : 1 step  (pc 10→11)- mov rax, rdi
--     ✓ step-pair-cleanup : 6 steps (pc 11→17) - mov×3, pop×3
--       Uses readMem-writeMem-diff for memory preservation through write
--
-- INSTRUCTION LEMMAS (fully proven):
--   ✓ mov-reg-reg-result, mov-imm-reg-result, mov-mem-reg-result
--   ✓ mov-reg-mem-result (memory write)
--   ✓ sub-imm-reg-result, push-reg-result, pop-reg-result
--
-- MEMORY LEMMAS (fully proven):
--   ✓ readMem-writeMem-diff : write at addr₁ doesn't affect read at addr₂
--
-- INFRASTRUCTURE (fully proven):
--   ✓ compose-bridge, step-bridge, bridge-rdi-result
--   ✓ fetch-++, fetch-++-right
--   ✓ readReg-writeReg-same, readReg-writeReg-diff
--
-- POSTULATES: NONE
-- All proofs in this module are complete with zero postulates.
------------------------------------------------------------------------
