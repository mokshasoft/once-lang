------------------------------------------------------------------------
-- Once.Backend.X86.Correct.InstrExec
--
-- Lemmas for single instruction execution.
-- These are independent (Level 0) - no dependencies on other Correct/* modules.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.InstrExec where

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State
open Once.Backend.X86.Semantics.Flags

open import Data.Nat using (ℕ; _∸_) renaming (_+_ to _+ℕ_)
open import Data.List using (List; [])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Execution Helpers
------------------------------------------------------------------------
--
-- These helpers capture the behavior of individual instructions.
-- Each lemma proves what state results from executing a specific instruction.

-- Helper: state after executing mov reg reg
execMov-reg-reg : ∀ (s : State) (dst src : Reg) →
  execInstr [] s (mov (reg dst) (reg src)) ≡
    just (record s { regs = writeReg (regs s) dst (readReg (regs s) src)
                   ; pc = pc s +ℕ 1 })
execMov-reg-reg s dst src = refl

-- Helper: state after executing mov reg imm
execMov-reg-imm : ∀ (s : State) (dst : Reg) (n : ℕ) →
  execInstr [] s (mov (reg dst) (imm n)) ≡
    just (record s { regs = writeReg (regs s) dst n
                   ; pc = pc s +ℕ 1 })
execMov-reg-imm s dst n = refl

-- Helper: state after executing mov reg [reg] (memory load)
execMov-reg-mem-base : ∀ (s : State) (dst src : Reg) (v : ℕ) →
  readMem (memory s) (readReg (regs s) src) ≡ just v →
  execInstr [] s (mov (reg dst) (mem (base src))) ≡
    just (record s { regs = writeReg (regs s) dst v
                   ; pc = pc s +ℕ 1 })
execMov-reg-mem-base s dst src v mem-ok with readMem (memory s) (readReg (regs s) src) | mem-ok
... | just .v | refl = refl

-- Helper: state after executing mov reg [reg+disp] (memory load with displacement)
execMov-reg-mem-disp : ∀ (s : State) (dst src : Reg) (disp v : ℕ) →
  readMem (memory s) (readReg (regs s) src +ℕ disp) ≡ just v →
  execInstr [] s (mov (reg dst) (mem (base+disp src disp))) ≡
    just (record s { regs = writeReg (regs s) dst v
                   ; pc = pc s +ℕ 1 })
execMov-reg-mem-disp s dst src disp v mem-ok with readMem (memory s) (readReg (regs s) src +ℕ disp) | mem-ok
... | just .v | refl = refl

-- Helper: state after executing mov [reg] imm (memory store)
execMov-mem-base-imm : ∀ (prog : List Instr) (s : State) (dst : Reg) (v : ℕ) →
  execInstr prog s (mov (mem (base dst)) (imm v)) ≡
    just (record s { memory = writeMem (memory s) (readReg (regs s) dst) v
                   ; pc = pc s +ℕ 1 })
execMov-mem-base-imm prog s dst v = refl

-- Helper: state after executing mov [reg+disp] reg (memory store)
execMov-mem-disp-reg : ∀ (prog : List Instr) (s : State) (dst src : Reg) (disp : ℕ) →
  execInstr prog s (mov (mem (base+disp dst disp)) (reg src)) ≡
    just (record s { memory = writeMem (memory s) (readReg (regs s) dst +ℕ disp) (readReg (regs s) src)
                   ; pc = pc s +ℕ 1 })
execMov-mem-disp-reg prog s dst src disp = refl

-- Helper: state after executing mov [reg] reg (memory store from register)
execMov-mem-base-reg : ∀ (prog : List Instr) (s : State) (dst src : Reg) →
  execInstr prog s (mov (mem (base dst)) (reg src)) ≡
    just (record s { memory = writeMem (memory s) (readReg (regs s) dst) (readReg (regs s) src)
                   ; pc = pc s +ℕ 1 })
execMov-mem-base-reg prog s dst src = refl

-- Helper: state after executing sub reg imm
execSub-reg-imm : ∀ (prog : List Instr) (s : State) (dst : Reg) (v : ℕ) →
  execInstr prog s (sub (reg dst) (imm v)) ≡
    just (record s { regs = writeReg (regs s) dst (readReg (regs s) dst ∸ v)
                   ; pc = pc s +ℕ 1
                   ; flags = updateFlags (readReg (regs s) dst ∸ v) (readReg (regs s) dst) })
execSub-reg-imm prog s dst v = refl

-- Helper: state after executing jmp target
execJmp : ∀ (prog : List Instr) (s : State) (target : ℕ) →
  execInstr prog s (jmp target) ≡ just (record s { pc = pc s +ℕ 1 +ℕ target })
execJmp prog s target = refl

-- Helper: state after executing lea reg, [mem]
execLea : ∀ (prog : List Instr) (s : State) (r : Reg) (m : Mem) →
  execInstr prog s (lea r m) ≡
    just (record s { regs = writeReg (regs s) r (effectiveAddr s m)
                   ; pc = pc s +ℕ 1 })
execLea prog s r m = refl

-- Helper: state after executing add reg, imm
execAdd-reg-imm : ∀ (prog : List Instr) (s : State) (dst : Reg) (v : ℕ) →
  execInstr prog s (add (reg dst) (imm v)) ≡
    just (record s { regs = writeReg (regs s) dst (readReg (regs s) dst +ℕ v)
                   ; pc = pc s +ℕ 1
                   ; flags = updateFlags (readReg (regs s) dst +ℕ v) (readReg (regs s) dst) })
execAdd-reg-imm prog s dst v = refl

-- Helper: state after executing cmp (reg r) (imm 0) when r contains 0
execCmp-zero : ∀ (prog : List Instr) (s : State) (r : Reg) →
  readReg (regs s) r ≡ 0 →
  execInstr prog s (cmp (reg r) (imm 0)) ≡
    just (record s { pc = pc s +ℕ 1 ; flags = mkflags true false false })
execCmp-zero prog s r eq rewrite eq = refl

-- Helper: state after executing cmp (reg r) (imm 0) when r contains 1 (inr tag)
execCmp-one : ∀ (prog : List Instr) (s : State) (r : Reg) →
  readReg (regs s) r ≡ 1 →
  execInstr prog s (cmp (reg r) (imm 0)) ≡
    just (record s { pc = pc s +ℕ 1 ; flags = mkflags false false false })
execCmp-one prog s r eq rewrite eq = refl

-- Helper: state after executing jne when ZF = true (not taken)
execJne-not-taken : ∀ (prog : List Instr) (s : State) (target : ℕ) →
  zf (flags s) ≡ true →
  execInstr prog s (jne target) ≡ just (record s { pc = pc s +ℕ 1 })
execJne-not-taken prog s target zf-true rewrite zf-true = refl

-- Helper: state after executing jne when ZF = false (taken)
execJne-taken : ∀ (prog : List Instr) (s : State) (target : ℕ) →
  zf (flags s) ≡ false →
  execInstr prog s (jne target) ≡ just (record s { pc = pc s +ℕ 1 +ℕ target })
execJne-taken prog s target zf-false rewrite zf-false = refl

-- Helper: label is a no-op, just advances pc
execLabel : ∀ (prog : List Instr) (s : State) (n : ℕ) →
  execInstr prog s (label n) ≡ just (record s { pc = pc s +ℕ 1 })
execLabel prog s n = refl

-- Helper: state after executing pop reg
execPop : ∀ (prog : List Instr) (s : State) (r : Reg) (v : Word) →
  readMem (memory s) (readReg (regs s) rsp) ≡ just v →
  execInstr prog s (pop r) ≡
    just (record s { regs = writeReg (writeReg (regs s) r v) rsp (readReg (regs s) rsp +ℕ 8)
                   ; pc = pc s +ℕ 1 })
execPop prog s r v mem-ok with readMem (memory s) (readReg (regs s) rsp) | mem-ok
... | just .v | refl = refl

-- Helper: state after executing push reg
execPush-reg : ∀ (prog : List Instr) (s : State) (r : Reg) →
  execInstr prog s (push (reg r)) ≡
    just (record s { regs = writeReg (regs s) rsp (readReg (regs s) rsp ∸ 8)
                   ; memory = writeMem (memory s) (readReg (regs s) rsp ∸ 8) (readReg (regs s) r)
                   ; pc = pc s +ℕ 1 })
execPush-reg prog s r = refl

-- Helper: state after executing mov reg, [mem] (load from memory)
execMov-reg-mem : ∀ (prog : List Instr) (s : State) (dst : Reg) (m : Mem) (v : Word) →
  readMem (memory s) (effectiveAddr s m) ≡ just v →
  execInstr prog s (mov (reg dst) (mem m)) ≡
    just (record s { regs = writeReg (regs s) dst v
                   ; pc = pc s +ℕ 1 })
execMov-reg-mem prog s dst m v mem-ok with readMem (memory s) (effectiveAddr s m) | mem-ok
... | just .v | refl = refl

-- Helper: state after executing call reg
execCall-reg : ∀ (prog : List Instr) (s : State) (r : Reg) →
  execInstr prog s (call (reg r)) ≡
    just (record s { pc = readReg (regs s) r })
execCall-reg prog s r = refl

-- Helper: state after executing ret
execRet : ∀ (prog : List Instr) (s : State) →
  execInstr prog s ret ≡ just (record s { halted = true })
execRet prog s = refl

-- Helper: state after executing ud2 (undefined instruction)
execUd2 : ∀ (prog : List Instr) (s : State) →
  execInstr prog s ud2 ≡ just (record s { halted = true })
execUd2 prog s = refl
