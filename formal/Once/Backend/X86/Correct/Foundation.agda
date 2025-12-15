------------------------------------------------------------------------
-- Once.Backend.X86.Correct.Foundation
--
-- Foundational lemmas for x86-64 code generation correctness proofs.
-- Contains: initial state, instruction execution helpers, register lemmas,
-- memory lemmas, fetch/step lemmas, and compile-length correctness.
--
-- This module has no dependencies on other Correct.* modules and can be
-- type-checked independently, improving incremental compilation.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.Foundation where

open import Once.Type
open import Once.IR
open import Once.Semantics

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State
open Once.Backend.X86.Semantics.Flags
open import Once.Backend.X86.CodeGen

-- Import common fetch lemmas (polymorphic, work with any instruction type)
open import Once.Backend.Common.Fetch
  using ( fetch-0; fetch-1; fetch-2; fetch-3
        ; fetch-1-single; fetch-4-of-4
        ; fetch-append-left; fetch-append-right
        )
  public

-- Import common memory helper lemmas
open import Once.Backend.Common.Memory
  using (≡ᵇ-refl; n≢n+suc; readMem-writeMem-same; readMem-writeMem-diff)
  public

-- Import encoding axioms from central postulates module
open import Once.Postulates public
  using ( encode
        ; encode-unit
        ; encode-pair-fst
        ; encode-pair-snd
        ; encode-inl-tag
        ; encode-inl-val
        ; encode-inr-tag
        ; encode-inr-val
        ; encode-inl-construct
        ; encode-inr-construct
        ; encode-fix-unwrap
        ; encode-fix-wrap
        ; encode-arr-identity
        ; encode-pair-construct
        ; encode-closure-construct
        )

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

------------------------------------------------------------------------
-- Initial State Setup
------------------------------------------------------------------------

-- | Create initial state with input in rdi
--
-- Sets up machine state ready to execute generated code:
--   - rdi contains encoded input
--   - Memory contains encoded heap objects
--   - Other registers initialized to 0
--   - Stack pointer set appropriately

-- | Initial state with input value (concrete definition)
--
-- We set up the state with:
--   - rdi = encode x (input)
--   - rsp = large value (stack pointer)
--   - pc = 0
--   - halted = false
--   - Memory contains encoded representation of x (postulated)
initWithInput : ∀ {A} → ⟦ A ⟧ → State
initWithInput {A} x = mkstate
  (writeReg (writeReg emptyRegFile rdi (encode x)) rsp stackBase)
  encodedMemory
  initFlags
  0
  false
  where
    -- Stack starts at a high address
    stackBase : Word
    stackBase = 0x7FFF0000

    -- Memory containing encoded values
    -- The encoding postulates (encode-pair-fst, encode-inl-tag, etc.) in
    -- Once.Postulates already assert that reading from any memory at
    -- encode addresses returns the correct components. This models a
    -- "magic heap" where all semantic values are pre-allocated.
    -- We use emptyMemory here; the encoding postulates handle the rest.
    encodedMemory : Memory
    encodedMemory = emptyMemory

-- | The input is placed in rdi (proven from definition)
--
-- Proof: regs (initWithInput x) = writeReg (writeReg emptyRegFile rdi (encode x)) rsp stackBase
-- readReg on rdi extracts get-rdi, which is (encode x) since we wrote rdi first then rsp.
initWithInput-rdi : ∀ {A} (x : ⟦ A ⟧) →
  readReg (regs (initWithInput x)) rdi ≡ encode x
initWithInput-rdi x = refl

-- | Initial state is not halted (proven from definition)
initWithInput-halted : ∀ {A} (x : ⟦ A ⟧) → halted (initWithInput x) ≡ false
initWithInput-halted x = refl

-- | Initial state has pc = 0 (proven from definition)
initWithInput-pc : ∀ {A} (x : ⟦ A ⟧) → pc (initWithInput x) ≡ 0
initWithInput-pc x = refl

------------------------------------------------------------------------
-- Instruction Execution Helpers
------------------------------------------------------------------------

-- Helper: state after executing mov reg reg
-- Proof: readOperand (reg src) = just (readReg (regs s) src), so the with clause
-- matches and we get writeOperand + increment pc, which computes to the expected state.
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
-- Proof: with-match on readOperand, which equals readMem for memory operands
execMov-reg-mem-base : ∀ (s : State) (dst src : Reg) (v : ℕ) →
  readMem (memory s) (readReg (regs s) src) ≡ just v →
  execInstr [] s (mov (reg dst) (mem (base src))) ≡
    just (record s { regs = writeReg (regs s) dst v
                   ; pc = pc s +ℕ 1 })
execMov-reg-mem-base s dst src v mem-ok with readMem (memory s) (readReg (regs s) src) | mem-ok
... | just .v | refl = refl

-- Helper: state after executing mov reg [reg+disp] (memory load with displacement)
-- Proof: with-match on readOperand, effectiveAddr computes to (reg s src + disp)
execMov-reg-mem-disp : ∀ (s : State) (dst src : Reg) (disp v : ℕ) →
  readMem (memory s) (readReg (regs s) src +ℕ disp) ≡ just v →
  execInstr [] s (mov (reg dst) (mem (base+disp src disp))) ≡
    just (record s { regs = writeReg (regs s) dst v
                   ; pc = pc s +ℕ 1 })
execMov-reg-mem-disp s dst src disp v mem-ok with readMem (memory s) (readReg (regs s) src +ℕ disp) | mem-ok
... | just .v | refl = refl

-- Helper: state after executing mov [reg] imm (memory store)
-- Proof: readOperand (imm v) = just v (always succeeds), so no with-matching needed
execMov-mem-base-imm : ∀ (prog : List Instr) (s : State) (dst : Reg) (v : ℕ) →
  execInstr prog s (mov (mem (base dst)) (imm v)) ≡
    just (record s { memory = writeMem (memory s) (readReg (regs s) dst) v
                   ; pc = pc s +ℕ 1 })
execMov-mem-base-imm prog s dst v = refl

-- Helper: state after executing mov [reg+disp] reg (memory store)
-- Proof: readOperand (reg src) = just (readReg regs src) (always succeeds)
execMov-mem-disp-reg : ∀ (prog : List Instr) (s : State) (dst src : Reg) (disp : ℕ) →
  execInstr prog s (mov (mem (base+disp dst disp)) (reg src)) ≡
    just (record s { memory = writeMem (memory s) (readReg (regs s) dst +ℕ disp) (readReg (regs s) src)
                   ; pc = pc s +ℕ 1 })
execMov-mem-disp-reg prog s dst src disp = refl

-- Helper: state after executing mov [reg] reg (memory store from register)
-- Proof: readOperand (reg src) = just (readReg regs src) (always succeeds)
execMov-mem-base-reg : ∀ (prog : List Instr) (s : State) (dst src : Reg) →
  execInstr prog s (mov (mem (base dst)) (reg src)) ≡
    just (record s { memory = writeMem (memory s) (readReg (regs s) dst) (readReg (regs s) src)
                   ; pc = pc s +ℕ 1 })
execMov-mem-base-reg prog s dst src = refl

-- Helper: state after executing sub reg imm
-- Proof: both readOperand (reg dst) and readOperand (imm v) always succeed
execSub-reg-imm : ∀ (prog : List Instr) (s : State) (dst : Reg) (v : ℕ) →
  execInstr prog s (sub (reg dst) (imm v)) ≡
    just (record s { regs = writeReg (regs s) dst (readReg (regs s) dst ∸ v)
                   ; pc = pc s +ℕ 1
                   ; flags = updateFlags (readReg (regs s) dst ∸ v) (readReg (regs s) dst) })
execSub-reg-imm prog s dst v = refl

-- Helper: state after executing jmp target
-- Proof: jmp has no with-clause, just sets pc to target
execJmp : ∀ (prog : List Instr) (s : State) (target : ℕ) →
  execInstr prog s (jmp target) ≡ just (record s { pc = target })
execJmp prog s target = refl

-- Helper: state after executing cmp (reg r) (imm 0) when r contains 0
-- This is the specific case we need for case analysis (tag comparison)
execCmp-zero : ∀ (prog : List Instr) (s : State) (r : Reg) →
  readReg (regs s) r ≡ 0 →
  execInstr prog s (cmp (reg r) (imm 0)) ≡
    just (record s { pc = pc s +ℕ 1 ; flags = mkflags true false false })
execCmp-zero prog s r eq rewrite eq = refl

-- Helper: state after executing jne when ZF = true (not taken)
-- Proof: when zf = true, pc := pc + 1
execJne-not-taken : ∀ (prog : List Instr) (s : State) (target : ℕ) →
  zf (flags s) ≡ true →
  execInstr prog s (jne target) ≡ just (record s { pc = pc s +ℕ 1 })
execJne-not-taken prog s target zf-true rewrite zf-true = refl

-- Helper: state after executing jne when ZF = false (taken)
-- Proof: when zf = false, pc := target
execJne-taken : ∀ (prog : List Instr) (s : State) (target : ℕ) →
  zf (flags s) ≡ false →
  execInstr prog s (jne target) ≡ just (record s { pc = target })
execJne-taken prog s target zf-false rewrite zf-false = refl

-- Helper: label is a no-op, just advances pc
execLabel : ∀ (prog : List Instr) (s : State) (n : ℕ) →
  execInstr prog s (label n) ≡ just (record s { pc = pc s +ℕ 1 })
execLabel prog s n = refl

-- Helper: state after executing pop reg
-- Requires proof that memory at rsp is defined (contains value v)
execPop : ∀ (prog : List Instr) (s : State) (r : Reg) (v : Word) →
  readMem (memory s) (readReg (regs s) rsp) ≡ just v →
  execInstr prog s (pop r) ≡
    just (record s { regs = writeReg (writeReg (regs s) r v) rsp (readReg (regs s) rsp +ℕ 8)
                   ; pc = pc s +ℕ 1 })
execPop prog s r v mem-ok with readMem (memory s) (readReg (regs s) rsp) | mem-ok
... | just .v | refl = refl

-- Helper: state after executing push reg
-- Push decrements rsp by 8, writes the register value to the new rsp location
execPush-reg : ∀ (prog : List Instr) (s : State) (r : Reg) →
  execInstr prog s (push (reg r)) ≡
    just (record s { regs = writeReg (regs s) rsp (readReg (regs s) rsp ∸ 8)
                   ; memory = writeMem (memory s) (readReg (regs s) rsp ∸ 8) (readReg (regs s) r)
                   ; pc = pc s +ℕ 1 })
execPush-reg prog s r = refl

------------------------------------------------------------------------
-- Register File Lemmas
------------------------------------------------------------------------

-- | Reading a register after writing to it returns the written value
-- This holds because both readReg and writeReg pattern-match on the same register.
readReg-writeReg-same : ∀ (rf : RegFile) (r : Reg) (v : Word) →
  readReg (writeReg rf r v) r ≡ v
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

-- | Reading rdi after writing rsp returns the old value
-- This is what we need for run-inl-seq
readReg-writeReg-rsp-rdi : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf rsp v) rdi ≡ readReg rf rdi
readReg-writeReg-rsp-rdi rf v = refl

-- | Reading rdi after writing r14 returns the old value
readReg-writeReg-r14-rdi : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf r14 v) rdi ≡ readReg rf rdi
readReg-writeReg-r14-rdi rf v = refl

-- | Reading rsp after writing r14 returns the old value
readReg-writeReg-r14-rsp : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf r14 v) rsp ≡ readReg rf rsp
readReg-writeReg-r14-rsp rf v = refl

-- | Reading r14 after writing rax returns the old value
readReg-writeReg-rax-r14 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf rax v) r14 ≡ readReg rf r14
readReg-writeReg-rax-r14 rf v = refl

-- | Reading rsp after writing rax returns the old value
readReg-writeReg-rax-rsp : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf rax v) rsp ≡ readReg rf rsp
readReg-writeReg-rax-rsp rf v = refl

-- | Reading rsp after writing rdi returns the old value
readReg-writeReg-rdi-rsp : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf rdi v) rsp ≡ readReg rf rsp
readReg-writeReg-rdi-rsp rf v = refl

-- | Reading rax after writing rsp returns the old value
readReg-writeReg-rsp-rax : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf rsp v) rax ≡ readReg rf rax
readReg-writeReg-rsp-rax rf v = refl

-- | Reading r15 after writing rsp returns the old value
readReg-writeReg-rsp-r15 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf rsp v) r15 ≡ readReg rf r15
readReg-writeReg-rsp-r15 rf v = refl

-- | Reading r14 after writing rsp returns the old value
readReg-writeReg-rsp-r14 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf rsp v) r14 ≡ readReg rf r14
readReg-writeReg-rsp-r14 rf v = refl

-- | Reading rax after writing r15 returns the old value
readReg-writeReg-r15-rax : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf r15 v) rax ≡ readReg rf rax
readReg-writeReg-r15-rax rf v = refl

-- | Reading rdi after writing r15 returns the old value
readReg-writeReg-r15-rdi : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf r15 v) rdi ≡ readReg rf rdi
readReg-writeReg-r15-rdi rf v = refl

-- | Reading rsp after writing r15 returns the old value
readReg-writeReg-r15-rsp : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf r15 v) rsp ≡ readReg rf rsp
readReg-writeReg-r15-rsp rf v = refl

-- | Reading rax after writing r14 returns the old value
readReg-writeReg-r14-rax : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf r14 v) rax ≡ readReg rf rax
readReg-writeReg-r14-rax rf v = refl

-- | Reading r15 after writing r14 returns the old value
readReg-writeReg-r14-r15 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf r14 v) r15 ≡ readReg rf r15
readReg-writeReg-r14-r15 rf v = refl

-- | Reading r14 after writing rdi returns the old value
readReg-writeReg-rdi-r14 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf rdi v) r14 ≡ readReg rf r14
readReg-writeReg-rdi-r14 rf v = refl

-- | Reading r15 after writing rdi returns the old value
readReg-writeReg-rdi-r15 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf rdi v) r15 ≡ readReg rf r15
readReg-writeReg-rdi-r15 rf v = refl

-- | Reading rax after writing rdi returns the old value
readReg-writeReg-rdi-rax : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf rdi v) rax ≡ readReg rf rax
readReg-writeReg-rdi-rax rf v = refl

-- | Reading r15 after writing rax returns the old value
readReg-writeReg-rax-r15 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf rax v) r15 ≡ readReg rf r15
readReg-writeReg-rax-r15 rf v = refl

-- | Reading rdi after writing rax returns the old value
readReg-writeReg-rax-rdi : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf rax v) rdi ≡ readReg rf rdi
readReg-writeReg-rax-rdi rf v = refl

------------------------------------------------------------------------
-- Memory Lemmas
------------------------------------------------------------------------

open import Data.Nat.Properties using (+-comm; +-assoc; +-identityʳ; m+[n∸m]≡n; ∸-+-assoc)

-- Memory read/write lemmas now imported from Once.Backend.Common.Memory:
--   readMem-writeMem-same, readMem-writeMem-diff

------------------------------------------------------------------------
-- Fetch and Step Lemmas
------------------------------------------------------------------------

-- Fetch lemmas (fetch-0 through fetch-3, fetch-append-left/right, fetch-N-single, etc.)
-- are now imported from Once.Backend.Common.Fetch.

-- | Step on non-halted state executes the instruction at pc
-- Proof: match on halted s, then on fetch prog (pc s)
step-exec : ∀ (prog : List Instr) (s : State) (i : Instr) →
  halted s ≡ false →
  fetch prog (pc s) ≡ just i →
  step prog s ≡ execInstr prog s i
step-exec prog s i h-false fetch-ok with halted s | h-false
... | false | refl with fetch prog (pc s) | fetch-ok
...   | just .i | refl = refl

-- | Step on non-halted state with pc=0 executes the first instruction
step-exec-0 : ∀ (i : Instr) (is : List Instr) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  step (i ∷ is) s ≡ execInstr (i ∷ is) s i
step-exec-0 i is s h-false pc-0 =
  step-exec (i ∷ is) s i h-false (subst (λ p → fetch (i ∷ is) p ≡ just i) (sym pc-0) refl)

-- | Step on non-halted state with pc=1 executes the second instruction
step-exec-1 : ∀ (i0 i1 : Instr) (is : List Instr) (s : State) →
  halted s ≡ false →
  pc s ≡ 1 →
  step (i0 ∷ i1 ∷ is) s ≡ execInstr (i0 ∷ i1 ∷ is) s i1
step-exec-1 i0 i1 is s h-false pc-1 =
  step-exec (i0 ∷ i1 ∷ is) s i1 h-false (subst (λ p → fetch (i0 ∷ i1 ∷ is) p ≡ just i1) (sym pc-1) refl)

-- | Step on non-halted state with pc=2 executes the third instruction
step-exec-2 : ∀ (i0 i1 i2 : Instr) (is : List Instr) (s : State) →
  halted s ≡ false →
  pc s ≡ 2 →
  step (i0 ∷ i1 ∷ i2 ∷ is) s ≡ execInstr (i0 ∷ i1 ∷ i2 ∷ is) s i2
step-exec-2 i0 i1 i2 is s h-false pc-2 =
  step-exec (i0 ∷ i1 ∷ i2 ∷ is) s i2 h-false (subst (λ p → fetch (i0 ∷ i1 ∷ i2 ∷ is) p ≡ just i2) (sym pc-2) refl)

-- | Step on non-halted state with pc=3 executes the fourth instruction
step-exec-3 : ∀ (i0 i1 i2 i3 : Instr) (is : List Instr) (s : State) →
  halted s ≡ false →
  pc s ≡ 3 →
  step (i0 ∷ i1 ∷ i2 ∷ i3 ∷ is) s ≡ execInstr (i0 ∷ i1 ∷ i2 ∷ i3 ∷ is) s i3
step-exec-3 i0 i1 i2 i3 is s h-false pc-3 =
  step-exec (i0 ∷ i1 ∷ i2 ∷ i3 ∷ is) s i3 h-false (subst (λ p → fetch (i0 ∷ i1 ∷ i2 ∷ i3 ∷ is) p ≡ just i3) (sym pc-3) refl)

-- | Fetching at index 4 returns the fifth instruction
fetch-4 : ∀ (i0 i1 i2 i3 i4 : Instr) (is : List Instr) → fetch (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ is) 4 ≡ just i4
fetch-4 i0 i1 i2 i3 i4 is = refl

-- | Fetching at index 5 returns the sixth instruction
fetch-5 : ∀ (i0 i1 i2 i3 i4 i5 : Instr) (is : List Instr) → fetch (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ is) 5 ≡ just i5
fetch-5 i0 i1 i2 i3 i4 i5 is = refl

-- | Fetching at index 6 returns the seventh instruction
fetch-6 : ∀ (i0 i1 i2 i3 i4 i5 i6 : Instr) (is : List Instr) → fetch (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ is) 6 ≡ just i6
fetch-6 i0 i1 i2 i3 i4 i5 i6 is = refl

-- | Fetching at index 7 returns the eighth instruction
fetch-7 : ∀ (i0 i1 i2 i3 i4 i5 i6 i7 : Instr) (is : List Instr) → fetch (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ i7 ∷ is) 7 ≡ just i7
fetch-7 i0 i1 i2 i3 i4 i5 i6 i7 is = refl

-- | Fetching at index 8 returns the ninth instruction
fetch-8 : ∀ (i0 i1 i2 i3 i4 i5 i6 i7 i8 : Instr) (is : List Instr) → fetch (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ i7 ∷ i8 ∷ is) 8 ≡ just i8
fetch-8 i0 i1 i2 i3 i4 i5 i6 i7 i8 is = refl

-- | Fetching at index 9 returns the tenth instruction
fetch-9 : ∀ (i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 : Instr) (is : List Instr) → fetch (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ i7 ∷ i8 ∷ i9 ∷ is) 9 ≡ just i9
fetch-9 i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 is = refl

------------------------------------------------------------------------
-- Fetch Lemmas for List Concatenation
------------------------------------------------------------------------

-- | Fetching past a prefix goes into the suffix
-- fetch (xs ++ ys) (length xs + n) ≡ fetch ys n
fetch-append-skip : ∀ (xs ys : List Instr) (n : ℕ) →
  fetch (xs ++ ys) (length xs +ℕ n) ≡ fetch ys n
fetch-append-skip [] ys n = refl
fetch-append-skip (x ∷ xs) ys n = fetch-append-skip xs ys n

-- | Fetching past the end of a list returns nothing
fetch-past-length : ∀ (xs : List Instr) (n : ℕ) →
  fetch xs (length xs +ℕ n) ≡ nothing
fetch-past-length [] n = refl
fetch-past-length (x ∷ xs) n = fetch-past-length xs n

-- | Length of concatenated lists
length-++ : ∀ (xs ys : List Instr) → length (xs ++ ys) ≡ length xs +ℕ length ys
length-++ [] ys = refl
length-++ (x ∷ xs) ys = cong suc (length-++ xs ys)

------------------------------------------------------------------------
-- Compile-length Correctness
------------------------------------------------------------------------

-- | compile-length correctly computes the length of compile-x86
-- This is essential for proving fetch lemmas at computed positions
compile-length-correct : ∀ {A B} (ir : IR A B) →
  length (compile-x86 ir) ≡ compile-length ir
compile-length-correct id = refl
compile-length-correct (g ∘ f) = helper
  where
    -- Key insight: a + suc b = a + (1 + b) = (a + 1) + b
    -- Since 1 + b = suc b definitionally, we just need +-assoc
    a+suc≡a+1+ : ∀ a b → a +ℕ suc b ≡ (a +ℕ 1) +ℕ b
    a+suc≡a+1+ a b = sym (+-assoc a 1 b)

    helper : length (compile-x86 f ++ mov (reg rdi) (reg rax) ∷ compile-x86 g) ≡
             (compile-length f +ℕ 1) +ℕ compile-length g
    helper =
      begin
        length (compile-x86 f ++ mov (reg rdi) (reg rax) ∷ compile-x86 g)
      ≡⟨ length-++ (compile-x86 f) _ ⟩
        length (compile-x86 f) +ℕ suc (length (compile-x86 g))
      ≡⟨ cong (λ x → x +ℕ suc (length (compile-x86 g))) (compile-length-correct f) ⟩
        compile-length f +ℕ suc (length (compile-x86 g))
      ≡⟨ cong (λ x → compile-length f +ℕ suc x) (compile-length-correct g) ⟩
        compile-length f +ℕ suc (compile-length g)
      ≡⟨ a+suc≡a+1+ (compile-length f) (compile-length g) ⟩
        (compile-length f +ℕ 1) +ℕ compile-length g
      ∎
compile-length-correct fst = refl
compile-length-correct snd = refl
compile-length-correct ⟨ f , g ⟩ = helper
  where
    -- Structure: push ∷ push ∷ sub ∷ mov ∷ mov ∷
    --            (compile-x86 f ++ mov ∷ mov ∷
    --             (compile-x86 g ++ mov ∷ mov ∷ pop ∷ pop ∷ []))
    -- We need to show: 5 + (|f| + (2 + (|g| + 4))) = (11 + |f|) + |g|

    inner-tail : List Instr
    inner-tail = mov (mem (base+disp r15 8)) (reg rax) ∷
                 mov (reg rax) (reg r15) ∷
                 pop r15 ∷
                 pop r14 ∷ []

    -- Lemma: length of the trailing part after g
    len-middle : length (compile-x86 g ++ inner-tail) ≡ compile-length g +ℕ 4
    len-middle = trans (length-++ (compile-x86 g) inner-tail) (cong (λ x → x +ℕ 4) (compile-length-correct g))

    mid-tail : List Instr
    mid-tail = mov (mem (base r15)) (reg rax) ∷ mov (reg rdi) (reg r14) ∷ (compile-x86 g ++ inner-tail)

    -- Lemma: length after f
    len-after-f : length mid-tail ≡ 2 +ℕ (compile-length g +ℕ 4)
    len-after-f = cong (λ x → 2 +ℕ x) len-middle

    full-tail : List Instr
    full-tail = compile-x86 f ++ mid-tail

    -- Lemma: length including f
    len-with-f : length full-tail ≡ compile-length f +ℕ (2 +ℕ (compile-length g +ℕ 4))
    len-with-f = trans (length-++ (compile-x86 f) mid-tail)
                       (trans (cong (λ x → x +ℕ length mid-tail) (compile-length-correct f))
                              (cong (λ x → compile-length f +ℕ x) len-after-f))

    -- Prove: 5 + (a + (2 + (b + 4))) = (11 + a) + b
    -- Using +-comm and +-assoc with equational reasoning
    arith2 : ∀ a b → 5 +ℕ (a +ℕ (2 +ℕ (b +ℕ 4))) ≡ (11 +ℕ a) +ℕ b
    arith2 a b =
      begin
        5 +ℕ (a +ℕ (2 +ℕ (b +ℕ 4)))
      ≡⟨ cong (5 +ℕ_) (cong (a +ℕ_) (cong (2 +ℕ_) (+-comm b 4))) ⟩
        5 +ℕ (a +ℕ (2 +ℕ (4 +ℕ b)))
      ≡⟨ cong (5 +ℕ_) (cong (a +ℕ_) (sym (+-assoc 2 4 b))) ⟩
        5 +ℕ (a +ℕ (6 +ℕ b))
      ≡⟨ cong (5 +ℕ_) (sym (+-assoc a 6 b)) ⟩
        5 +ℕ ((a +ℕ 6) +ℕ b)
      ≡⟨ cong (5 +ℕ_) (cong (_+ℕ b) (+-comm a 6)) ⟩
        5 +ℕ ((6 +ℕ a) +ℕ b)
      ≡⟨ sym (+-assoc 5 (6 +ℕ a) b) ⟩
        (5 +ℕ (6 +ℕ a)) +ℕ b
      ≡⟨ cong (_+ℕ b) (sym (+-assoc 5 6 a)) ⟩
        (11 +ℕ a) +ℕ b
      ∎

    helper : length (compile-x86 ⟨ f , g ⟩) ≡ (11 +ℕ compile-length f) +ℕ compile-length g
    helper = trans (cong (λ x → 5 +ℕ x) len-with-f)
                   (arith2 (compile-length f) (compile-length g))
compile-length-correct inl = refl
compile-length-correct inr = refl
compile-length-correct [ f , g ] = helper
  where
    -- Structure: mov ∷ cmp ∷ jne ∷ mov ∷ (compile-x86 f ++ jmp ∷ label ∷ mov ∷ (compile-x86 g ++ label ∷ []))
    -- Length = 4 + (|f| + (3 + (|g| + 1))) = (8 + |f|) + |g|

    end-lbl : ℕ
    end-lbl = (7 +ℕ compile-length f) +ℕ compile-length g

    right-lbl : ℕ
    right-lbl = 5 +ℕ compile-length f

    inner-tail : List Instr
    inner-tail = label end-lbl ∷ []

    len-inner : length (compile-x86 g ++ inner-tail) ≡ compile-length g +ℕ 1
    len-inner = trans (length-++ (compile-x86 g) inner-tail)
                      (cong (λ x → x +ℕ 1) (compile-length-correct g))

    mid-tail : List Instr
    mid-tail = jmp end-lbl ∷ label right-lbl ∷ mov (reg rdi) (mem (base+disp rdi 8)) ∷
               (compile-x86 g ++ inner-tail)

    len-mid : length mid-tail ≡ 3 +ℕ (compile-length g +ℕ 1)
    len-mid = cong (λ x → 3 +ℕ x) len-inner

    full-tail : List Instr
    full-tail = compile-x86 f ++ mid-tail

    len-with-f : length full-tail ≡ compile-length f +ℕ (3 +ℕ (compile-length g +ℕ 1))
    len-with-f = trans (length-++ (compile-x86 f) mid-tail)
                       (trans (cong (λ x → x +ℕ length mid-tail) (compile-length-correct f))
                              (cong (λ x → compile-length f +ℕ x) len-mid))

    -- Prove: 4 + (a + (3 + (b + 1))) = (8 + a) + b
    arith : ∀ a b → 4 +ℕ (a +ℕ (3 +ℕ (b +ℕ 1))) ≡ (8 +ℕ a) +ℕ b
    arith a b =
      begin
        4 +ℕ (a +ℕ (3 +ℕ (b +ℕ 1)))
      ≡⟨ cong (4 +ℕ_) (cong (a +ℕ_) (cong (3 +ℕ_) (+-comm b 1))) ⟩
        4 +ℕ (a +ℕ (3 +ℕ (1 +ℕ b)))
      ≡⟨ cong (4 +ℕ_) (cong (a +ℕ_) (sym (+-assoc 3 1 b))) ⟩
        4 +ℕ (a +ℕ (4 +ℕ b))
      ≡⟨ cong (4 +ℕ_) (sym (+-assoc a 4 b)) ⟩
        4 +ℕ ((a +ℕ 4) +ℕ b)
      ≡⟨ cong (4 +ℕ_) (cong (_+ℕ b) (+-comm a 4)) ⟩
        4 +ℕ ((4 +ℕ a) +ℕ b)
      ≡⟨ sym (+-assoc 4 (4 +ℕ a) b) ⟩
        (4 +ℕ (4 +ℕ a)) +ℕ b
      ≡⟨ cong (_+ℕ b) (sym (+-assoc 4 4 a)) ⟩
        (8 +ℕ a) +ℕ b
      ∎

    helper : length (compile-x86 [ f , g ]) ≡ (8 +ℕ compile-length f) +ℕ compile-length g
    helper = trans (cong (λ x → 4 +ℕ x) len-with-f)
                   (arith (compile-length f) (compile-length g))
compile-length-correct terminal = refl
compile-length-correct initial = refl
compile-length-correct (curry f) = helper
  where
    -- Structure: sub ∷ mov ∷ mov ∷ mov ∷ jmp ∷ label ∷ sub ∷ mov ∷ mov ∷ mov ∷ (compile-x86 f ++ ret ∷ label ∷ [])
    -- Length = 10 + (|f| + 2) = 12 + |f|

    end-lbl : ℕ
    end-lbl = 11 +ℕ compile-length f

    inner-tail : List Instr
    inner-tail = ret ∷ label end-lbl ∷ []

    len-inner : length (compile-x86 f ++ inner-tail) ≡ compile-length f +ℕ 2
    len-inner = trans (length-++ (compile-x86 f) inner-tail)
                      (cong (λ x → x +ℕ 2) (compile-length-correct f))

    -- Prove: 10 + (a + 2) = 12 + a
    arith : ∀ a → 10 +ℕ (a +ℕ 2) ≡ 12 +ℕ a
    arith a =
      begin
        10 +ℕ (a +ℕ 2)
      ≡⟨ cong (10 +ℕ_) (+-comm a 2) ⟩
        10 +ℕ (2 +ℕ a)
      ≡⟨ sym (+-assoc 10 2 a) ⟩
        12 +ℕ a
      ∎

    helper : length (compile-x86 (curry f)) ≡ 12 +ℕ compile-length f
    helper = trans (cong (λ x → 10 +ℕ x) len-inner)
                   (arith (compile-length f))
compile-length-correct apply = refl
compile-length-correct fold = refl
compile-length-correct unfold = refl
compile-length-correct arr = refl

------------------------------------------------------------------------
-- Additional Step Lemmas
------------------------------------------------------------------------

-- | Step on non-halted state with pc=4 executes the fifth instruction
step-exec-4 : ∀ (i0 i1 i2 i3 i4 : Instr) (is : List Instr) (s : State) →
  halted s ≡ false →
  pc s ≡ 4 →
  step (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ is) s ≡ execInstr (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ is) s i4
step-exec-4 i0 i1 i2 i3 i4 is s h-false pc-4 =
  step-exec (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ is) s i4 h-false (subst (λ p → fetch (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ is) p ≡ just i4) (sym pc-4) refl)

-- | Step on non-halted state with pc=5 executes the sixth instruction
step-exec-5 : ∀ (i0 i1 i2 i3 i4 i5 : Instr) (is : List Instr) (s : State) →
  halted s ≡ false →
  pc s ≡ 5 →
  step (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ is) s ≡ execInstr (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ is) s i5
step-exec-5 i0 i1 i2 i3 i4 i5 is s h-false pc-5 =
  step-exec (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ is) s i5 h-false (subst (λ p → fetch (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ is) p ≡ just i5) (sym pc-5) refl)

-- | Step on non-halted state with pc=6 executes the seventh instruction
step-exec-6 : ∀ (i0 i1 i2 i3 i4 i5 i6 : Instr) (is : List Instr) (s : State) →
  halted s ≡ false →
  pc s ≡ 6 →
  step (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ is) s ≡ execInstr (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ is) s i6
step-exec-6 i0 i1 i2 i3 i4 i5 i6 is s h-false pc-6 =
  step-exec (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ is) s i6 h-false (subst (λ p → fetch (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ is) p ≡ just i6) (sym pc-6) refl)

-- | Step on non-halted state with pc=7 executes the eighth instruction
step-exec-7 : ∀ (i0 i1 i2 i3 i4 i5 i6 i7 : Instr) (is : List Instr) (s : State) →
  halted s ≡ false →
  pc s ≡ 7 →
  step (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ i7 ∷ is) s ≡ execInstr (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ i7 ∷ is) s i7
step-exec-7 i0 i1 i2 i3 i4 i5 i6 i7 is s h-false pc-7 =
  step-exec (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ i7 ∷ is) s i7 h-false (subst (λ p → fetch (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ i7 ∷ is) p ≡ just i7) (sym pc-7) refl)

step-exec-8 : ∀ (i0 i1 i2 i3 i4 i5 i6 i7 i8 : Instr) (is : List Instr) (s : State) →
  halted s ≡ false →
  pc s ≡ 8 →
  step (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ i7 ∷ i8 ∷ is) s ≡ execInstr (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ i7 ∷ i8 ∷ is) s i8
step-exec-8 i0 i1 i2 i3 i4 i5 i6 i7 i8 is s h-false pc-8 =
  step-exec (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ i7 ∷ i8 ∷ is) s i8 h-false (subst (λ p → fetch (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ i7 ∷ i8 ∷ is) p ≡ just i8) (sym pc-8) refl)

step-exec-9 : ∀ (i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 : Instr) (is : List Instr) (s : State) →
  halted s ≡ false →
  pc s ≡ 9 →
  step (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ i7 ∷ i8 ∷ i9 ∷ is) s ≡ execInstr (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ i7 ∷ i8 ∷ i9 ∷ is) s i9
step-exec-9 i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 is s h-false pc-9 =
  step-exec (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ i7 ∷ i8 ∷ i9 ∷ is) s i9 h-false (subst (λ p → fetch (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ i7 ∷ i8 ∷ i9 ∷ is) p ≡ just i9) (sym pc-9) refl)

-- | Step on non-halted state where fetch fails sets halted=true
-- Proof: match on halted s, then on fetch prog (pc s)
step-halt-on-fetch-fail : ∀ (prog : List Instr) (s : State) →
  halted s ≡ false →
  fetch prog (pc s) ≡ nothing →
  step prog s ≡ just (record s { halted = true })
step-halt-on-fetch-fail prog s h-false fetch-fail with halted s | h-false
... | false | refl with fetch prog (pc s) | fetch-fail
...   | nothing | refl = refl

-- | Step on already halted state returns the same state
step-on-halted : ∀ (prog : List Instr) (s : State) →
  halted s ≡ true →
  step prog s ≡ just s
step-on-halted prog s h-true with halted s
step-on-halted prog s refl | true = refl

-- | Step at arbitrary offset within combined program
-- Key lemma: if pc = length prefix, step executes instruction at that position
step-exec-at-offset : ∀ (prefix : Program) (instr : Instr) (suffix : Program) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  step (prefix ++ instr ∷ suffix) s ≡ execInstr (prefix ++ instr ∷ suffix) s instr
step-exec-at-offset prefix instr suffix s h-false pc-eq =
  step-exec (prefix ++ instr ∷ suffix) s instr h-false fetch-eq
  where
    -- Step 1: fetch (prefix ++ instr ∷ suffix) (length prefix +ℕ 0) ≡ just instr
    fetch-with-plus-0 : fetch (prefix ++ instr ∷ suffix) (length prefix +ℕ 0) ≡ just instr
    fetch-with-plus-0 = fetch-append-right prefix (instr ∷ suffix) 0

    -- Step 2: Use +-identityʳ to rewrite (length prefix +ℕ 0) to (length prefix)
    -- +-identityʳ (length prefix) : (length prefix +ℕ 0) ≡ length prefix
    fetch-at-prefix-len : fetch (prefix ++ instr ∷ suffix) (length prefix) ≡ just instr
    fetch-at-prefix-len = subst (λ n → fetch (prefix ++ instr ∷ suffix) n ≡ just instr)
                                (+-identityʳ (length prefix))
                                fetch-with-plus-0

    -- Step 3: Use pc-eq to rewrite (length prefix) to (pc s)
    -- pc-eq : pc s ≡ length prefix, so sym pc-eq : length prefix ≡ pc s
    fetch-eq : fetch (prefix ++ instr ∷ suffix) (pc s) ≡ just instr
    fetch-eq = subst (λ n → fetch (prefix ++ instr ∷ suffix) n ≡ just instr)
                     (sym pc-eq)
                     fetch-at-prefix-len
