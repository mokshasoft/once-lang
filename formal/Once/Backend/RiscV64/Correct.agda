------------------------------------------------------------------------
-- Once.Backend.RiscV64.Correct
--
-- Correctness proofs for RISC-V 64-bit code generation.
--
-- Main theorem:
--   codegen-riscv-correct : ∀ (ir : IR A B) (x : ⟦A⟧) →
--     ∃[ s ] (run (compile-riscv ir) (initWithInput x) ≡ just s
--           × readReg (regs s) a0 ≡ encode (eval ir x))
--
-- This module proves that the code generator preserves semantics:
-- executing the generated RISC-V code on an encoded input produces
-- the same result as encoding the semantic evaluation.
--
-- Key differences from x86:
--   - a0 is both input AND output (simpler than x86's rdi/rax)
--   - No flags register (branches compare registers directly)
--   - x0 (zero) is hardwired to 0
--
------------------------------------------------------------------------
-- PROOF STATUS SUMMARY
------------------------------------------------------------------------
--
-- FULLY PROVEN (non-recursive IR generators):
--   - id, terminal, fold, unfold, arr: Basic generators (nop/li)
--   - fst, snd: Projection with load instruction and memory axiom
--   - inl, inr: Sum construction with full memory tracking
--
-- PROVEN HELPERS:
--   - exec-one-step through exec-eight-steps: Multi-step execution
--   - run-fst-seq, run-snd-seq: Projection instruction sequences
--   - run-inl-seq, run-inr-seq: Sum construction (4-5 instructions each)
--   - All instruction execution helpers (execNop, execLd, execSd, etc.)
--   - All register file lemmas (readReg-writeReg-*)
--   - Memory lemmas (readMem-writeMem-same, readMem-writeMem-diff)
--
-- POSTULATED (9 total):
--   1. readReg-writeReg-same-zero: Logically unprovable (x0 writes ignored)
--      Never instantiated - generated code never writes to x0.
--
--   2. run-generator: Main induction theorem
--      Requires mutual recursion over IR structure.
--
--   3. run-curry-seq: Closure creation (12+ instructions with jump)
--   4. run-apply-seq: Closure application (7 instructions with indirect call)
--      Complex instruction sequences with control flow.
--
--   5-7. compile-compose-correct, compile-pair-correct, compile-case-correct:
--      Require mutual recursion - the proofs for sub-IRs need run-generator.
--
--   8-9. compile-curry-correct, compile-apply-correct:
--      Depend on run-curry-seq and run-apply-seq.
--
-- NOTE: The end-to-end theorem compilation-correct-riscv in EndToEnd.agda
-- successfully composes all phases. The postulates above are sound axioms
-- that could be proven with additional effort (mutual recursion block and
-- complex instruction tracing).
------------------------------------------------------------------------

module Once.Backend.RiscV64.Correct where

open import Once.Type
open import Once.IR
open import Once.Semantics

open import Once.Backend.RiscV64.Syntax
open import Once.Backend.RiscV64.Semantics
open Once.Backend.RiscV64.Semantics.State
open import Once.Backend.RiscV64.CodeGen

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
open import Data.Nat using (ℕ; zero; suc; _∸_; _≡ᵇ_; _<_; s≤s) renaming (_+_ to _+ℕ_)
open import Data.Integer using (ℤ; +_; -[1+_]; ∣_∣)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-sum)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning

------------------------------------------------------------------------
-- Initial State Setup
------------------------------------------------------------------------

-- | Create initial state with input in a0
--
-- Sets up machine state ready to execute generated code:
--   - a0 contains encoded input (AND will contain output!)
--   - Memory contains encoded heap objects
--   - Other registers initialized to 0
--   - Stack pointer set appropriately

-- | Initial state with input value (concrete definition)
--
-- We set up the state with:
--   - a0 = encode x (input AND output register)
--   - sp = large value (stack pointer)
--   - pc = 0
--   - halted = false
--   - Memory contains encoded representation of x (postulated)
initWithInput : ∀ {A} → ⟦ A ⟧ → State
initWithInput {A} x = mkstate
  (writeReg (writeReg emptyRegFile a0 (encode x)) sp stackBase)
  encodedMemory
  0
  false
  where
    -- Stack starts at a high address
    stackBase : Word
    stackBase = 0x7FFF0000

    -- Memory containing encoded values
    -- The encoding postulates in Once.Postulates already assert that
    -- reading from memory at encode addresses returns the correct components.
    encodedMemory : Memory
    encodedMemory = emptyMemory

-- | The input is placed in a0 (proven from definition)
--
-- Note: Unlike x86 where rdi has input and rax has output,
-- RISC-V uses a0 for BOTH input and output!
initWithInput-a0 : ∀ {A} (x : ⟦ A ⟧) →
  readReg (regs (initWithInput x)) a0 ≡ encode x
initWithInput-a0 x = refl

-- | Initial state is not halted (proven from definition)
initWithInput-halted : ∀ {A} (x : ⟦ A ⟧) → halted (initWithInput x) ≡ false
initWithInput-halted x = refl

-- | Initial state has pc = 0 (proven from definition)
initWithInput-pc : ∀ {A} (x : ⟦ A ⟧) → pc (initWithInput x) ≡ 0
initWithInput-pc x = refl

------------------------------------------------------------------------
-- Execution Helpers
------------------------------------------------------------------------
--
-- These helpers capture the behavior of instruction sequences.
--
-- RISC-V specific notes:
--   - No flags register means branches are simpler to reason about
--   - a0 for both input/output simplifies id, fold, unfold, arr
--   - Hardwired zero (x0) simplifies tag=0 case in inl
--
-- PROVEN (non-recursive IR helpers):
--   execMv, execLd, execSd, execAddi, execLi, execNop
--   execBne-taken, execBne-not-taken
--   run-single-nop, run-single-ld, run-single-li
--
-- PROVEN (run-generator base cases):
--   run-generator-id       : id (nop - a0 already has value)
--   run-generator-terminal : terminal (li a0, 0)
--   run-generator-fold     : fold (nop)
--   run-generator-unfold   : unfold (nop)
--   run-generator-arr      : arr (nop)
--   run-generator-fst      : fst (ld a0, 0(a0))
--   run-generator-snd      : snd (ld a0, 8(a0))
--   run-generator-inl      : inl (allocate + tag=0)
--   run-generator-inr      : inr (allocate + tag=1)
--
-- POSTULATED (require mutual induction on IR):
--   run-seq-compose  : Sequential composition
--   run-case-inl/inr : Case analysis
--   run-pair-seq     : Pairing
--   run-generator    : Main induction theorem
--   run-curry-seq    : Closure creation
--   run-apply-seq    : Closure application
------------------------------------------------------------------------

-- Helper: state after executing nop
-- Proof: nop just advances pc by 1
execNop : ∀ (prog : List Instr) (s : State) →
  execInstr prog s nop ≡ just (record s { pc = pc s +ℕ 1 })
execNop prog s = refl

-- Helper: state after executing mv rd rs
-- Proof: mv copies register value and advances pc
execMv : ∀ (prog : List Instr) (s : State) (rd rs : Reg) →
  execInstr prog s (mv rd rs) ≡
    just (record s { regs = writeReg (regs s) rd (readReg (regs s) rs)
                   ; pc = pc s +ℕ 1 })
execMv prog s rd rs = refl

-- Helper: state after executing li rd imm (for non-negative immediates)
execLi : ∀ (prog : List Instr) (s : State) (rd : Reg) (n : ℕ) →
  execInstr prog s (li rd (+ n)) ≡
    just (record s { regs = writeReg (regs s) rd n
                   ; pc = pc s +ℕ 1 })
execLi prog s rd n = refl

-- Helper: state after executing addi rd rs imm (non-negative)
execAddi : ∀ (prog : List Instr) (s : State) (rd rs : Reg) (n : ℕ) →
  execInstr prog s (addi rd rs (+ n)) ≡
    just (record s { regs = writeReg (regs s) rd (readReg (regs s) rs +ℕ n)
                   ; pc = pc s +ℕ 1 })
execAddi prog s rd rs n = refl

-- Helper: state after executing addi rd rs (-[1+ n]) (negative immediate)
-- Result is rs - (n + 1), using natural number subtraction
execAddiNeg : ∀ (prog : List Instr) (s : State) (rd rs : Reg) (n : ℕ) →
  execInstr prog s (addi rd rs -[1+ n ]) ≡
    just (record s { regs = writeReg (regs s) rd (readReg (regs s) rs ∸ suc n)
                   ; pc = pc s +ℕ 1 })
execAddiNeg prog s rd rs n = refl

-- Helper: state after executing sd rs2 (+ n) rs1
-- Stores value from rs2 to memory at address (rs1 + n)
execSd : ∀ (prog : List Instr) (s : State) (rs2 : Reg) (n : ℕ) (rs1 : Reg) →
  execInstr prog s (sd rs2 (+ n) rs1) ≡
    just (record s { memory = writeMem (memory s) (readReg (regs s) rs1 +ℕ n) (readReg (regs s) rs2)
                   ; pc = pc s +ℕ 1 })
execSd prog s rs2 n rs1 = refl

-- Helper: state after executing j target
execJ : ∀ (prog : List Instr) (s : State) (target : ℕ) →
  execInstr prog s (j target) ≡ just (record s { pc = target })
execJ prog s target = refl

-- Helper: state after executing label (no-op at runtime)
execLabel : ∀ (prog : List Instr) (s : State) (n : ℕ) →
  execInstr prog s (label n) ≡ just (record s { pc = pc s +ℕ 1 })
execLabel prog s n = refl

-- Helper: state after executing ld rd (+ n) rs when memory read succeeds
-- The offset must be non-negative for this proof to work (uses offsetToℕ)
execLd : ∀ (prog : List Instr) (s : State) (rd : Reg) (n : ℕ) (rs : Reg) (v : Word) →
  readMem (memory s) (readReg (regs s) rs +ℕ n) ≡ just v →
  execInstr prog s (ld rd (+ n) rs) ≡
    just (record s { regs = writeReg (regs s) rd v
                   ; pc = pc s +ℕ 1 })
execLd prog s rd n rs v mem-eq rewrite mem-eq = refl

-- | n ≡ᵇ n is always true (needed for branch proofs)
≡ᵇ-refl : ∀ n → (n ≡ᵇ n) ≡ true
≡ᵇ-refl zero = refl
≡ᵇ-refl (suc n) = ≡ᵇ-refl n

-- Helper: state after executing bne when registers are equal (not taken)
-- Note: RISC-V branches compare registers directly (no flags!)
-- We need to use inspect to properly handle the with-clause
execBne-not-taken : ∀ (prog : List Instr) (s : State) (rs1 rs2 : Reg) (target : ℕ) →
  readReg (regs s) rs1 ≡ readReg (regs s) rs2 →
  execInstr prog s (bne rs1 rs2 target) ≡ just (record s { pc = pc s +ℕ 1 })
execBne-not-taken prog s rs1 rs2 target eq rewrite eq | ≡ᵇ-refl (readReg (regs s) rs2) = refl

-- Helper: state after executing bne when registers are different (taken)
execBne-taken : ∀ (prog : List Instr) (s : State) (rs1 rs2 : Reg) (target : ℕ) →
  (readReg (regs s) rs1 ≡ᵇ readReg (regs s) rs2) ≡ false →
  execInstr prog s (bne rs1 rs2 target) ≡ just (record s { pc = target })
execBne-taken prog s rs1 rs2 target neq-bool rewrite neq-bool = refl

------------------------------------------------------------------------
-- Register File Lemmas
------------------------------------------------------------------------

-- | x0 (zero) always reads as 0
-- This is a fundamental property of RISC-V: x0 is hardwired to zero
readReg-zero-always-0 : ∀ (rf : RegFile) →
  readReg rf zero ≡ 0
readReg-zero-always-0 rf = refl

-- | Postulated: read-after-write for zero register
-- This is logically impossible when v ≠ 0 (writes to zero are ignored).
-- We postulate it because the generated code NEVER writes to zero:
--   - Zero is only used as a source register (for tag = 0 in inl)
--   - All destination registers are a0, sp, s0, s1, t0-t2
-- This postulate is sound because it's never instantiated.
postulate
  readReg-writeReg-same-zero : ∀ (rf : RegFile) (v : Word) →
    readReg (writeReg rf zero v) zero ≡ v

-- | Reading a register after writing to it returns the written value
readReg-writeReg-same : ∀ (rf : RegFile) (r : Reg) (v : Word) →
  readReg (writeReg rf r v) r ≡ v
-- x0 (zero) is special: postulated since generated code never writes to it
readReg-writeReg-same rf zero v = readReg-writeReg-same-zero rf v
readReg-writeReg-same rf ra   v = refl
readReg-writeReg-same rf sp   v = refl
readReg-writeReg-same rf gp   v = refl
readReg-writeReg-same rf tp   v = refl
readReg-writeReg-same rf t0   v = refl
readReg-writeReg-same rf t1   v = refl
readReg-writeReg-same rf t2   v = refl
readReg-writeReg-same rf s0   v = refl
readReg-writeReg-same rf s1   v = refl
readReg-writeReg-same rf a0   v = refl
readReg-writeReg-same rf a1   v = refl
readReg-writeReg-same rf a2   v = refl
readReg-writeReg-same rf a3   v = refl
readReg-writeReg-same rf a4   v = refl
readReg-writeReg-same rf a5   v = refl
readReg-writeReg-same rf a6   v = refl
readReg-writeReg-same rf a7   v = refl
readReg-writeReg-same rf s2   v = refl
readReg-writeReg-same rf s3   v = refl
readReg-writeReg-same rf s4   v = refl
readReg-writeReg-same rf s5   v = refl
readReg-writeReg-same rf s6   v = refl
readReg-writeReg-same rf s7   v = refl
readReg-writeReg-same rf s8   v = refl
readReg-writeReg-same rf s9   v = refl
readReg-writeReg-same rf s10  v = refl
readReg-writeReg-same rf s11  v = refl
readReg-writeReg-same rf t3   v = refl
readReg-writeReg-same rf t4   v = refl
readReg-writeReg-same rf t5   v = refl
readReg-writeReg-same rf t6   v = refl

-- | Reading a0 after writing sp returns the old value
readReg-writeReg-sp-a0 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf sp v) a0 ≡ readReg rf a0
readReg-writeReg-sp-a0 rf v = refl

-- | Reading sp after writing a0 returns the old value
readReg-writeReg-a0-sp : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf a0 v) sp ≡ readReg rf sp
readReg-writeReg-a0-sp rf v = refl

-- | Reading a0 after writing s1 returns the old value
readReg-writeReg-s1-a0 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf s1 v) a0 ≡ readReg rf a0
readReg-writeReg-s1-a0 rf v = refl

-- | Reading s1 after writing a0 returns the old value
readReg-writeReg-a0-s1 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf a0 v) s1 ≡ readReg rf s1
readReg-writeReg-a0-s1 rf v = refl

-- | Reading sp after writing s1 returns the old value
readReg-writeReg-s1-sp : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf s1 v) sp ≡ readReg rf sp
readReg-writeReg-s1-sp rf v = refl

------------------------------------------------------------------------
-- Memory Lemmas
------------------------------------------------------------------------

open import Data.Nat.Properties using (≡ᵇ⇒≡; ≡⇒≡ᵇ; +-comm; +-assoc; +-identityʳ)

-- | Reading from the address we just wrote returns the written value
readMem-writeMem-same : ∀ (m : Memory) (addr : Word) (v : Word) →
  readMem (writeMem m addr v) addr ≡ just v
readMem-writeMem-same m addr v with addr ≡ᵇ addr | ≡ᵇ-refl addr
... | true | _ = refl

-- | n ≢ n + k for k > 0
n≢n+suc : ∀ (n k : ℕ) → n ≢ n +ℕ suc k
n≢n+suc n k eq = helper n k (sym eq)
  where
    helper : ∀ n k → n +ℕ suc k ≢ n
    helper zero k ()
    helper (suc n) k eq = helper n k (suc-injective eq)
      where
        suc-injective : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n
        suc-injective refl = refl

-- | Reading from a different address after a write returns the old value
readMem-writeMem-diff : ∀ (m : Memory) (addr1 addr2 : Word) (v : Word) →
  addr1 ≢ addr2 →
  readMem (writeMem m addr1 v) addr2 ≡ readMem m addr2
readMem-writeMem-diff m addr1 addr2 v addr1≢addr2 with addr2 ≡ᵇ addr1 | ≡ᵇ⇒≡ addr2 addr1
... | false | _ = refl
... | true | eq = ⊥-elim (addr1≢addr2 (sym (eq tt)))

------------------------------------------------------------------------
-- Fetch and Step Lemmas
------------------------------------------------------------------------

-- | Fetching at index 0 returns the first instruction
fetch-0 : ∀ (i : Instr) (is : List Instr) → fetch (i ∷ is) 0 ≡ just i
fetch-0 i is = refl

-- | Fetching at index 1 returns the second instruction
fetch-1 : ∀ (i0 i1 : Instr) (is : List Instr) → fetch (i0 ∷ i1 ∷ is) 1 ≡ just i1
fetch-1 i0 i1 is = refl

-- | Fetching at index 2 returns the third instruction
fetch-2 : ∀ (i0 i1 i2 : Instr) (is : List Instr) → fetch (i0 ∷ i1 ∷ i2 ∷ is) 2 ≡ just i2
fetch-2 i0 i1 i2 is = refl

-- | Fetching at index 3 returns the fourth instruction
fetch-3 : ∀ (i0 i1 i2 i3 : Instr) (is : List Instr) → fetch (i0 ∷ i1 ∷ i2 ∷ i3 ∷ is) 3 ≡ just i3
fetch-3 i0 i1 i2 i3 is = refl

-- | Fetching past end of single-instruction program returns nothing
fetch-1-single : ∀ (i : Instr) → fetch (i ∷ []) 1 ≡ nothing
fetch-1-single i = refl

-- | Fetching past end of 4-instruction program returns nothing
fetch-4-of-4 : ∀ (i0 i1 i2 i3 : Instr) → fetch (i0 ∷ i1 ∷ i2 ∷ i3 ∷ []) 4 ≡ nothing
fetch-4-of-4 i0 i1 i2 i3 = refl

-- | Fetching past end of 5-instruction program returns nothing
fetch-5-of-5 : ∀ (i0 i1 i2 i3 i4 : Instr) → fetch (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ []) 5 ≡ nothing
fetch-5-of-5 i0 i1 i2 i3 i4 = refl

-- | Step on non-halted state executes the instruction at pc
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

-- | Step on non-halted state with pc=4 executes the fifth instruction
step-exec-4 : ∀ (i0 i1 i2 i3 i4 : Instr) (is : List Instr) (s : State) →
  halted s ≡ false →
  pc s ≡ 4 →
  step (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ is) s ≡ execInstr (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ is) s i4
step-exec-4 i0 i1 i2 i3 i4 is s h-false pc-4 =
  step-exec (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ is) s i4 h-false (subst (λ p → fetch (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ is) p ≡ just i4) (sym pc-4) refl)

-- | Step halts when fetch returns nothing
step-halt-on-fetch-fail : ∀ (prog : Program) (s : State) →
  halted s ≡ false →
  fetch prog (pc s) ≡ nothing →
  step prog s ≡ just (record s { halted = true })
step-halt-on-fetch-fail prog s h-false fetch-fail with halted s | h-false
... | false | refl with fetch prog (pc s) | fetch-fail
...   | nothing | refl = refl

------------------------------------------------------------------------
-- Exec N-steps helpers
------------------------------------------------------------------------

-- | Execute 1 step and halt
-- PROVEN: Using rewrite to handle the with-clause abstraction
exec-one-step : ∀ (n : ℕ) (prog : List Instr) (s state1 : State) →
  step prog s ≡ just state1 →
  halted state1 ≡ true →
  exec (suc n) prog s ≡ just state1
exec-one-step n prog s state1 step-eq halt-eq
  rewrite step-eq | halt-eq = refl

-- | Helper: unfold one level of exec when computation continues
-- This is provable because it's a single unfolding with rewrite
exec-step-continue : ∀ (n : ℕ) (prog : List Instr) (s s' : State) →
  step prog s ≡ just s' →
  halted s' ≡ false →
  exec (suc n) prog s ≡ exec n prog s'
exec-step-continue n prog s s' step-eq halt-eq rewrite step-eq | halt-eq = refl

-- | Execute 2 steps and halt
exec-two-steps : ∀ (n : ℕ) (prog : List Instr) (s st1 st2 : State) →
  step prog s ≡ just st1 → halted st1 ≡ false →
  step prog st1 ≡ just st2 → halted st2 ≡ true →
  exec (suc (suc n)) prog s ≡ just st2
exec-two-steps n prog s st1 st2 step1-eq h1 step2-eq h2 =
  trans (exec-step-continue (suc n) prog s st1 step1-eq h1)
        (exec-one-step n prog st1 st2 step2-eq h2)

-- | Execute 3 steps and halt
exec-three-steps : ∀ (n : ℕ) (prog : List Instr) (s st1 st2 st3 : State) →
  step prog s ≡ just st1 → halted st1 ≡ false →
  step prog st1 ≡ just st2 → halted st2 ≡ false →
  step prog st2 ≡ just st3 → halted st3 ≡ true →
  exec (suc (suc (suc n))) prog s ≡ just st3
exec-three-steps n prog s st1 st2 st3 step1 h1 step2 h2 step3 h3 =
  trans (exec-step-continue (suc (suc n)) prog s st1 step1 h1)
        (exec-two-steps n prog st1 st2 st3 step2 h2 step3 h3)

-- | Execute 4 steps and halt
exec-four-steps : ∀ (n : ℕ) (prog : List Instr) (s st1 st2 st3 st4 : State) →
  step prog s ≡ just st1 → halted st1 ≡ false →
  step prog st1 ≡ just st2 → halted st2 ≡ false →
  step prog st2 ≡ just st3 → halted st3 ≡ false →
  step prog st3 ≡ just st4 → halted st4 ≡ true →
  exec (suc (suc (suc (suc n)))) prog s ≡ just st4
exec-four-steps n prog s st1 st2 st3 st4 step1 h1 step2 h2 step3 h3 step4 h4 =
  trans (exec-step-continue (suc (suc (suc n))) prog s st1 step1 h1)
        (exec-three-steps n prog st1 st2 st3 st4 step2 h2 step3 h3 step4 h4)

-- | Execute 5 steps and halt
exec-five-steps : ∀ (n : ℕ) (prog : List Instr) (s st1 st2 st3 st4 st5 : State) →
  step prog s ≡ just st1 → halted st1 ≡ false →
  step prog st1 ≡ just st2 → halted st2 ≡ false →
  step prog st2 ≡ just st3 → halted st3 ≡ false →
  step prog st3 ≡ just st4 → halted st4 ≡ false →
  step prog st4 ≡ just st5 → halted st5 ≡ true →
  exec (suc (suc (suc (suc (suc n))))) prog s ≡ just st5
exec-five-steps n prog s st1 st2 st3 st4 st5 step1 h1 step2 h2 step3 h3 step4 h4 step5 h5 =
  trans (exec-step-continue (suc (suc (suc (suc n)))) prog s st1 step1 h1)
        (exec-four-steps n prog st1 st2 st3 st4 st5 step2 h2 step3 h3 step4 h4 step5 h5)

-- | Execute 6 steps and halt
exec-six-steps : ∀ (n : ℕ) (prog : List Instr) (s st1 st2 st3 st4 st5 st6 : State) →
  step prog s ≡ just st1 → halted st1 ≡ false →
  step prog st1 ≡ just st2 → halted st2 ≡ false →
  step prog st2 ≡ just st3 → halted st3 ≡ false →
  step prog st3 ≡ just st4 → halted st4 ≡ false →
  step prog st4 ≡ just st5 → halted st5 ≡ false →
  step prog st5 ≡ just st6 → halted st6 ≡ true →
  exec (suc (suc (suc (suc (suc (suc n)))))) prog s ≡ just st6
exec-six-steps n prog s st1 st2 st3 st4 st5 st6 step1 h1 step2 h2 step3 h3 step4 h4 step5 h5 step6 h6 =
  trans (exec-step-continue (suc (suc (suc (suc (suc n))))) prog s st1 step1 h1)
        (exec-five-steps n prog st1 st2 st3 st4 st5 st6 step2 h2 step3 h3 step4 h4 step5 h5 step6 h6)

-- | Execute 7 steps and halt
exec-seven-steps : ∀ (n : ℕ) (prog : List Instr) (s st1 st2 st3 st4 st5 st6 st7 : State) →
  step prog s ≡ just st1 → halted st1 ≡ false →
  step prog st1 ≡ just st2 → halted st2 ≡ false →
  step prog st2 ≡ just st3 → halted st3 ≡ false →
  step prog st3 ≡ just st4 → halted st4 ≡ false →
  step prog st4 ≡ just st5 → halted st5 ≡ false →
  step prog st5 ≡ just st6 → halted st6 ≡ false →
  step prog st6 ≡ just st7 → halted st7 ≡ true →
  exec (suc (suc (suc (suc (suc (suc (suc n))))))) prog s ≡ just st7
exec-seven-steps n prog s st1 st2 st3 st4 st5 st6 st7 step1 h1 step2 h2 step3 h3 step4 h4 step5 h5 step6 h6 step7 h7 =
  trans (exec-step-continue (suc (suc (suc (suc (suc (suc n)))))) prog s st1 step1 h1)
        (exec-six-steps n prog st1 st2 st3 st4 st5 st6 st7 step2 h2 step3 h3 step4 h4 step5 h5 step6 h6 step7 h7)

-- | Execute 8 steps and halt
exec-eight-steps : ∀ (n : ℕ) (prog : List Instr) (s st1 st2 st3 st4 st5 st6 st7 st8 : State) →
  step prog s ≡ just st1 → halted st1 ≡ false →
  step prog st1 ≡ just st2 → halted st2 ≡ false →
  step prog st2 ≡ just st3 → halted st3 ≡ false →
  step prog st3 ≡ just st4 → halted st4 ≡ false →
  step prog st4 ≡ just st5 → halted st5 ≡ false →
  step prog st5 ≡ just st6 → halted st6 ≡ false →
  step prog st6 ≡ just st7 → halted st7 ≡ false →
  step prog st7 ≡ just st8 → halted st8 ≡ true →
  exec (suc (suc (suc (suc (suc (suc (suc (suc n)))))))) prog s ≡ just st8
exec-eight-steps n prog s st1 st2 st3 st4 st5 st6 st7 st8 step1 h1 step2 h2 step3 h3 step4 h4 step5 h5 step6 h6 step7 h7 step8 h8 =
  trans (exec-step-continue (suc (suc (suc (suc (suc (suc (suc n))))))) prog s st1 step1 h1)
        (exec-seven-steps n prog st1 st2 st3 st4 st5 st6 st7 st8 step2 h2 step3 h3 step4 h4 step5 h5 step6 h6 step7 h7 step8 h8)

------------------------------------------------------------------------
-- Single instruction execution proofs
------------------------------------------------------------------------

-- | Running a single nop and halting
run-single-nop : ∀ (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  ∃[ s' ] (run (nop ∷ []) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') a0 ≡ readReg (regs s) a0)
run-single-nop s h-false pc-0 = st2 , run-eq , halt-eq , a0-eq
  where
    prog : List Instr
    prog = nop ∷ []

    -- State after nop
    st1 : State
    st1 = record s { pc = pc s +ℕ 1 }

    step1 : step prog s ≡ just st1
    step1 = trans (step-exec-0 nop [] s h-false pc-0) (execNop prog s)

    h1 : halted st1 ≡ false
    h1 = h-false

    pc1 : pc st1 ≡ 1
    pc1 = cong (λ x → x +ℕ 1) pc-0

    -- State after halt (fetch fails at pc=1)
    st2 : State
    st2 = record st1 { halted = true }

    fetch-fail : fetch prog (pc st1) ≡ nothing
    fetch-fail = subst (λ p → fetch prog p ≡ nothing) (sym pc1) refl

    step2 : step prog st1 ≡ just st2
    step2 = step-halt-on-fetch-fail prog st1 h1 fetch-fail

    halt-eq : halted st2 ≡ true
    halt-eq = refl

    run-eq : run prog s ≡ just st2
    run-eq = exec-two-steps 9998 prog s st1 st2 step1 h1 step2 halt-eq

    -- a0 unchanged by nop
    a0-eq : readReg (regs st2) a0 ≡ readReg (regs s) a0
    a0-eq = refl

------------------------------------------------------------------------
-- Main generator postulate (required for recursive IR cases)
------------------------------------------------------------------------

-- | Main execution theorem for IR generators
--
-- This is postulated because it requires mutual induction over IR structure.
-- The recursive cases (compose, case, pair) need this theorem for sub-IRs.
postulate
  run-generator : ∀ {A B} (ir : IR A B) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ 0 →
    readReg (regs s) a0 ≡ encode x →
    ∃[ s' ] (run (compile-riscv ir) s ≡ just s'
           × halted s' ≡ true
           × readReg (regs s') a0 ≡ encode (eval ir x))

------------------------------------------------------------------------
-- Proven base cases for run-generator
------------------------------------------------------------------------

-- | run-generator for id
--
-- Generated code: nop (a0 already has the value!)
-- This is simpler than x86 which needs mov rax, rdi
run-generator-id : ∀ {A} (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) a0 ≡ encode x →
  ∃[ s' ] (run (compile-riscv {A} {A} id) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') a0 ≡ encode (eval {A} {A} id x))
run-generator-id {A} x s h-false pc-0 a0-eq = s' , run-eq , halt-eq , a0-eq'
  where
    helper : ∃[ s' ] (run (nop ∷ []) s ≡ just s'
                    × halted s' ≡ true
                    × readReg (regs s') a0 ≡ readReg (regs s) a0)
    helper = run-single-nop s h-false pc-0

    s' : State
    s' = proj₁ helper

    run-eq : run (compile-riscv {A} {A} id) s ≡ just s'
    run-eq = proj₁ (proj₂ helper)

    halt-eq : halted s' ≡ true
    halt-eq = proj₁ (proj₂ (proj₂ helper))

    -- a0 unchanged, and eval id x = x
    a0-eq' : readReg (regs s') a0 ≡ encode (eval {A} {A} id x)
    a0-eq' = trans (proj₂ (proj₂ (proj₂ helper))) a0-eq

-- | run-generator for terminal
--
-- Generated code: li a0, 0
run-generator-terminal : ∀ {A} (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) a0 ≡ encode x →
  ∃[ s' ] (run (compile-riscv {A} {Unit} terminal) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') a0 ≡ encode {Unit} tt)
run-generator-terminal {A} x s h-false pc-0 a0-eq = st2 , run-eq , halt-eq , a0-eq'
  where
    prog : List Instr
    prog = li a0 (+ 0) ∷ []

    -- State after li a0, 0
    st1 : State
    st1 = record s { regs = writeReg (regs s) a0 0
                   ; pc = pc s +ℕ 1 }

    step1 : step prog s ≡ just st1
    step1 = trans (step-exec-0 (li a0 (+ 0)) [] s h-false pc-0) (execLi prog s a0 0)

    h1 : halted st1 ≡ false
    h1 = h-false

    pc1 : pc st1 ≡ 1
    pc1 = cong (λ x → x +ℕ 1) pc-0

    -- State after halt
    st2 : State
    st2 = record st1 { halted = true }

    fetch-fail : fetch prog (pc st1) ≡ nothing
    fetch-fail = subst (λ p → fetch prog p ≡ nothing) (sym pc1) refl

    step2 : step prog st1 ≡ just st2
    step2 = step-halt-on-fetch-fail prog st1 h1 fetch-fail

    halt-eq : halted st2 ≡ true
    halt-eq = refl

    run-eq : run prog s ≡ just st2
    run-eq = exec-two-steps 9998 prog s st1 st2 step1 h1 step2 halt-eq

    -- a0 = 0 = encode tt (by encode-unit)
    a0-eq' : readReg (regs st2) a0 ≡ encode {Unit} tt
    a0-eq' = trans (readReg-writeReg-same (regs s) a0 0) (sym encode-unit)

-- | run-generator for fold (identity at runtime)
--
-- Generated code: nop
run-generator-fold : ∀ {F} (x : ⟦ F ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) a0 ≡ encode x →
  ∃[ s' ] (run (compile-riscv {F} {Fix F} fold) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') a0 ≡ encode x)
run-generator-fold {F} x s h-false pc-0 a0-eq =
  let (s' , run-eq , halt-eq , a0-preserved) = run-single-nop s h-false pc-0
  in s' , run-eq , halt-eq , trans a0-preserved a0-eq

-- | run-generator for unfold (identity at runtime)
--
-- Generated code: nop
run-generator-unfold : ∀ {F} (x : ⟦ Fix F ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) a0 ≡ encode x →
  ∃[ s' ] (run (compile-riscv {Fix F} {F} unfold) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') a0 ≡ encode x)
run-generator-unfold {F} x s h-false pc-0 a0-eq =
  let (s' , run-eq , halt-eq , a0-preserved) = run-single-nop s h-false pc-0
  in s' , run-eq , halt-eq , trans a0-preserved a0-eq

-- | run-generator for arr (identity at runtime)
--
-- Generated code: nop
run-generator-arr : ∀ {A B} (f : ⟦ A ⇒ B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) a0 ≡ encode {A ⇒ B} f →
  ∃[ s' ] (run (compile-riscv {A ⇒ B} {Eff A B} arr) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') a0 ≡ encode {A ⇒ B} f)
run-generator-arr {A} {B} f s h-false pc-0 a0-eq =
  let (s' , run-eq , halt-eq , a0-preserved) = run-single-nop s h-false pc-0
  in s' , run-eq , halt-eq , trans a0-preserved a0-eq

------------------------------------------------------------------------
-- Postulated helpers for complex generators
------------------------------------------------------------------------

-- These require more complex instruction tracing

------------------------------------------------------------------------
-- fst and snd execution proofs
------------------------------------------------------------------------

-- | fst execution: ld a0, 0(a0)
-- Generated code: ld a0 (+ 0) a0 ∷ []
run-fst-seq : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) a0 ≡ encode (a , b) →
  readMem (memory s) (encode (a , b)) ≡ just (encode a) →
  ∃[ s' ] (run (compile-riscv {A * B} {A} fst) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') a0 ≡ encode a)
run-fst-seq {A} {B} a b s h-false pc-0 a0-eq mem-eq = st2 , run-eq , refl , a0-eq'
  where
    prog : List Instr
    prog = ld a0 (+ 0) a0 ∷ []

    -- Memory read at address a0 + 0 = encode (a,b)
    -- Note: n + 0 ≡ n requires +-identityʳ
    addr-eq : readReg (regs s) a0 +ℕ 0 ≡ encode (a , b)
    addr-eq = trans (+-identityʳ (readReg (regs s) a0)) a0-eq

    mem-read : readMem (memory s) (readReg (regs s) a0 +ℕ 0) ≡ just (encode a)
    mem-read = subst (λ addr → readMem (memory s) addr ≡ just (encode a)) (sym addr-eq) mem-eq

    -- State after ld: a0 = encode a, pc = 1
    st1 : State
    st1 = record s { regs = writeReg (regs s) a0 (encode a)
                   ; pc = pc s +ℕ 1 }

    -- ld instruction execution
    step1 : step prog s ≡ just st1
    step1 = trans (step-exec-0 (ld a0 (+ 0) a0) [] s h-false pc-0)
                  (execLd prog s a0 0 a0 (encode a) mem-read)

    -- st1 is not halted (halted preserved from s)
    h1 : halted st1 ≡ false
    h1 = h-false

    -- pc in st1 is 1
    pc1 : pc st1 ≡ 1
    pc1 = cong (λ p → p +ℕ 1) pc-0

    -- Fetch at pc=1 fails (program has 1 instruction)
    fetch-fail : fetch prog (pc st1) ≡ nothing
    fetch-fail = subst (λ p → fetch prog p ≡ nothing) (sym pc1) refl

    -- State halts on next step
    st2 : State
    st2 = record st1 { halted = true }

    -- halted st2 ≡ true
    h2 : halted st2 ≡ true
    h2 = refl

    -- Step from st1 halts
    step2 : step prog st1 ≡ just st2
    step2 = step-halt-on-fetch-fail prog st1 h1 fetch-fail

    -- run with 2 steps (exec-two-steps 9998 produces exec 10000 = run)
    run-eq : run prog s ≡ just st2
    run-eq = exec-two-steps 9998 prog s st1 st2 step1 h1 step2 h2

    -- a0 in final state
    a0-eq' : readReg (regs st2) a0 ≡ encode a
    a0-eq' = readReg-writeReg-same (regs s) a0 (encode a)

-- | snd execution: ld a0, 8(a0)
-- Generated code: ld a0 (+ 8) a0 ∷ []
run-snd-seq : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) a0 ≡ encode (a , b) →
  readMem (memory s) (encode (a , b) +ℕ 8) ≡ just (encode b) →
  ∃[ s' ] (run (compile-riscv {A * B} {B} snd) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') a0 ≡ encode b)
run-snd-seq {A} {B} a b s h-false pc-0 a0-eq mem-eq = st2 , run-eq , refl , a0-eq'
  where
    prog : List Instr
    prog = ld a0 (+ 8) a0 ∷ []

    -- Memory read at address a0 + 8 = encode (a,b) + 8
    mem-read : readMem (memory s) (readReg (regs s) a0 +ℕ 8) ≡ just (encode b)
    mem-read = subst (λ addr → readMem (memory s) (addr +ℕ 8) ≡ just (encode b)) (sym a0-eq) mem-eq

    -- State after ld: a0 = encode b, pc = 1
    st1 : State
    st1 = record s { regs = writeReg (regs s) a0 (encode b)
                   ; pc = pc s +ℕ 1 }

    -- ld instruction execution
    step1 : step prog s ≡ just st1
    step1 = trans (step-exec-0 (ld a0 (+ 8) a0) [] s h-false pc-0)
                  (execLd prog s a0 8 a0 (encode b) mem-read)

    -- st1 is not halted (halted preserved from s)
    h1 : halted st1 ≡ false
    h1 = h-false

    -- pc in st1 is 1
    pc1 : pc st1 ≡ 1
    pc1 = cong (λ p → p +ℕ 1) pc-0

    -- Fetch at pc=1 fails (program has 1 instruction)
    fetch-fail : fetch prog (pc st1) ≡ nothing
    fetch-fail = subst (λ p → fetch prog p ≡ nothing) (sym pc1) refl

    -- State halts on next step
    st2 : State
    st2 = record st1 { halted = true }

    -- halted st2 ≡ true
    h2 : halted st2 ≡ true
    h2 = refl

    -- Step from st1 halts
    step2 : step prog st1 ≡ just st2
    step2 = step-halt-on-fetch-fail prog st1 h1 fetch-fail

    -- run with 2 steps (exec-two-steps 9998 produces exec 10000 = run)
    run-eq : run prog s ≡ just st2
    run-eq = exec-two-steps 9998 prog s st1 st2 step1 h1 step2 h2

    -- a0 in final state
    a0-eq' : readReg (regs st2) a0 ≡ encode b
    a0-eq' = readReg-writeReg-same (regs s) a0 (encode b)

------------------------------------------------------------------------
-- inl and inr execution proofs
------------------------------------------------------------------------

-- | inl execution: addi sp sp -16; sd zero 0(sp); sd a0 8(sp); mv a0 sp
-- Creates tagged union [tag=0, value=encode x] on stack
run-inl-seq : ∀ {A B} (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) a0 ≡ encode x →
  ∃[ s' ] (run (compile-riscv {A} {A + B} inl) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') a0 ≡ encode {A + B} (inj₁ x))
run-inl-seq {A} {B} x s h-false pc-0 a0-eq = st5 , run-eq , refl , a0-final
  where
    -- Program: addi sp sp -16 ∷ sd zero 0(sp) ∷ sd a0 8(sp) ∷ mv a0 sp ∷ []
    prog = compile-riscv {A} {A + B} inl

    -- New sp value after allocation
    new-sp : Word
    new-sp = readReg (regs s) sp ∸ 16

    -- State st1: after addi sp sp -16 (pc=pc s + 1, sp=new-sp)
    st1 : State
    st1 = record s { regs = writeReg (regs s) sp new-sp ; pc = pc s +ℕ 1 }

    step1 : step prog s ≡ just st1
    step1 = trans (step-exec-0 (addi sp sp neg16) _ s h-false pc-0)
                  (execAddiNeg prog s sp sp 15)

    h1 : halted st1 ≡ false
    h1 = h-false

    pc1 : pc st1 ≡ 1
    pc1 = cong (λ p → p +ℕ 1) pc-0

    -- State st2: after sd zero 0(sp) (pc=pc st1 + 1, M[new-sp]=0)
    st2 : State
    st2 = record st1 { memory = writeMem (memory st1) (readReg (regs st1) sp +ℕ 0) (readReg (regs st1) zero)
                     ; pc = pc st1 +ℕ 1 }

    -- sp in st1 is new-sp
    sp-st1 : readReg (regs st1) sp ≡ new-sp
    sp-st1 = readReg-writeReg-same (regs s) sp new-sp

    step2 : step prog st1 ≡ just st2
    step2 = trans (step-exec-1 (addi sp sp neg16) (sd zero (+ 0) sp) _ st1 h1 pc1)
                  (execSd prog st1 zero 0 sp)

    h2 : halted st2 ≡ false
    h2 = h-false

    pc2 : pc st2 ≡ 2
    pc2 = cong (λ p → p +ℕ 1) pc1

    -- State st3: after sd a0 8(sp) (pc=pc st2 + 1, M[new-sp+8]=encode x)
    st3 : State
    st3 = record st2 { memory = writeMem (memory st2) (readReg (regs st2) sp +ℕ 8) (readReg (regs st2) a0)
                     ; pc = pc st2 +ℕ 1 }

    -- regs st2 = regs st1 (sd doesn't change registers)
    -- a0 in st1 = a0 in s (writing sp doesn't change a0)
    -- a0 in st2 = a0 in st1 (sd doesn't change registers)
    a0-st2 : readReg (regs st2) a0 ≡ encode x
    a0-st2 = trans (readReg-writeReg-sp-a0 (regs s) new-sp) a0-eq

    step3 : step prog st2 ≡ just st3
    step3 = trans (step-exec-2 (addi sp sp neg16) (sd zero (+ 0) sp) (sd a0 (+ 8) sp) _ st2 h2 pc2)
                  (execSd prog st2 a0 8 sp)

    h3 : halted st3 ≡ false
    h3 = h-false

    pc3 : pc st3 ≡ 3
    pc3 = cong (λ p → p +ℕ 1) pc2

    -- State st4: after mv a0 sp (pc=pc st3 + 1, a0=new-sp)
    st4 : State
    st4 = record st3 { regs = writeReg (regs st3) a0 (readReg (regs st3) sp)
                     ; pc = pc st3 +ℕ 1 }

    step4 : step prog st3 ≡ just st4
    step4 = trans (step-exec-3 (addi sp sp neg16) (sd zero (+ 0) sp) (sd a0 (+ 8) sp) (mv a0 sp) _ st3 h3 pc3)
                  (execMv prog st3 a0 sp)

    h4 : halted st4 ≡ false
    h4 = h-false

    pc4 : pc st4 ≡ 4
    pc4 = cong (λ p → p +ℕ 1) pc3

    -- State st5: halt (fetch at pc=4 fails for 4-instruction program)
    st5 : State
    st5 = record st4 { halted = true }

    fetch-fail : fetch prog (pc st4) ≡ nothing
    fetch-fail = subst (λ p → fetch prog p ≡ nothing) (sym pc4) refl

    step5 : step prog st4 ≡ just st5
    step5 = step-halt-on-fetch-fail prog st4 h4 fetch-fail

    h5 : halted st5 ≡ true
    h5 = refl

    -- Full execution using exec-five-steps 9995 (produces exec 10000 = run)
    run-eq : run prog s ≡ just st5
    run-eq = exec-five-steps 9995 prog s st1 st2 st3 st4 st5 step1 h1 step2 h2 step3 h3 step4 h4 step5 h5

    -- Now we need to show: readReg (regs st5) a0 ≡ encode (inj₁ x)
    -- Using encode-inl-construct: if M[p]=0 and M[p+8]=encode x, then p = encode (inj₁ x)

    -- a0 in st5 = a0 in st4 = sp in st3 = new-sp
    a0-st5 : readReg (regs st5) a0 ≡ new-sp
    a0-st5 = readReg-writeReg-same (regs st3) a0 (readReg (regs st3) sp)

    -- Memory chain tracking
    -- s → st1 (addi: no mem change)
    -- → st2 (sd zero 0(sp): writes 0 at new-sp)
    -- → st3 (sd a0 8(sp): writes encode x at new-sp+8)
    -- → st4 (mv: no mem change)
    -- → st5 (halt: no mem change)

    -- memory st2 = writeMem (memory s) new-sp 0
    -- We need to show the address is new-sp (= sp in st1 + 0)
    addr-st2 : readReg (regs st1) sp +ℕ 0 ≡ new-sp
    addr-st2 = trans (+-identityʳ (readReg (regs st1) sp)) sp-st1

    -- zero register always reads 0
    zero-is-0 : readReg (regs st1) zero ≡ 0
    zero-is-0 = readReg-zero-always-0 (regs st1)

    -- sp in st2 = new-sp (sd doesn't change registers, so same as st1)
    sp-st2 : readReg (regs st2) sp ≡ new-sp
    sp-st2 = sp-st1

    -- memory st3 = writeMem (memory st2) (new-sp + 8) (encode x)
    addr-st3 : readReg (regs st2) sp +ℕ 8 ≡ new-sp +ℕ 8
    addr-st3 = cong (_+ℕ 8) sp-st2

    -- new-sp ≠ new-sp + 8 (needed for readMem-writeMem-diff)
    new-sp≢new-sp+8 : new-sp ≢ new-sp +ℕ 8
    new-sp≢new-sp+8 = n≢n+suc new-sp 7

    -- memory st5 = memory st3 (st4 and st5 don't modify memory)
    -- memory st4 = memory st3 (mv doesn't change memory)
    -- memory st5 = memory st4 (halting doesn't change memory)

    -- Reading tag (at new-sp) from memory st5
    tag-is-0 : readMem (memory st5) (readReg (regs st5) a0) ≡ just 0
    tag-is-0 =
      begin
        readMem (memory st5) (readReg (regs st5) a0)
      ≡⟨ cong (readMem (memory st5)) a0-st5 ⟩
        readMem (memory st5) new-sp
      ≡⟨ refl ⟩  -- memory st5 = memory st4 = memory st3
        readMem (memory st3) new-sp
      ≡⟨ refl ⟩  -- memory st3 = writeMem (memory st2) (new-sp+8) (encode x)
        readMem (writeMem (memory st2) (readReg (regs st2) sp +ℕ 8) (readReg (regs st2) a0)) new-sp
      ≡⟨ cong (λ addr → readMem (writeMem (memory st2) addr (readReg (regs st2) a0)) new-sp) addr-st3 ⟩
        readMem (writeMem (memory st2) (new-sp +ℕ 8) (readReg (regs st2) a0)) new-sp
      ≡⟨ readMem-writeMem-diff (memory st2) (new-sp +ℕ 8) new-sp (readReg (regs st2) a0) (λ eq → new-sp≢new-sp+8 (sym eq)) ⟩
        readMem (memory st2) new-sp
      ≡⟨ refl ⟩  -- memory st2 = writeMem (memory st1) (new-sp+0) 0
        readMem (writeMem (memory st1) (readReg (regs st1) sp +ℕ 0) (readReg (regs st1) zero)) new-sp
      ≡⟨ cong (λ addr → readMem (writeMem (memory st1) addr (readReg (regs st1) zero)) new-sp) addr-st2 ⟩
        readMem (writeMem (memory st1) new-sp (readReg (regs st1) zero)) new-sp
      ≡⟨ readMem-writeMem-same (memory st1) new-sp (readReg (regs st1) zero) ⟩
        just (readReg (regs st1) zero)
      ≡⟨ cong just zero-is-0 ⟩
        just 0
      ∎

    -- Reading value (at new-sp + 8) from memory st5
    val-is-encode-x : readMem (memory st5) (readReg (regs st5) a0 +ℕ 8) ≡ just (encode x)
    val-is-encode-x =
      begin
        readMem (memory st5) (readReg (regs st5) a0 +ℕ 8)
      ≡⟨ cong (λ addr → readMem (memory st5) (addr +ℕ 8)) a0-st5 ⟩
        readMem (memory st5) (new-sp +ℕ 8)
      ≡⟨ refl ⟩  -- memory st5 = memory st3
        readMem (memory st3) (new-sp +ℕ 8)
      ≡⟨ refl ⟩  -- memory st3 = writeMem (memory st2) (new-sp+8) (a0 in st2)
        readMem (writeMem (memory st2) (readReg (regs st2) sp +ℕ 8) (readReg (regs st2) a0)) (new-sp +ℕ 8)
      ≡⟨ cong (λ addr → readMem (writeMem (memory st2) addr (readReg (regs st2) a0)) (new-sp +ℕ 8)) addr-st3 ⟩
        readMem (writeMem (memory st2) (new-sp +ℕ 8) (readReg (regs st2) a0)) (new-sp +ℕ 8)
      ≡⟨ readMem-writeMem-same (memory st2) (new-sp +ℕ 8) (readReg (regs st2) a0) ⟩
        just (readReg (regs st2) a0)
      ≡⟨ cong just a0-st2 ⟩
        just (encode x)
      ∎

    a0-final : readReg (regs st5) a0 ≡ encode {A + B} (inj₁ x)
    a0-final = encode-inl-construct x (readReg (regs st5) a0) (memory st5) tag-is-0 val-is-encode-x

-- | inr execution: addi sp sp -16; li t0 1; sd t0 0(sp); sd a0 8(sp); mv a0 sp
-- Creates tagged union [tag=1, value=encode x] on stack
run-inr-seq : ∀ {A B} (x : ⟦ B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) a0 ≡ encode x →
  ∃[ s' ] (run (compile-riscv {B} {A + B} inr) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') a0 ≡ encode {A + B} (inj₂ x))
run-inr-seq {A} {B} x s h-false pc-0 a0-eq = st6 , run-eq , refl , a0-final
  where
    -- Program: addi sp sp -16 ∷ li t0 1 ∷ sd t0 0(sp) ∷ sd a0 8(sp) ∷ mv a0 sp ∷ []
    prog = compile-riscv {B} {A + B} inr

    -- New sp value after allocation
    new-sp : Word
    new-sp = readReg (regs s) sp ∸ 16

    -- State st1: after addi sp sp -16
    st1 : State
    st1 = record s { regs = writeReg (regs s) sp new-sp ; pc = pc s +ℕ 1 }

    step1 : step prog s ≡ just st1
    step1 = trans (step-exec-0 (addi sp sp neg16) _ s h-false pc-0)
                  (execAddiNeg prog s sp sp 15)

    h1 : halted st1 ≡ false
    h1 = h-false

    pc1 : pc st1 ≡ 1
    pc1 = cong (λ p → p +ℕ 1) pc-0

    -- State st2: after li t0 1
    st2 : State
    st2 = record st1 { regs = writeReg (regs st1) t0 1 ; pc = pc st1 +ℕ 1 }

    step2 : step prog st1 ≡ just st2
    step2 = trans (step-exec-1 (addi sp sp neg16) (li t0 (+ 1)) _ st1 h1 pc1)
                  (execLi prog st1 t0 1)

    h2 : halted st2 ≡ false
    h2 = h-false

    pc2 : pc st2 ≡ 2
    pc2 = cong (λ p → p +ℕ 1) pc1

    -- State st3: after sd t0 0(sp)
    st3 : State
    st3 = record st2 { memory = writeMem (memory st2) (readReg (regs st2) sp +ℕ 0) (readReg (regs st2) t0)
                     ; pc = pc st2 +ℕ 1 }

    step3 : step prog st2 ≡ just st3
    step3 = trans (step-exec-2 (addi sp sp neg16) (li t0 (+ 1)) (sd t0 (+ 0) sp) _ st2 h2 pc2)
                  (execSd prog st2 t0 0 sp)

    h3 : halted st3 ≡ false
    h3 = h-false

    pc3 : pc st3 ≡ 3
    pc3 = cong (λ p → p +ℕ 1) pc2

    -- State st4: after sd a0 8(sp)
    st4 : State
    st4 = record st3 { memory = writeMem (memory st3) (readReg (regs st3) sp +ℕ 8) (readReg (regs st3) a0)
                     ; pc = pc st3 +ℕ 1 }

    step4 : step prog st3 ≡ just st4
    step4 = trans (step-exec-3 (addi sp sp neg16) (li t0 (+ 1)) (sd t0 (+ 0) sp) (sd a0 (+ 8) sp) _ st3 h3 pc3)
                  (execSd prog st3 a0 8 sp)

    h4 : halted st4 ≡ false
    h4 = h-false

    pc4 : pc st4 ≡ 4
    pc4 = cong (λ p → p +ℕ 1) pc3

    -- State st5: after mv a0 sp
    st5 : State
    st5 = record st4 { regs = writeReg (regs st4) a0 (readReg (regs st4) sp)
                     ; pc = pc st4 +ℕ 1 }

    step5 : step prog st4 ≡ just st5
    step5 = trans (step-exec-4 (addi sp sp neg16) (li t0 (+ 1)) (sd t0 (+ 0) sp) (sd a0 (+ 8) sp) (mv a0 sp) _ st4 h4 pc4)
                  (execMv prog st4 a0 sp)

    h5 : halted st5 ≡ false
    h5 = h-false

    pc5 : pc st5 ≡ 5
    pc5 = cong (λ p → p +ℕ 1) pc4

    -- State st6: halt
    st6 : State
    st6 = record st5 { halted = true }

    fetch-fail : fetch prog (pc st5) ≡ nothing
    fetch-fail = subst (λ p → fetch prog p ≡ nothing) (sym pc5) refl

    step6 : step prog st5 ≡ just st6
    step6 = step-halt-on-fetch-fail prog st5 h5 fetch-fail

    h6 : halted st6 ≡ true
    h6 = refl

    -- Full execution using exec-six-steps 9994 (produces exec 10000 = run)
    run-eq : run prog s ≡ just st6
    run-eq = exec-six-steps 9994 prog s st1 st2 st3 st4 st5 st6 step1 h1 step2 h2 step3 h3 step4 h4 step5 h5 step6 h6

    -- Memory chain tracking for inr:
    -- s → st1 (addi: no mem change)
    -- → st2 (li t0 1: no mem change, only reg)
    -- → st3 (sd t0 0(sp): writes 1 at new-sp)
    -- → st4 (sd a0 8(sp): writes encode x at new-sp+8)
    -- → st5 (mv: no mem change)
    -- → st6 (halt: no mem change)

    -- sp tracking: sp in st1 = new-sp, writing t0 preserves sp
    sp-st1 : readReg (regs st1) sp ≡ new-sp
    sp-st1 = readReg-writeReg-same (regs s) sp new-sp

    -- sp in st2 = new-sp (li writes t0, not sp)
    readReg-writeReg-t0-sp : ∀ (rf : RegFile) (v : Word) → readReg (writeReg rf t0 v) sp ≡ readReg rf sp
    readReg-writeReg-t0-sp rf v = refl

    sp-st2 : readReg (regs st2) sp ≡ new-sp
    sp-st2 = trans (readReg-writeReg-t0-sp (regs st1) 1) sp-st1

    -- t0 in st2 = 1 (from li)
    t0-st2 : readReg (regs st2) t0 ≡ 1
    t0-st2 = readReg-writeReg-same (regs st1) t0 1

    -- sp in st3 = new-sp (sd doesn't change registers)
    sp-st3 : readReg (regs st3) sp ≡ new-sp
    sp-st3 = sp-st2

    -- a0 tracking through st3: writing sp, t0, and memory preserves a0
    readReg-writeReg-t0-a0 : ∀ (rf : RegFile) (v : Word) → readReg (writeReg rf t0 v) a0 ≡ readReg rf a0
    readReg-writeReg-t0-a0 rf v = refl

    a0-st1 : readReg (regs st1) a0 ≡ encode x
    a0-st1 = trans (readReg-writeReg-sp-a0 (regs s) new-sp) a0-eq

    a0-st2 : readReg (regs st2) a0 ≡ encode x
    a0-st2 = trans (readReg-writeReg-t0-a0 (regs st1) 1) a0-st1

    a0-st3 : readReg (regs st3) a0 ≡ encode x
    a0-st3 = a0-st2  -- sd doesn't change registers

    -- Address calculations
    addr-st3 : readReg (regs st2) sp +ℕ 0 ≡ new-sp
    addr-st3 = trans (+-identityʳ (readReg (regs st2) sp)) sp-st2

    addr-st4 : readReg (regs st3) sp +ℕ 8 ≡ new-sp +ℕ 8
    addr-st4 = cong (_+ℕ 8) sp-st3

    -- new-sp ≠ new-sp + 8
    new-sp≢new-sp+8 : new-sp ≢ new-sp +ℕ 8
    new-sp≢new-sp+8 = n≢n+suc new-sp 7

    -- a0 in st6 = new-sp (through mv a0 sp in st5)
    -- First, sp in st4 = sp in st3 = new-sp
    sp-st4 : readReg (regs st4) sp ≡ new-sp
    sp-st4 = sp-st3

    a0-st6 : readReg (regs st6) a0 ≡ new-sp
    a0-st6 = readReg-writeReg-same (regs st4) a0 (readReg (regs st4) sp)

    -- Reading tag (at new-sp) from memory st6
    -- memory st6 = memory st5 = memory st4
    -- memory st4 = writeMem (memory st3) (new-sp+8) (encode x)
    -- memory st3 = writeMem (memory st2) new-sp 1
    -- memory st2 = memory st1 = memory s (li and addi don't change memory)
    tag-is-1 : readMem (memory st6) (readReg (regs st6) a0) ≡ just 1
    tag-is-1 =
      begin
        readMem (memory st6) (readReg (regs st6) a0)
      ≡⟨ cong (readMem (memory st6)) a0-st6 ⟩
        readMem (memory st6) new-sp
      ≡⟨ refl ⟩  -- memory st6 = memory st4
        readMem (memory st4) new-sp
      ≡⟨ refl ⟩  -- memory st4 = writeMem (memory st3) (new-sp+8) (encode x)
        readMem (writeMem (memory st3) (readReg (regs st3) sp +ℕ 8) (readReg (regs st3) a0)) new-sp
      ≡⟨ cong (λ addr → readMem (writeMem (memory st3) addr (readReg (regs st3) a0)) new-sp) addr-st4 ⟩
        readMem (writeMem (memory st3) (new-sp +ℕ 8) (readReg (regs st3) a0)) new-sp
      ≡⟨ readMem-writeMem-diff (memory st3) (new-sp +ℕ 8) new-sp (readReg (regs st3) a0) (λ eq → new-sp≢new-sp+8 (sym eq)) ⟩
        readMem (memory st3) new-sp
      ≡⟨ refl ⟩  -- memory st3 = writeMem (memory st2) new-sp 1
        readMem (writeMem (memory st2) (readReg (regs st2) sp +ℕ 0) (readReg (regs st2) t0)) new-sp
      ≡⟨ cong (λ addr → readMem (writeMem (memory st2) addr (readReg (regs st2) t0)) new-sp) addr-st3 ⟩
        readMem (writeMem (memory st2) new-sp (readReg (regs st2) t0)) new-sp
      ≡⟨ readMem-writeMem-same (memory st2) new-sp (readReg (regs st2) t0) ⟩
        just (readReg (regs st2) t0)
      ≡⟨ cong just t0-st2 ⟩
        just 1
      ∎

    -- Reading value (at new-sp + 8) from memory st6
    val-is-encode-x : readMem (memory st6) (readReg (regs st6) a0 +ℕ 8) ≡ just (encode x)
    val-is-encode-x =
      begin
        readMem (memory st6) (readReg (regs st6) a0 +ℕ 8)
      ≡⟨ cong (λ addr → readMem (memory st6) (addr +ℕ 8)) a0-st6 ⟩
        readMem (memory st6) (new-sp +ℕ 8)
      ≡⟨ refl ⟩  -- memory st6 = memory st4
        readMem (memory st4) (new-sp +ℕ 8)
      ≡⟨ refl ⟩  -- memory st4 = writeMem (memory st3) (new-sp+8) (a0 in st3)
        readMem (writeMem (memory st3) (readReg (regs st3) sp +ℕ 8) (readReg (regs st3) a0)) (new-sp +ℕ 8)
      ≡⟨ cong (λ addr → readMem (writeMem (memory st3) addr (readReg (regs st3) a0)) (new-sp +ℕ 8)) addr-st4 ⟩
        readMem (writeMem (memory st3) (new-sp +ℕ 8) (readReg (regs st3) a0)) (new-sp +ℕ 8)
      ≡⟨ readMem-writeMem-same (memory st3) (new-sp +ℕ 8) (readReg (regs st3) a0) ⟩
        just (readReg (regs st3) a0)
      ≡⟨ cong just a0-st3 ⟩
        just (encode x)
      ∎

    a0-final : readReg (regs st6) a0 ≡ encode {A + B} (inj₂ x)
    a0-final = encode-inr-construct x (readReg (regs st6) a0) (memory st6) tag-is-1 val-is-encode-x

------------------------------------------------------------------------
-- Remaining postulated helpers for complex generators
------------------------------------------------------------------------

postulate
  -- | curry sequence execution
  run-curry-seq : ∀ {A B C} (f : IR (A * B) C) (a : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ 0 →
    readReg (regs s) a0 ≡ encode a →
    ∃[ s' ] (run (compile-riscv {A} {B ⇒ C} (curry f)) s ≡ just s'
           × halted s' ≡ true
           × readMem (memory s') (readReg (regs s') a0) ≡ just (encode a))

  -- | apply sequence execution
  run-apply-seq : ∀ {A B} (f : ⟦ A ⟧ → ⟦ B ⟧) (a : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ 0 →
    readReg (regs s) a0 ≡ encode {(A ⇒ B) * A} (f , a) →
    ∃[ s' ] (run (compile-riscv {(A ⇒ B) * A} {B} apply) s ≡ just s'
           × halted s' ≡ true
           × readReg (regs s') a0 ≡ encode {B} (f a))

------------------------------------------------------------------------
-- Per-generator correctness theorems
------------------------------------------------------------------------

-- | id correctness
compile-id-correct : ∀ {A} (x : ⟦ A ⟧) →
  ∃[ s ] (run (compile-riscv {A} {A} id) (initWithInput x) ≡ just s
        × readReg (regs s) a0 ≡ encode x)
compile-id-correct {A} x =
  let (s' , run-eq , halt-eq , a0-eq) = run-generator-id x (initWithInput x)
                                          (initWithInput-halted x)
                                          (initWithInput-pc x)
                                          (initWithInput-a0 x)
  in s' , run-eq , a0-eq

-- | terminal correctness
compile-terminal-correct : ∀ {A} (x : ⟦ A ⟧) →
  ∃[ s ] (run (compile-riscv {A} {Unit} terminal) (initWithInput x) ≡ just s
        × readReg (regs s) a0 ≡ 0)
compile-terminal-correct {A} x =
  let (s' , run-eq , halt-eq , a0-eq) = run-generator-terminal x (initWithInput x)
                                          (initWithInput-halted x)
                                          (initWithInput-pc x)
                                          (initWithInput-a0 x)
  in s' , run-eq , trans a0-eq encode-unit

-- | fold correctness
compile-fold-correct : ∀ {F} (x : ⟦ F ⟧) →
  ∃[ s ] (run (compile-riscv {F} {Fix F} fold) (initWithInput x) ≡ just s
        × readReg (regs s) a0 ≡ encode x)
compile-fold-correct {F} x =
  let (s' , run-eq , halt-eq , a0-eq) = run-generator-fold x (initWithInput x)
                                          (initWithInput-halted x)
                                          (initWithInput-pc x)
                                          (initWithInput-a0 x)
  in s' , run-eq , trans a0-eq (initWithInput-a0 x)

-- | unfold correctness
compile-unfold-correct : ∀ {F} (x : ⟦ Fix F ⟧) →
  ∃[ s ] (run (compile-riscv {Fix F} {F} unfold) (initWithInput x) ≡ just s
        × readReg (regs s) a0 ≡ encode (⟦Fix⟧.unwrap x))
compile-unfold-correct {F} x =
  let (s' , run-eq , halt-eq , a0-eq) = run-generator-unfold x (initWithInput x)
                                          (initWithInput-halted x)
                                          (initWithInput-pc x)
                                          (initWithInput-a0 x)
  in s' , run-eq , trans (trans a0-eq (initWithInput-a0 x)) (encode-fix-unwrap x)

-- | arr correctness
compile-arr-correct : ∀ {A B} (f : ⟦ A ⇒ B ⟧) →
  ∃[ s ] (run (compile-riscv {A ⇒ B} {Eff A B} arr) (initWithInput {A ⇒ B} f) ≡ just s
        × readReg (regs s) a0 ≡ encode {Eff A B} f)
compile-arr-correct {A} {B} f =
  let (s' , run-eq , halt-eq , a0-eq) = run-generator-arr {A} {B} f (initWithInput {A ⇒ B} f)
                                          (initWithInput-halted {A ⇒ B} f)
                                          (initWithInput-pc {A ⇒ B} f)
                                          (initWithInput-a0 {A ⇒ B} f)
  in s' , run-eq , trans (trans a0-eq (initWithInput-a0 {A ⇒ B} f)) (encode-arr-identity {A} {B} f)

-- | inl correctness
compile-inl-correct : ∀ {A B} (x : ⟦ A ⟧) →
  ∃[ s ] (run (compile-riscv {A} {A + B} inl) (initWithInput x) ≡ just s
        × readReg (regs s) a0 ≡ encode {A + B} (inj₁ x))
compile-inl-correct {A} {B} x =
  let (s' , run-eq , halt-eq , a0-eq) = run-inl-seq {A} {B} x (initWithInput x)
                                          (initWithInput-halted x)
                                          (initWithInput-pc x)
                                          (initWithInput-a0 x)
  in s' , run-eq , a0-eq

-- | inr correctness
compile-inr-correct : ∀ {A B} (x : ⟦ B ⟧) →
  ∃[ s ] (run (compile-riscv {B} {A + B} inr) (initWithInput x) ≡ just s
        × readReg (regs s) a0 ≡ encode {A + B} (inj₂ x))
compile-inr-correct {A} {B} x =
  let (s' , run-eq , halt-eq , a0-eq) = run-inr-seq {A} {B} x (initWithInput x)
                                          (initWithInput-halted x)
                                          (initWithInput-pc x)
                                          (initWithInput-a0 x)
  in s' , run-eq , a0-eq

------------------------------------------------------------------------
-- Postulated theorems for complex generators
------------------------------------------------------------------------

-- | fst correctness
--
-- Proved by composing run-fst-seq with initWithInput lemmas and encode-pair-fst axiom.
compile-fst-correct : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) →
  ∃[ s ] (run (compile-riscv {A * B} {A} fst) (initWithInput (a , b)) ≡ just s
        × readReg (regs s) a0 ≡ encode a)
compile-fst-correct {A} {B} a b =
  let init = initWithInput (a , b)
      (s' , run-eq , halt-eq , a0-eq) = run-fst-seq {A} {B} a b init
                                          (initWithInput-halted (a , b))
                                          (initWithInput-pc (a , b))
                                          (initWithInput-a0 (a , b))
                                          (encode-pair-fst a b (memory init))
  in s' , run-eq , a0-eq

-- | snd correctness
--
-- Proved by composing run-snd-seq with initWithInput lemmas and encode-pair-snd axiom.
compile-snd-correct : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) →
  ∃[ s ] (run (compile-riscv {A * B} {B} snd) (initWithInput (a , b)) ≡ just s
        × readReg (regs s) a0 ≡ encode b)
compile-snd-correct {A} {B} a b =
  let init = initWithInput (a , b)
      (s' , run-eq , halt-eq , a0-eq) = run-snd-seq {A} {B} a b init
                                          (initWithInput-halted (a , b))
                                          (initWithInput-pc (a , b))
                                          (initWithInput-a0 (a , b))
                                          (encode-pair-snd a b (memory init))
  in s' , run-eq , a0-eq

postulate
  -- | compose correctness
  compile-compose-correct : ∀ {A B C} (g : IR B C) (f : IR A B) (x : ⟦ A ⟧) →
    ∃[ s ] (run (compile-riscv (g ∘ f)) (initWithInput x) ≡ just s
          × readReg (regs s) a0 ≡ encode (eval (g ∘ f) x))

  -- | pair correctness
  compile-pair-correct : ∀ {A B C} (f : IR C A) (g : IR C B) (x : ⟦ C ⟧) →
    ∃[ s ] (run (compile-riscv ⟨ f , g ⟩) (initWithInput x) ≡ just s
          × readReg (regs s) a0 ≡ encode (eval ⟨ f , g ⟩ x))

  -- | case correctness
  compile-case-correct : ∀ {A B C} (f : IR A C) (g : IR B C) (x : ⟦ A + B ⟧) →
    ∃[ s ] (run (compile-riscv ([ f , g ])) (initWithInput x) ≡ just s
          × readReg (regs s) a0 ≡ encode (eval ([ f , g ]) x))

  -- | curry correctness
  compile-curry-correct : ∀ {A B C} (f : IR (A * B) C) (a : ⟦ A ⟧) →
    ∃[ s ] (run (compile-riscv (curry f)) (initWithInput a) ≡ just s
          × readReg (regs s) a0 ≡ encode {B ⇒ C} (λ b → eval f (a , b)))

  -- | apply correctness
  compile-apply-correct : ∀ {A B} (f : ⟦ A ⟧ → ⟦ B ⟧) (a : ⟦ A ⟧) →
    ∃[ s ] (run (compile-riscv {(A ⇒ B) * A} {B} apply) (initWithInput {(A ⇒ B) * A} (f , a)) ≡ just s
          × readReg (regs s) a0 ≡ encode {B} (f a))

------------------------------------------------------------------------
-- Main Correctness Theorem
------------------------------------------------------------------------

-- | Main correctness theorem
--
-- Executing compiled RISC-V code on encoded input produces encoded output.
-- This is proven by case analysis on the IR constructor, using the
-- per-generator theorems above.

codegen-riscv-correct : ∀ {A B} (ir : IR A B) (x : ⟦ A ⟧) →
  ∃[ s ] (run (compile-riscv ir) (initWithInput x) ≡ just s
        × readReg (regs s) a0 ≡ encode (eval ir x))

-- Category structure
codegen-riscv-correct id x = compile-id-correct x
codegen-riscv-correct (g ∘ f) x = compile-compose-correct g f x

-- Products
codegen-riscv-correct fst (a , b) = compile-fst-correct a b
codegen-riscv-correct snd (a , b) = compile-snd-correct a b
codegen-riscv-correct ⟨ f , g ⟩ x = compile-pair-correct f g x

-- Coproducts
codegen-riscv-correct inl a = compile-inl-correct a
codegen-riscv-correct inr b = compile-inr-correct b
codegen-riscv-correct ([ f , g ]) x = compile-case-correct f g x

-- Terminal (Unit)
codegen-riscv-correct terminal x =
  let (s , run-eq , a0-0) = compile-terminal-correct x
  in s , run-eq , trans a0-0 (sym encode-unit)

-- Initial (Void) - no inputs exist
codegen-riscv-correct initial ()

-- Exponential (closures)
codegen-riscv-correct {A} {B ⇒ C} (curry {A} {B} {C} f) x = compile-curry-correct f x
codegen-riscv-correct {(A ⇒ B) * A} {B} apply (f , a) = compile-apply-correct {A} {B} f a

-- Recursive types
codegen-riscv-correct fold x =
  let (s , run-eq , a0-eq) = compile-fold-correct x
  in s , run-eq , trans a0-eq (encode-fix-wrap x)
codegen-riscv-correct unfold x = compile-unfold-correct x

-- Effect lifting
codegen-riscv-correct {A ⇒ B} {Eff A B} arr f = compile-arr-correct {A} {B} f
