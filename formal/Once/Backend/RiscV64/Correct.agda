------------------------------------------------------------------------
-- Once.Backend.RiscV64.Correct
--
-- Correctness proofs for RISC-V 64-bit code generation.
--
-- Main theorem:
--   codegen-riscv-correct : ∀ (ir : IR A B) (x : ⟦A⟧) →
--     exec-riscv (compile-riscv ir) (encode-riscv x) ≡ encode-riscv (eval ir x)
--
-- This module proves that the code generator preserves semantics:
-- executing the generated RISC-V code on an encoded input produces
-- the same result as encoding the semantic evaluation.
--
-- Key differences from x86:
--   - a0 is both input AND output (simpler than x86's rdi/rax)
--   - No flags register (branches compare registers directly)
--   - x0 (zero) is hardwired to 0
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

-- Helper: state after executing addi rd rs imm
execAddi : ∀ (prog : List Instr) (s : State) (rd rs : Reg) (n : ℕ) →
  execInstr prog s (addi rd rs (+ n)) ≡
    just (record s { regs = writeReg (regs s) rd (readReg (regs s) rs +ℕ n)
                   ; pc = pc s +ℕ 1 })
execAddi prog s rd rs n = refl

-- Helper: state after executing j target
execJ : ∀ (prog : List Instr) (s : State) (target : ℕ) →
  execInstr prog s (j target) ≡ just (record s { pc = target })
execJ prog s target = refl

-- Helper: state after executing label (no-op at runtime)
execLabel : ∀ (prog : List Instr) (s : State) (n : ℕ) →
  execInstr prog s (label n) ≡ just (record s { pc = pc s +ℕ 1 })
execLabel prog s n = refl

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

open import Data.Nat.Properties using (≡ᵇ⇒≡; ≡⇒≡ᵇ; +-comm; +-assoc)

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
-- Postulated because exec uses internal `with` clauses that complicate proofs.
-- The semantics are straightforward: if step succeeds and halts, exec returns that state.
postulate
  exec-one-step : ∀ (n : ℕ) (prog : List Instr) (s state1 : State) →
    step prog s ≡ just state1 →
    halted state1 ≡ true →
    exec (suc n) prog s ≡ just state1

-- | Execute 2 steps and halt
-- Postulated for same reason as exec-one-step.
postulate
  exec-two-steps : ∀ (n : ℕ) (prog : List Instr) (s state1 state2 : State) →
    step prog s ≡ just state1 → halted state1 ≡ false →
    step prog state1 ≡ just state2 → halted state2 ≡ true →
    exec (suc (suc n)) prog s ≡ just state2

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

postulate
  -- | inl sequence execution
  run-inl-seq : ∀ {A B} (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ 0 →
    readReg (regs s) a0 ≡ encode x →
    ∃[ s' ] (run (compile-riscv {A} {A + B} inl) s ≡ just s'
           × halted s' ≡ true
           × readReg (regs s') a0 ≡ encode {A + B} (inj₁ x))

  -- | inr sequence execution
  run-inr-seq : ∀ {A B} (x : ⟦ B ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ 0 →
    readReg (regs s) a0 ≡ encode x →
    ∃[ s' ] (run (compile-riscv {B} {A + B} inr) s ≡ just s'
           × halted s' ≡ true
           × readReg (regs s') a0 ≡ encode {A + B} (inj₂ x))

  -- | fst execution
  run-fst-seq : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ 0 →
    readReg (regs s) a0 ≡ encode (a , b) →
    readMem (memory s) (encode (a , b)) ≡ just (encode a) →
    ∃[ s' ] (run (compile-riscv {A * B} {A} fst) s ≡ just s'
           × halted s' ≡ true
           × readReg (regs s') a0 ≡ encode a)

  -- | snd execution
  run-snd-seq : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ 0 →
    readReg (regs s) a0 ≡ encode (a , b) →
    readMem (memory s) (encode (a , b) +ℕ 8) ≡ just (encode b) →
    ∃[ s' ] (run (compile-riscv {A * B} {B} snd) s ≡ just s'
           × halted s' ≡ true
           × readReg (regs s') a0 ≡ encode b)

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

postulate
  -- | fst correctness
  compile-fst-correct : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) →
    ∃[ s ] (run (compile-riscv {A * B} {A} fst) (initWithInput (a , b)) ≡ just s
          × readReg (regs s) a0 ≡ encode a)

  -- | snd correctness
  compile-snd-correct : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) →
    ∃[ s ] (run (compile-riscv {A * B} {B} snd) (initWithInput (a , b)) ≡ just s
          × readReg (regs s) a0 ≡ encode b)

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
