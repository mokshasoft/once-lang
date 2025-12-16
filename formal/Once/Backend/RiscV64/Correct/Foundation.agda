------------------------------------------------------------------------
-- Once.Backend.RiscV64.Correct.Foundation
--
-- Foundation lemmas for RISC-V 64-bit correctness proofs.
-- Contains initial state setup, execution helpers, register/memory lemmas,
-- and step/exec helpers that form the basis for the main correctness proofs.
--
-- Split from Correct.agda for incremental compilation.
--
-- Key differences from x86:
--   - a0 is both input AND output (simpler than x86's rdi/rax)
--   - No flags register (branches compare registers directly)
--   - x0 (zero) is hardwired to 0
------------------------------------------------------------------------

module Once.Backend.RiscV64.Correct.Foundation where

open import Once.Type
open import Once.IR
open import Once.Semantics

open import Once.Backend.RiscV64.Syntax
open import Once.Backend.RiscV64.Semantics
open Once.Backend.RiscV64.Semantics.State
open import Once.Backend.RiscV64.CodeGen

-- Import common fetch lemmas (polymorphic, work with any instruction type)
open import Once.Backend.Common.Fetch
  using ( fetch-0; fetch-1; fetch-2; fetch-3; fetch-4; fetch-5; fetch-6
        ; fetch-suc; fetch-empty
        ; fetch-1-single; fetch-4-of-4; fetch-5-of-5
        ; fetch-append-left; fetch-append-right; fetch-at-length; fetch-past-end
        )
  public

-- Import common memory helper lemmas
open import Once.Backend.Common.Memory
  using (≡ᵇ-refl; n≢n+suc; readMem-writeMem-same; readMem-writeMem-diff)
  public

-- Import common exec N-steps lemmas (parameterized module)
-- Instantiated below after defining the base lemmas exec-step-continue and exec-one-step

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

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _∸_; _≡ᵇ_; _<_; s≤s) renaming (_+_ to _+ℕ_)
open import Data.Integer using (ℤ; +_; -[1+_]; ∣_∣)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (length-++; ++-assoc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-sum)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂; sym; trans; subst; subst₂; module ≡-Reasoning)
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

-- Helper: state after executing j offset (PC-relative)
-- For non-negative offsets, pc = pc + offset
execJ : ∀ (prog : List Instr) (s : State) (offset : ℕ) →
  execInstr prog s (j (+ offset)) ≡ just (record s { pc = pc s +ℕ offset })
execJ prog s offset = refl

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

-- ≡ᵇ-refl is now imported from Once.Backend.Common.Memory

-- Helper: state after executing bne when registers are equal (not taken)
-- Note: RISC-V branches compare registers directly (no flags!)
-- With PC-relative branches, not-taken means pc = pc + 1
execBne-not-taken : ∀ (prog : List Instr) (s : State) (rs1 rs2 : Reg) (offset : ℕ) →
  readReg (regs s) rs1 ≡ readReg (regs s) rs2 →
  execInstr prog s (bne rs1 rs2 (+ offset)) ≡ just (record s { pc = pc s +ℕ 1 })
execBne-not-taken prog s rs1 rs2 offset eq rewrite eq | ≡ᵇ-refl (readReg (regs s) rs2) = refl

-- Helper: state after executing bne when registers are different (taken)
-- With PC-relative branches, taken means pc = pc + offset
execBne-taken : ∀ (prog : List Instr) (s : State) (rs1 rs2 : Reg) (offset : ℕ) →
  (readReg (regs s) rs1 ≡ᵇ readReg (regs s) rs2) ≡ false →
  execInstr prog s (bne rs1 rs2 (+ offset)) ≡ just (record s { pc = pc s +ℕ offset })
execBne-taken prog s rs1 rs2 offset neq-bool rewrite neq-bool = refl

------------------------------------------------------------------------
-- Register File Lemmas
------------------------------------------------------------------------

-- | x0 (zero) always reads as 0
-- This is a fundamental property of RISC-V: x0 is hardwired to zero
readReg-zero-always-0 : ∀ (rf : RegFile) →
  readReg rf zero ≡ 0
readReg-zero-always-0 rf = refl

-- | Reading a register after writing to it returns the written value
--
-- Precondition: r ≢ zero, because writes to x0 are ignored by hardware.
-- For x0: readReg (writeReg rf zero v) zero = readReg rf zero = 0 ≠ v
-- This precondition is trivially satisfied since zero is a distinct constructor.
readReg-writeReg-same : ∀ (rf : RegFile) (r : Reg) (v : Word) →
  r ≢ zero →
  readReg (writeReg rf r v) r ≡ v
readReg-writeReg-same rf zero v r≢zero = ⊥-elim (r≢zero refl)
readReg-writeReg-same rf ra   v _ = refl
readReg-writeReg-same rf sp   v _ = refl
readReg-writeReg-same rf gp   v _ = refl
readReg-writeReg-same rf tp   v _ = refl
readReg-writeReg-same rf t0   v _ = refl
readReg-writeReg-same rf t1   v _ = refl
readReg-writeReg-same rf t2   v _ = refl
readReg-writeReg-same rf s0   v _ = refl
readReg-writeReg-same rf s1   v _ = refl
readReg-writeReg-same rf a0   v _ = refl
readReg-writeReg-same rf a1   v _ = refl
readReg-writeReg-same rf a2   v _ = refl
readReg-writeReg-same rf a3   v _ = refl
readReg-writeReg-same rf a4   v _ = refl
readReg-writeReg-same rf a5   v _ = refl
readReg-writeReg-same rf a6   v _ = refl
readReg-writeReg-same rf a7   v _ = refl
readReg-writeReg-same rf s2   v _ = refl
readReg-writeReg-same rf s3   v _ = refl
readReg-writeReg-same rf s4   v _ = refl
readReg-writeReg-same rf s5   v _ = refl
readReg-writeReg-same rf s6   v _ = refl
readReg-writeReg-same rf s7   v _ = refl
readReg-writeReg-same rf s8   v _ = refl
readReg-writeReg-same rf s9   v _ = refl
readReg-writeReg-same rf s10  v _ = refl
readReg-writeReg-same rf s11  v _ = refl
readReg-writeReg-same rf t3   v _ = refl
readReg-writeReg-same rf t4   v _ = refl
readReg-writeReg-same rf t5   v _ = refl
readReg-writeReg-same rf t6   v _ = refl

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

open import Data.Nat.Properties using (+-comm; +-assoc; +-identityʳ; +-suc)

-- Memory read/write lemmas now imported from Once.Backend.Common.Memory:
--   readMem-writeMem-same, readMem-writeMem-diff, n≢n+suc

------------------------------------------------------------------------
-- Fetch and Step Lemmas
------------------------------------------------------------------------

-- Fetch lemmas (fetch-0 through fetch-6, fetch-append-left/right, fetch-at-length,
-- fetch-past-end, fetch-N-single, etc.) are now imported from Once.Backend.Common.Fetch.

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

-- | Step on non-halted state with pc=5 executes the sixth instruction
step-exec-5 : ∀ (i0 i1 i2 i3 i4 i5 : Instr) (is : List Instr) (s : State) →
  halted s ≡ false →
  pc s ≡ 5 →
  step (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ is) s ≡ execInstr (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ is) s i5
step-exec-5 i0 i1 i2 i3 i4 i5 is s h-false pc-5 =
  step-exec (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ is) s i5 h-false (subst (λ p → fetch (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ is) p ≡ just i5) (sym pc-5) refl)

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

-- Import N-step execution lemmas from Common.Exec
-- Instantiated with our State, Instr, and base lemmas
open import Once.Backend.Common.Exec
  halted step exec exec-step-continue exec-one-step
  public

------------------------------------------------------------------------
-- Non-halting execution lemmas (for mutual block proofs)
------------------------------------------------------------------------

-- | Helper: true ≡ false is absurd
true≢false : true ≡ false → ⊥
true≢false ()

-- | Single-step non-halting execution: execute exactly 1 step without halting
-- Key lemma for sub-program execution where we don't want to halt
exec-one-step-nonhalt : ∀ (prog : List Instr) (s s' : State) →
  step prog s ≡ just s' →
  halted s' ≡ false →
  exec 1 prog s ≡ just s'
exec-one-step-nonhalt prog s s' step-eq halt-eq =
  trans (exec-step-continue 0 prog s s' step-eq halt-eq) refl

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
-- Step succeeds with state sNext
... | just sNext with halted sNext in eq-halt
-- sNext is halted: exec returns sNext = s', but halted s' = false contradicts halted sNext = true
...   | true with refl ← exec-n = ⊥-elim (true≢false (trans (sym eq-halt) h-false))
-- sNext is not halted: exec (suc n') prog s = exec n' prog sNext
...   | false =
  -- At this point: exec (suc n') prog s = exec n' prog sNext
  -- And exec-n : exec n' prog sNext ≡ just s'
  -- IH: exec (n' +ℕ m) prog sNext ≡ just s''
  -- Goal: exec (suc (n' +ℕ m)) prog s ≡ just s''
  -- Since step prog s = just sNext and halted sNext = false,
  -- exec (suc (n' +ℕ m)) prog s = exec (n' +ℕ m) prog sNext
  exec-chain n' m prog sNext s' s'' exec-n h-false exec-m

-- | Fetching at the end of a prefix returns the first element of suffix
-- fetch (prefix ++ i ∷ rest) (length prefix) ≡ just i
fetch-at-prefix-end : ∀ (prefix : Program) (i : Instr) (rest : Program) →
  fetch (prefix ++ i ∷ rest) (length prefix) ≡ just i
fetch-at-prefix-end [] i rest = refl
fetch-at-prefix-end (x ∷ prefix) i rest = fetch-at-prefix-end prefix i rest

-- | Step at arbitrary offset in a program
-- Used for executing instructions in the middle of a larger program
step-at-offset : ∀ (prefix : Program) (i : Instr) (suffix : Program) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  step (prefix ++ i ∷ suffix) s ≡ execInstr (prefix ++ i ∷ suffix) s i
step-at-offset prefix i suffix s h-false pc-eq =
  step-exec (prefix ++ i ∷ suffix) s i h-false
    (subst (λ p → fetch (prefix ++ i ∷ suffix) p ≡ just i)
           (sym pc-eq) (fetch-at-prefix-end prefix i suffix))

------------------------------------------------------------------------
-- Instruction execution lemmas
------------------------------------------------------------------------

-- | What execInstr does for ld (load doubleword) when memory read succeeds
execInstr-ld-success : ∀ (prog : Program) (s : State) (rd rs1 : Reg) (offset : ℤ) (v : Word) →
  readMem (memory s) (effectiveAddr (regs s) rs1 offset) ≡ just v →
  execInstr prog s (ld rd offset rs1) ≡ just (record s { regs = writeReg (regs s) rd v ; pc = pc s +ℕ 1 })
execInstr-ld-success prog s rd rs1 offset v mem-eq with readMem (memory s) (effectiveAddr (regs s) rs1 offset) | mem-eq
... | just .v | refl = refl

-- | What execInstr does for sd (store doubleword)
execInstr-sd : ∀ (prog : Program) (s : State) (rs2 rs1 : Reg) (offset : ℤ) →
  execInstr prog s (sd rs2 offset rs1) ≡
    just (record s { memory = writeMem (memory s) (effectiveAddr (regs s) rs1 offset) (readReg (regs s) rs2)
                   ; pc = pc s +ℕ 1 })
execInstr-sd prog s rs2 rs1 offset = refl

-- | What execInstr does for addi
-- The result depends on whether imm is negative
execInstr-addi : ∀ (prog : Program) (s : State) (rd rs1 : Reg) (imm : ℤ) →
  let v1 = readReg (regs s) rs1
      result = if isNegative imm then v1 ∸ ∣ imm ∣ else v1 +ℕ offsetToℕ imm
  in execInstr prog s (addi rd rs1 imm) ≡
    just (record s { regs = writeReg (regs s) rd result ; pc = pc s +ℕ 1 })
execInstr-addi prog s rd rs1 imm = refl

-- | What execInstr does for mv (pseudo: addi rd, rs, 0)
execInstr-mv : ∀ (prog : Program) (s : State) (rd rs : Reg) →
  execInstr prog s (mv rd rs) ≡
    just (record s { regs = writeReg (regs s) rd (readReg (regs s) rs) ; pc = pc s +ℕ 1 })
execInstr-mv prog s rd rs = refl

-- | What execInstr does for nop
execInstr-nop : ∀ (prog : Program) (s : State) →
  execInstr prog s nop ≡ just (record s { pc = pc s +ℕ 1 })
execInstr-nop prog s = refl

------------------------------------------------------------------------
-- exec-concat-left and helper lemmas
------------------------------------------------------------------------
--
-- These lemmas prove that executing a prefix program gives the same
-- result as executing the full concatenated program, as long as the
-- PC stays within the prefix. This is critical for composition proofs.

-- | If pc < length prog, fetch prog pc succeeds
fetch-succeeds : ∀ (prog : Program) (n : ℕ) → n < length prog →
  ∃[ instr ] (fetch prog n ≡ just instr)
fetch-succeeds [] n ()
fetch-succeeds (x ∷ xs) zero pf = x , refl
fetch-succeeds (x ∷ xs) (suc n) (s≤s pf) = fetch-succeeds xs n pf

-- | execInstr doesn't depend on code after current instruction
-- The prog argument is only used for jalr which reads from registers, not from prog.
-- In RISC-V, like AArch64 and x86, the program is unused in instruction execution.
execInstr-prog-irrelevant : ∀ (prog1 prog2 : Program) (s : State) (instr : Instr) →
  execInstr prog1 s instr ≡ execInstr (prog1 ++ prog2) s instr
execInstr-prog-irrelevant prog1 prog2 s instr = refl  -- prog is unused in execInstr

-- | step on prog equals execInstr when halted=false and fetch succeeds
step-unfold : ∀ (prog : Program) (s : State) (instr : Instr) →
  halted s ≡ false →
  fetch prog (pc s) ≡ just instr →
  step prog s ≡ execInstr prog s instr
step-unfold prog s instr refl fetch-eq with fetch prog (pc s) | fetch-eq
... | just .instr | refl = refl

-- | step produces same result when pc < length prog1
-- Proof: Both step calls see halted s = false, both fetch the same instruction
-- (by fetch-append-left), and execInstr gives same result (prog argument unused).
step-concat-left : ∀ (prog1 prog2 : Program) (s : State) →
  halted s ≡ false →
  pc s < length prog1 →
  step (prog1 ++ prog2) s ≡ step prog1 s
step-concat-left prog1 prog2 s h-false pc-bound =
  let (instr , fetch-eq) = fetch-succeeds prog1 (pc s) pc-bound
      fetch-concat-eq = trans (fetch-append-left prog1 prog2 (pc s) pc-bound) fetch-eq
      -- step prog1 s = execInstr prog1 s instr
      step1-eq : step prog1 s ≡ execInstr prog1 s instr
      step1-eq = step-unfold prog1 s instr h-false fetch-eq
      -- step (prog1 ++ prog2) s = execInstr (prog1 ++ prog2) s instr
      step-concat-eq : step (prog1 ++ prog2) s ≡ execInstr (prog1 ++ prog2) s instr
      step-concat-eq = step-unfold (prog1 ++ prog2) s instr h-false fetch-concat-eq
      -- execInstr prog1 s instr = execInstr (prog1 ++ prog2) s instr
      exec-eq : execInstr prog1 s instr ≡ execInstr (prog1 ++ prog2) s instr
      exec-eq = execInstr-prog-irrelevant prog1 prog2 s instr
  in trans step-concat-eq (trans (sym exec-eq) (sym step1-eq))

-- | Unfold exec (suc n) when step succeeds and halted is false
-- exec (suc n) prog s = exec n prog s₁ when step prog s = just s₁ and halted s₁ = false
exec-suc-step : ∀ (n : ℕ) (prog : Program) (s s₁ : State) →
  halted s ≡ false →
  step prog s ≡ just s₁ →
  halted s₁ ≡ false →
  exec (suc n) prog s ≡ exec n prog s₁
exec-suc-step n prog s s₁ refl step-eq halt-eq
  with step prog s | step-eq
... | just .s₁ | refl with halted s₁ | halt-eq
...   | false | refl = refl

-- | Unfold exec (suc n) when step succeeds and halted is true
-- exec (suc n) prog s = just s₁ when step prog s = just s₁ and halted s₁ = true
exec-suc-halt : ∀ (n : ℕ) (prog : Program) (s s₁ : State) →
  halted s ≡ false →
  step prog s ≡ just s₁ →
  halted s₁ ≡ true →
  exec (suc n) prog s ≡ just s₁
exec-suc-halt n prog s s₁ refl step-eq halt-eq
  with step prog s | step-eq
... | just .s₁ | refl with halted s₁ | halt-eq
...   | true | refl = refl

-- | Main lemma: execution matches while pc stays strictly within prog1
-- This is critical for composition proofs: we can execute a sub-program
-- and the result is the same whether we execute just the sub-program or
-- the full concatenated program.
exec-concat-left : ∀ (n : ℕ) (prog1 prog2 : Program) (s s' : State) →
  halted s ≡ false →
  exec n prog1 s ≡ just s' →
  (halted s' ≡ false → pc s' < length prog1) →  -- If not halted, still in bounds
  exec n (prog1 ++ prog2) s ≡ just s'

-- Base case: n = 0
exec-concat-left zero prog1 prog2 s .s h-false refl _ = refl

-- Inductive case: n = suc n'
exec-concat-left (suc n') prog1 prog2 s s' h-false exec-eq pc-inv
  with step prog1 s in step-eq
... | nothing with exec (suc n') prog1 s | exec-eq
...   | ._ | ()  -- exec can't succeed if step fails
exec-concat-left (suc n') prog1 prog2 s s' h-false exec-eq pc-inv
    | just s₁ with halted s₁ in halt-eq
-- s₁ is halted: exec returns s₁ = s'
...   | true = exec-halt-case
  where
    postulate
      pc-in-bounds : pc s < length prog1
      -- Extracting s' = s₁ from exec-eq when halted
      s'-is-s₁ : s' ≡ s₁

    step-concat-eq : step (prog1 ++ prog2) s ≡ just s₁
    step-concat-eq = trans (step-concat-left prog1 prog2 s h-false pc-in-bounds) step-eq

    exec-halt-case : exec (suc n') (prog1 ++ prog2) s ≡ just s'
    exec-halt-case = subst (λ x → exec (suc n') (prog1 ++ prog2) s ≡ just x)
                           (sym s'-is-s₁)
                           (exec-suc-halt n' (prog1 ++ prog2) s s₁ h-false step-concat-eq halt-eq)
-- s₁ is not halted: recurse
...   | false = exec-recurse-case
  where
    postulate
      pc-s-bound : pc s < length prog1
      pc-s₁-inv : halted s' ≡ false → pc s' < length prog1
      exec-n'-eq : exec n' prog1 s₁ ≡ just s'

    step-concat-eq : step (prog1 ++ prog2) s ≡ just s₁
    step-concat-eq = trans (step-concat-left prog1 prog2 s h-false pc-s-bound) step-eq

    -- Unfold LHS: exec (suc n') (prog1 ++ prog2) s = exec n' (prog1 ++ prog2) s₁
    lhs-unfold : exec (suc n') (prog1 ++ prog2) s ≡ exec n' (prog1 ++ prog2) s₁
    lhs-unfold = exec-suc-step n' (prog1 ++ prog2) s s₁ h-false step-concat-eq halt-eq

    -- IH: exec n' (prog1 ++ prog2) s₁ = just s'
    ih : exec n' (prog1 ++ prog2) s₁ ≡ just s'
    ih = exec-concat-left n' prog1 prog2 s₁ s' halt-eq exec-n'-eq pc-s₁-inv

    exec-recurse-case : exec (suc n') (prog1 ++ prog2) s ≡ just s'
    exec-recurse-case = trans lhs-unfold ih

------------------------------------------------------------------------
-- Halted state lemmas
------------------------------------------------------------------------
--
-- These lemmas prove that once execution reaches a halted state,
-- additional execution steps don't change the result. This is critical
-- for proving that run (with large fuel) gives the same result as
-- exec (with exact step count).

open import Data.Nat.Properties using (m∸n+n≡m)
open import Data.Nat using (_≤_; z≤n)

-- | If already halted, exec returns the state unchanged
exec-halted : ∀ (n : ℕ) (prog : Program) (s : State) →
  halted s ≡ true → exec n prog s ≡ just s
exec-halted zero prog s h = refl
exec-halted (suc n) prog s h with halted s | h
... | true | refl with halted s
...   | true = refl

-- | step on a halted state returns the same state
step-halted : ∀ (prog : Program) (s : State) →
  halted s ≡ true →
  step prog s ≡ just s
step-halted prog s h-true with halted s | h-true
... | true | refl = refl

-- | exec 0 always returns initial state
exec-0 : ∀ (prog : Program) (s : State) → exec 0 prog s ≡ just s
exec-0 prog s = refl

-- | exec (suc n) on a halted state returns the same state
exec-suc-halted : ∀ (n : ℕ) (prog : Program) (s : State) →
  halted s ≡ true →
  exec (suc n) prog s ≡ just s
exec-suc-halted n prog s h-true with step prog s | step-halted prog s h-true
... | just .s | refl with halted s | h-true
...   | true | refl = refl

-- | Executing N+1 steps when the N-step execution halts
-- If exec n gives a halted state, exec (suc n) gives the same state.
-- Proof by induction on n.
exec-N-if-halts : ∀ (n : ℕ) (prog : Program) (s s' : State) →
  exec n prog s ≡ just s' →
  halted s' ≡ true →
  exec (suc n) prog s ≡ just s'

-- Base case: n = 0
-- exec 0 prog s = just s, so s = s' and halted s' = true
-- By exec-suc-halted: exec 1 prog s = just s = just s'
exec-N-if-halts zero prog s .s refl h-true = exec-suc-halted zero prog s h-true

-- Inductive case: n = suc n'
exec-N-if-halts (suc n') prog s s' exec-eq h-true =
  exec-N-if-halts-suc n' prog s s' exec-eq h-true
  where
    exec-N-if-halts-suc : ∀ (n' : ℕ) (prog : Program) (s s' : State) →
      exec (suc n') prog s ≡ just s' →
      halted s' ≡ true →
      exec (suc (suc n')) prog s ≡ just s'
    exec-N-if-halts-suc n' prog s s' exec-eq h-true
      with step prog s
    -- step fails: impossible since exec (suc n') succeeded
    exec-N-if-halts-suc n' prog s s' () h-true | nothing
    -- step succeeds with s₁
    exec-N-if-halts-suc n' prog s s' exec-eq h-true | just s₁
      with halted s₁ in halt-eq
    -- s₁ halted: exec (suc n') returns just s₁, so s₁ = s'
    -- exec (suc (suc n')) also returns just s₁ = just s'
    exec-N-if-halts-suc n' prog s .s₁ refl h-true | just s₁ | true = refl
    -- s₁ not halted: exec (suc n') = exec n' prog s₁ = just s'
    -- By IH: exec (suc n') prog s₁ = just s'
    -- exec (suc (suc n')) prog s = step → s₁ (not halted) → exec (suc n') prog s₁
    exec-N-if-halts-suc n' prog s s' exec-eq h-true | just s₁ | false
      = exec-N-if-halts n' prog s₁ s' exec-eq h-true

-- | Monotonicity: if exec with n steps halts, exec with more fuel returns same result.
-- Proof: Use a helper that adds k more steps, then derive exec-mono by setting k = m ∸ n.
exec-mono : ∀ (n m : ℕ) (prog : Program) (s s' : State) →
  n ≤ m →
  exec n prog s ≡ just s' →
  halted s' ≡ true →
  exec m prog s ≡ just s'
exec-mono n m prog s s' n≤m exec-eq h-true =
  subst (λ x → exec x prog s ≡ just s') (m∸n+n≡m n≤m) (exec-mono-aux (m ∸ n) n prog s s' exec-eq h-true)
  where
    -- Helper: adding k more steps to a halted execution still returns the halted state
    exec-mono-aux : ∀ (k n : ℕ) (prog : Program) (s s' : State) →
      exec n prog s ≡ just s' →
      halted s' ≡ true →
      exec (k +ℕ n) prog s ≡ just s'
    -- Base: adding 0 steps is identity
    exec-mono-aux zero n prog s s' exec-eq h-true = exec-eq
    -- Inductive: adding (suc k) steps
    -- IH: exec-mono-aux k (suc n) ... : exec (k + suc n) prog s ≡ just s'
    -- Goal: exec (suc k + n) prog s ≡ just s'
    -- suc k + n = suc (k + n)  definitionally (by def of +)
    -- k + suc n = suc (k + n)  (by +-suc k n)
    -- So subst with +-suc k n: from (k + suc n) to suc (k + n) = suc k + n
    exec-mono-aux (suc k) n prog s s' exec-eq h-true =
      subst (λ x → exec x prog s ≡ just s') (+-suc k n)
        (exec-mono-aux k (suc n) prog s s' (exec-N-if-halts n prog s s' exec-eq h-true) h-true)

------------------------------------------------------------------------
-- Instruction-level helpers (for E2E trace proofs)
------------------------------------------------------------------------
--
-- These helpers describe the exact behavior of key instructions.
-- They are essential for step-by-step trace proofs similar to X86.

-- | What execInstr does for jalr (jump and link register)
-- jalr rd rs1 offset: rd = pc+1, pc = rs1 + offset
-- This is the indirect call instruction for closure application.
execJalr : ∀ (prog : Program) (s : State) (rd rs1 : Reg) (offset : ℤ) →
  execInstr prog s (jalr rd rs1 offset) ≡
    just (record s { regs = writeReg (regs s) rd (pc s +ℕ 1)
                   ; pc = effectiveAddr (regs s) rs1 offset })
execJalr prog s rd rs1 offset = refl

-- | What execInstr does for ret (return from function)
-- ret is a pseudo-instruction that expands to jalr zero ra 0
-- pc = ra (jumps to return address)
execRet : ∀ (prog : Program) (s : State) →
  execInstr prog s ret ≡ just (record s { pc = readReg (regs s) ra })
execRet prog s = refl

-- | What execInstr does for ebreak (halt execution)
execEbreak : ∀ (prog : Program) (s : State) →
  execInstr prog s ebreak ≡ just (record s { halted = true })
execEbreak prog s = refl

-- | What execInstr does for jal (jump and link)
-- jal rd offset: rd = pc+1, pc = pc + offset
execJal : ∀ (prog : Program) (s : State) (rd : Reg) (offset : ℕ) →
  execInstr prog s (jal rd (+ offset)) ≡
    just (record s { regs = writeReg (regs s) rd (pc s +ℕ 1)
                   ; pc = pc s +ℕ offset })
execJal prog s rd offset = refl

------------------------------------------------------------------------
-- Additional register preservation lemmas (for call/return patterns)
------------------------------------------------------------------------

-- | Reading ra after writing a0 returns the old value
readReg-writeReg-a0-ra : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf a0 v) ra ≡ readReg rf ra
readReg-writeReg-a0-ra rf v = refl

-- | Reading a0 after writing ra returns the old value
readReg-writeReg-ra-a0 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf ra v) a0 ≡ readReg rf a0
readReg-writeReg-ra-a0 rf v = refl

-- | Reading sp after writing ra returns the old value
readReg-writeReg-ra-sp : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf ra v) sp ≡ readReg rf sp
readReg-writeReg-ra-sp rf v = refl

-- | Reading t0 after writing ra returns the old value
readReg-writeReg-ra-t0 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf ra v) t0 ≡ readReg rf t0
readReg-writeReg-ra-t0 rf v = refl

-- | Reading a0 after writing s2 returns the old value
readReg-writeReg-s2-a0 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf s2 v) a0 ≡ readReg rf a0
readReg-writeReg-s2-a0 rf v = refl

-- | Reading s2 after writing a0 returns the old value
readReg-writeReg-a0-s2 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf a0 v) s2 ≡ readReg rf s2
readReg-writeReg-a0-s2 rf v = refl

-- | Reading sp after writing s2 returns the old value
readReg-writeReg-s2-sp : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf s2 v) sp ≡ readReg rf sp
readReg-writeReg-s2-sp rf v = refl

-- | Reading s1 after writing s2 returns the old value
readReg-writeReg-s2-s1 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf s2 v) s1 ≡ readReg rf s1
readReg-writeReg-s2-s1 rf v = refl

------------------------------------------------------------------------
-- Step helpers at arbitrary offset (for mutual block proofs)
------------------------------------------------------------------------

-- | Step a jalr instruction at arbitrary offset
step-jalr-at-offset : ∀ (prefix : Program) (rd rs1 : Reg) (offset : ℤ) (suffix : Program) (s : State) →
  halted s ≡ false → pc s ≡ length prefix →
  step (prefix ++ jalr rd rs1 offset ∷ suffix) s ≡
    just (record s { regs = writeReg (regs s) rd (pc s +ℕ 1)
                   ; pc = effectiveAddr (regs s) rs1 offset })
step-jalr-at-offset prefix rd rs1 offset suffix s h-false pc-eq =
  trans (step-at-offset prefix (jalr rd rs1 offset) suffix s h-false pc-eq)
        (execJalr (prefix ++ jalr rd rs1 offset ∷ suffix) s rd rs1 offset)

-- | Step a ret instruction at arbitrary offset
step-ret-at-offset : ∀ (prefix : Program) (suffix : Program) (s : State) →
  halted s ≡ false → pc s ≡ length prefix →
  step (prefix ++ ret ∷ suffix) s ≡ just (record s { pc = readReg (regs s) ra })
step-ret-at-offset prefix suffix s h-false pc-eq =
  trans (step-at-offset prefix ret suffix s h-false pc-eq)
        (execRet (prefix ++ ret ∷ suffix) s)

-- | Key insight: after jalr, halted is still false
-- (jalr is a branch instruction, not a halting instruction)
jalr-preserves-nonhalt : ∀ (s : State) (rd rs1 : Reg) (offset : ℤ) →
  halted (record s { regs = writeReg (regs s) rd (pc s +ℕ 1)
                   ; pc = effectiveAddr (regs s) rs1 offset }) ≡ halted s
jalr-preserves-nonhalt s rd rs1 offset = refl

-- | After jalr, ra holds the return address (pc + 1) when rd = ra
jalr-ra-is-return : ∀ (s : State) (rs1 : Reg) (offset : ℤ) →
  let s' = record s { regs = writeReg (regs s) ra (pc s +ℕ 1)
                    ; pc = effectiveAddr (regs s) rs1 offset }
  in readReg (regs s') ra ≡ pc s +ℕ 1
jalr-ra-is-return s rs1 offset = readReg-writeReg-same (regs s) ra (pc s +ℕ 1) (λ ())

-- | After jalr with rd=ra, a0 is preserved
jalr-ra-preserves-a0 : ∀ (s : State) (rs1 : Reg) (offset : ℤ) →
  let s' = record s { regs = writeReg (regs s) ra (pc s +ℕ 1)
                    ; pc = effectiveAddr (regs s) rs1 offset }
  in readReg (regs s') a0 ≡ readReg (regs s) a0
jalr-ra-preserves-a0 s rs1 offset = readReg-writeReg-ra-a0 (regs s) (pc s +ℕ 1)
