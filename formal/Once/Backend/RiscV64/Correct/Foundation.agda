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
open import Data.Nat using (ℕ; zero; suc; _∸_; _≡ᵇ_; _<_; _≤_; s≤s; _≟_; _≥_) renaming (_+_ to _+ℕ_)
open import Relation.Nullary using (yes; no; ¬_)
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

-- | Reading s1 after writing sp returns the old value
readReg-writeReg-sp-s1 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf sp v) s1 ≡ readReg rf s1
readReg-writeReg-sp-s1 rf v = refl

-- | Reading ra after writing sp returns the old value
readReg-writeReg-sp-ra : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf sp v) ra ≡ readReg rf ra
readReg-writeReg-sp-ra rf v = refl

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

-- | Reading ra after writing s1 returns the old value
readReg-writeReg-s1-ra : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf s1 v) ra ≡ readReg rf ra
readReg-writeReg-s1-ra rf v = refl

-- | Reading s2 after writing s1 returns the old value
readReg-writeReg-s1-s2 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf s1 v) s2 ≡ readReg rf s2
readReg-writeReg-s1-s2 rf v = refl

-- | Reading s0 after writing sp returns the old value
readReg-writeReg-sp-s0 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf sp v) s0 ≡ readReg rf s0
readReg-writeReg-sp-s0 rf v = refl

-- | Reading s0 after writing a0 returns the old value
readReg-writeReg-a0-s0 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf a0 v) s0 ≡ readReg rf s0
readReg-writeReg-a0-s0 rf v = refl

-- | Reading sp after writing s0 returns the old value
readReg-writeReg-s0-sp : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf s0 v) sp ≡ readReg rf sp
readReg-writeReg-s0-sp rf v = refl

------------------------------------------------------------------------
-- Memory Lemmas
------------------------------------------------------------------------

open import Data.Nat.Properties using (+-comm; +-assoc; +-identityʳ; +-suc; m∸n+n≡m; m≤m+n; <-≤-trans; +-monoʳ-<)
open import Data.Nat using (z<s; s<s) -- _<_ already imported above

-- Memory read/write lemmas now imported from Once.Backend.Common.Memory:
--   readMem-writeMem-same, readMem-writeMem-diff, n≢n+suc

------------------------------------------------------------------------
-- Stack Address Disjointness Lemmas
--
-- For proving that stack writes at new-sp don't interfere with
-- memory at orig-sp and above. Key insight:
--   new-sp = orig-sp ∸ n (where n = 16 for inl/inr)
--   When n ≤ orig-sp and n > 0: new-sp < orig-sp ≤ orig-sp + k
--   Therefore new-sp ≢ orig-sp + k
------------------------------------------------------------------------

-- | Core lemma: (m ∸ n) + k ≢ m + j when n ≤ m, n > 0
-- This proves disjointness between write addresses (below orig-sp)
-- and preserved addresses (at or above orig-sp).
--
-- Case 1: new-sp ≢ orig-sp (k=0, j=0): (m ∸ n) ≢ m since n > 0
-- Case 2: new-sp + 8 ≢ orig-sp (k=8, j=0): (m ∸ n) + 8 ≢ m when n > 8
-- Case 3: new-sp ≢ orig-sp + 8 (k=0, j=8): (m ∸ n) ≢ m + 8
--
-- General form for the proofs we need:
-- Proof: (m ∸ n) + n = m, and n > 0, so (m ∸ n) < (m ∸ n) + n = m

-- Helper: m ∸ n ≤ m
m∸n≤m : ∀ (m n : ℕ) → m ∸ n ≤ m
m∸n≤m m zero = ≤-refl
  where open import Data.Nat.Properties using (≤-refl)
m∸n≤m zero (suc n) = Data.Nat.z≤n
m∸n≤m (suc m) (suc n) = m≤n⇒m≤1+n (m∸n≤m m n)
  where open import Data.Nat.Properties using (m≤n⇒m≤1+n)

monus-lt-plus : ∀ (n m : ℕ) → n ≤ m → 0 < n → (m ∸ n) < m
monus-lt-plus (suc n) zero () _
monus-lt-plus (suc n) (suc m) _ _ = s<s (m∸n≤m m n)

-- | When x < y, x ≢ y
<-to-≢ : ∀ {x y : ℕ} → x < y → x ≢ y
<-to-≢ (s<s p) refl = <-to-≢ p refl

-- | Core disjointness: (m ∸ n) ≢ m when n ≤ m and n > 0
monus-neq-self : ∀ (n m : ℕ) → n ≤ m → 0 < n → (m ∸ n) ≢ m
monus-neq-self n m n≤m 0<n = <-to-≢ (monus-lt-plus n m n≤m 0<n)

-- | (m ∸ n) ≢ m + k for any k when n ≤ m and n > 0
monus-neq-plus : ∀ (n m k : ℕ) → n ≤ m → 0 < n → (m ∸ n) ≢ (m +ℕ k)
monus-neq-plus n m k n≤m 0<n eq = <-to-≢ (<-≤-trans lt-m m≤m+k) eq
  where
    lt-m : (m ∸ n) < m
    lt-m = monus-lt-plus n m n≤m 0<n
    m≤m+k : m ≤ m +ℕ k
    m≤m+k = m≤m+n m k

-- | (m ∸ n) + offset ≢ m + k when n > offset (the common case for our proofs)
-- For inl/inr: n = 16, offset ∈ {0, 8}, k ∈ {0, 8, 16, 24}
-- We have: (orig-sp ∸ 16) + offset ≢ orig-sp + k
monus-plus-neq-plus : ∀ (n m offset k : ℕ) → n ≤ m → offset < n → ((m ∸ n) +ℕ offset) ≢ (m +ℕ k)
monus-plus-neq-plus n m offset k n≤m offset-lt-n eq = <-to-≢ goal eq
  where
    -- (m ∸ n) + offset < (m ∸ n) + n = m ≤ m + k
    -- First: (m ∸ n) + offset < m (since offset < n and (m ∸ n) + n = m)
    step1 : ((m ∸ n) +ℕ offset) < ((m ∸ n) +ℕ n)
    step1 = +-monoʳ-< (m ∸ n) offset-lt-n
    step2 : ((m ∸ n) +ℕ n) ≡ m
    step2 = m∸n+n≡m n≤m
    step3 : ((m ∸ n) +ℕ offset) < m
    step3 = subst (((m ∸ n) +ℕ offset) <_) step2 step1
    goal : ((m ∸ n) +ℕ offset) < (m +ℕ k)
    goal = <-≤-trans step3 (m≤m+n m k)

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

-- NOTE: Fuel-based lemmas (step-halted, exec-suc-halted, exec-N-if-halts, exec-mono)
-- were removed as dead code after the top-level API became fuel-free (Star-based).

------------------------------------------------------------------------
-- Instruction-level helpers (for E2E trace proofs)
------------------------------------------------------------------------
--
-- These helpers describe the exact behavior of key instructions.
-- They are essential for step-by-step trace proofs similar to X86.

-- | effectiveAddr with zero offset just reads the register
effectiveAddr-zero : ∀ (rf : RegFile) (r : Reg) →
  effectiveAddr rf r (+ 0) ≡ readReg rf r
effectiveAddr-zero rf r = +-identityʳ (readReg rf r)

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

-- | Helper: 0 << n ≡ 0 for any n
0-<<-n : ∀ n → 0 << n ≡ 0
0-<<-n zero = refl
0-<<-n (suc n) = 0-<<-n n  -- (0 + 0) << n = 0 << n = 0

-- | Helper: pc + 0 ≡ pc (uses +-identityʳ)
open import Data.Nat.Properties using (+-identityʳ)

-- | What execInstr does for auipc with imm=0
-- auipc rd (+ 0): rd = pc (since 0 << 12 = 0), pc = pc + 1
-- This is used in curry codegen to capture the current PC for code-ptr computation
execAuipc0 : ∀ (prog : Program) (s : State) (rd : Reg) →
  execInstr prog s (auipc rd (+ 0)) ≡
    just (record s { regs = writeReg (regs s) rd (pc s)
                   ; pc = pc s +ℕ 1 })
execAuipc0 prog s rd =
  -- result = pc s + (offsetToℕ (+ 0) << 12) = pc s + (0 << 12) = pc s + 0 = pc s
  cong (λ r → just (record s { regs = writeReg (regs s) rd r ; pc = pc s +ℕ 1 }))
       (trans (cong (pc s +ℕ_) (0-<<-n 12)) (+-identityʳ (pc s)))

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

-- | Reading s2 after writing sp returns the old value
readReg-writeReg-sp-s2 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf sp v) s2 ≡ readReg rf s2
readReg-writeReg-sp-s2 rf v = refl

-- | Reading s0 after writing s2 returns the old value
readReg-writeReg-s2-s0 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf s2 v) s0 ≡ readReg rf s0
readReg-writeReg-s2-s0 rf v = refl

-- | Reading ra after writing s2 returns the old value
readReg-writeReg-s2-ra : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf s2 v) ra ≡ readReg rf ra
readReg-writeReg-s2-ra rf v = refl

-- | Reading sp after writing t0 returns the old value
readReg-writeReg-t0-sp : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf t0 v) sp ≡ readReg rf sp
readReg-writeReg-t0-sp rf v = refl

-- | Reading a0 after writing t0 returns the old value
readReg-writeReg-t0-a0 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf t0 v) a0 ≡ readReg rf a0
readReg-writeReg-t0-a0 rf v = refl

-- | Reading s1 after writing t0 returns the old value
readReg-writeReg-t0-s1 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf t0 v) s1 ≡ readReg rf s1
readReg-writeReg-t0-s1 rf v = refl

-- | Reading s2 after writing t0 returns the old value
readReg-writeReg-t0-s2 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf t0 v) s2 ≡ readReg rf s2
readReg-writeReg-t0-s2 rf v = refl

-- | Reading s0 after writing t0 returns the old value
readReg-writeReg-t0-s0 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf t0 v) s0 ≡ readReg rf s0
readReg-writeReg-t0-s0 rf v = refl

-- | Reading ra after writing t0 returns the old value
readReg-writeReg-t0-ra : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf t0 v) ra ≡ readReg rf ra
readReg-writeReg-t0-ra rf v = refl

------------------------------------------------------------------------
-- Register preservation lemmas for t1 (apply proof)
------------------------------------------------------------------------

-- | Reading a0 after writing t1 returns the old value
readReg-writeReg-t1-a0 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf t1 v) a0 ≡ readReg rf a0
readReg-writeReg-t1-a0 rf v = refl

-- | Reading s1 after writing t1 returns the old value
readReg-writeReg-t1-s1 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf t1 v) s1 ≡ readReg rf s1
readReg-writeReg-t1-s1 rf v = refl

-- | Reading t1 after writing t2 returns the old value
readReg-writeReg-t2-t1 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf t2 v) t1 ≡ readReg rf t1
readReg-writeReg-t2-t1 rf v = refl

-- | Reading a0 after writing t2 returns the old value
readReg-writeReg-t2-a0 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf t2 v) a0 ≡ readReg rf a0
readReg-writeReg-t2-a0 rf v = refl

-- | Reading s1 after writing t2 returns the old value
readReg-writeReg-t2-s1 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf t2 v) s1 ≡ readReg rf s1
readReg-writeReg-t2-s1 rf v = refl

-- | Reading t1 after writing s0 returns the old value
readReg-writeReg-s0-t1 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf s0 v) t1 ≡ readReg rf t1
readReg-writeReg-s0-t1 rf v = refl

-- | Reading t2 after writing s0 returns the old value
readReg-writeReg-s0-t2 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf s0 v) t2 ≡ readReg rf t2
readReg-writeReg-s0-t2 rf v = refl

-- | Reading s1 after writing s0 returns the old value
readReg-writeReg-s0-s1 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf s0 v) s1 ≡ readReg rf s1
readReg-writeReg-s0-s1 rf v = refl

-- | Reading t1 after writing t0 returns the old value
readReg-writeReg-t0-t1 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf t0 v) t1 ≡ readReg rf t1
readReg-writeReg-t0-t1 rf v = refl

-- | Reading t2 after writing t0 returns the old value
readReg-writeReg-t0-t2 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf t0 v) t2 ≡ readReg rf t2
readReg-writeReg-t0-t2 rf v = refl

-- | Reading s0 after writing t1 returns the old value
readReg-writeReg-t1-s0 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf t1 v) s0 ≡ readReg rf s0
readReg-writeReg-t1-s0 rf v = refl

-- | Reading s0 after writing t2 returns the old value
readReg-writeReg-t2-s0 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf t2 v) s0 ≡ readReg rf s0
readReg-writeReg-t2-s0 rf v = refl

-- | Reading t2 after writing a0 returns the old value
readReg-writeReg-a0-t2 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf a0 v) t2 ≡ readReg rf t2
readReg-writeReg-a0-t2 rf v = refl

-- | Reading t0 after writing a0 returns the old value
readReg-writeReg-a0-t0 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf a0 v) t0 ≡ readReg rf t0
readReg-writeReg-a0-t0 rf v = refl

-- | Reading s0 after writing ra returns the old value
readReg-writeReg-ra-s0 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf ra v) s0 ≡ readReg rf s0
readReg-writeReg-ra-s0 rf v = refl

-- | Reading s1 after writing ra returns the old value
readReg-writeReg-ra-s1 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf ra v) s1 ≡ readReg rf s1
readReg-writeReg-ra-s1 rf v = refl

-- | Reading ra after writing t1 returns the old value
readReg-writeReg-t1-ra : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf t1 v) ra ≡ readReg rf ra
readReg-writeReg-t1-ra rf v = refl

-- | Reading ra after writing t2 returns the old value
readReg-writeReg-t2-ra : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf t2 v) ra ≡ readReg rf ra
readReg-writeReg-t2-ra rf v = refl

-- | Reading ra after writing s0 returns the old value
readReg-writeReg-s0-ra : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf s0 v) ra ≡ readReg rf ra
readReg-writeReg-s0-ra rf v = refl

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

-- | Step an auipc instruction with imm=0 at arbitrary offset
-- auipc rd (+ 0): rd = pc, pc = pc + 1
step-auipc0-at-offset : ∀ (prefix : Program) (rd : Reg) (suffix : Program) (s : State) →
  halted s ≡ false → pc s ≡ length prefix →
  step (prefix ++ auipc rd (+ 0) ∷ suffix) s ≡
    just (record s { regs = writeReg (regs s) rd (pc s)
                   ; pc = pc s +ℕ 1 })
step-auipc0-at-offset prefix rd suffix s h-false pc-eq =
  trans (step-at-offset prefix (auipc rd (+ 0)) suffix s h-false pc-eq)
        (execAuipc0 (prefix ++ auipc rd (+ 0) ∷ suffix) s rd)

-- | Step a j instruction at arbitrary offset
-- j offset: pc = pc + offset
step-j-at-offset : ∀ (prefix : Program) (offset : ℕ) (suffix : Program) (s : State) →
  halted s ≡ false → pc s ≡ length prefix →
  step (prefix ++ j (+ offset) ∷ suffix) s ≡
    just (record s { pc = pc s +ℕ offset })
step-j-at-offset prefix offset suffix s h-false pc-eq =
  trans (step-at-offset prefix (j (+ offset)) suffix s h-false pc-eq)
        (execJ (prefix ++ j (+ offset) ∷ suffix) s offset)

-- | Step a label instruction at arbitrary offset
-- label n: pc = pc + 1 (no-op)
step-label-at-offset : ∀ (prefix : Program) (n : ℕ) (suffix : Program) (s : State) →
  halted s ≡ false → pc s ≡ length prefix →
  step (prefix ++ label n ∷ suffix) s ≡
    just (record s { pc = pc s +ℕ 1 })
step-label-at-offset prefix n suffix s h-false pc-eq =
  trans (step-at-offset prefix (label n) suffix s h-false pc-eq)
        (execLabel (prefix ++ label n ∷ suffix) s n)

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

------------------------------------------------------------------------
-- Non-halting multi-step execution helpers
------------------------------------------------------------------------
--
-- These are analogous to X86's exec-n-steps-nonhalt helpers.
-- They chain together step proofs for sub-program execution where
-- we don't want to halt after each step.
--
-- Note: We use st1, st2, etc. to avoid conflict with register names s1, s2.

-- | Two-step non-halting execution: execute exactly 2 steps without halting
exec-two-steps-nonhalt : ∀ (prog : List Instr) (s st1 st2 : State) →
  step prog s ≡ just st1 → halted st1 ≡ false →
  step prog st1 ≡ just st2 → halted st2 ≡ false →
  exec 2 prog s ≡ just st2
exec-two-steps-nonhalt prog s st1 st2 step1 h1 step2 h2 =
  trans (exec-step-continue 1 prog s st1 step1 h1)
        (exec-one-step-nonhalt prog st1 st2 step2 h2)

-- | Three-step non-halting execution
exec-three-steps-nonhalt : ∀ (prog : List Instr) (s st1 st2 st3 : State) →
  step prog s ≡ just st1 → halted st1 ≡ false →
  step prog st1 ≡ just st2 → halted st2 ≡ false →
  step prog st2 ≡ just st3 → halted st3 ≡ false →
  exec 3 prog s ≡ just st3
exec-three-steps-nonhalt prog s st1 st2 st3 step1 h1 step2 h2 step3 h3 =
  trans (exec-step-continue 2 prog s st1 step1 h1)
        (exec-two-steps-nonhalt prog st1 st2 st3 step2 h2 step3 h3)

-- | Four-step non-halting execution
exec-four-steps-nonhalt : ∀ (prog : List Instr) (s st1 st2 st3 st4 : State) →
  step prog s ≡ just st1 → halted st1 ≡ false →
  step prog st1 ≡ just st2 → halted st2 ≡ false →
  step prog st2 ≡ just st3 → halted st3 ≡ false →
  step prog st3 ≡ just st4 → halted st4 ≡ false →
  exec 4 prog s ≡ just st4
exec-four-steps-nonhalt prog s st1 st2 st3 st4 step1 h1 step2 h2 step3 h3 step4 h4 =
  trans (exec-step-continue 3 prog s st1 step1 h1)
        (exec-three-steps-nonhalt prog st1 st2 st3 st4 step2 h2 step3 h3 step4 h4)

-- | Five-step non-halting execution
exec-five-steps-nonhalt : ∀ (prog : List Instr) (s st1 st2 st3 st4 st5 : State) →
  step prog s ≡ just st1 → halted st1 ≡ false →
  step prog st1 ≡ just st2 → halted st2 ≡ false →
  step prog st2 ≡ just st3 → halted st3 ≡ false →
  step prog st3 ≡ just st4 → halted st4 ≡ false →
  step prog st4 ≡ just st5 → halted st5 ≡ false →
  exec 5 prog s ≡ just st5
exec-five-steps-nonhalt prog s st1 st2 st3 st4 st5 step1 h1 step2 h2 step3 h3 step4 h4 step5 h5 =
  trans (exec-step-continue 4 prog s st1 step1 h1)
        (exec-four-steps-nonhalt prog st1 st2 st3 st4 st5 step2 h2 step3 h3 step4 h4 step5 h5)

-- | Six-step non-halting execution
exec-six-steps-nonhalt : ∀ (prog : List Instr) (s st1 st2 st3 st4 st5 st6 : State) →
  step prog s ≡ just st1 → halted st1 ≡ false →
  step prog st1 ≡ just st2 → halted st2 ≡ false →
  step prog st2 ≡ just st3 → halted st3 ≡ false →
  step prog st3 ≡ just st4 → halted st4 ≡ false →
  step prog st4 ≡ just st5 → halted st5 ≡ false →
  step prog st5 ≡ just st6 → halted st6 ≡ false →
  exec 6 prog s ≡ just st6
exec-six-steps-nonhalt prog s st1 st2 st3 st4 st5 st6 step1 h1 step2 h2 step3 h3 step4 h4 step5 h5 step6 h6 =
  trans (exec-step-continue 5 prog s st1 step1 h1)
        (exec-five-steps-nonhalt prog st1 st2 st3 st4 st5 st6 step2 h2 step3 h3 step4 h4 step5 h5 step6 h6)
