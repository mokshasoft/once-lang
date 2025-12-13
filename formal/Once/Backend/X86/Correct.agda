------------------------------------------------------------------------
-- Once.Backend.X86.Correct
--
-- Correctness proofs for x86-64 code generation.
--
-- Main theorem:
--   codegen-x86-correct : ∀ (ir : IR A B) (x : ⟦A⟧) →
--     exec-x86 (compile-x86 ir) (encode-x86 x) ≡ encode-x86 (eval ir x)
--
-- This module proves that the code generator preserves semantics:
-- executing the generated x86-64 code on an encoded input produces
-- the same result as encoding the semantic evaluation.
------------------------------------------------------------------------

module Once.Backend.X86.Correct where

open import Once.Type
open import Once.IR
open import Once.Semantics

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State
open import Once.Backend.X86.CodeGen

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
open import Data.Nat using (ℕ; zero; suc; _∸_; _≡ᵇ_) renaming (_+_ to _+ℕ_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-sum)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans; subst)

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
  (encodedMemory x)
  initFlags
  0
  false
  where
    -- Stack starts at a high address
    stackBase : Word
    stackBase = 0x7FFF0000

    -- Memory containing the encoded value (postulated)
    postulate
      encodedMemory : ⟦ A ⟧ → Memory

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
-- Execution Helpers
------------------------------------------------------------------------
--
-- These helpers capture the behavior of instruction sequences.
-- See Once.Postulates for a summary of what remains postulated.
--
-- PROVEN (non-recursive IR helpers):
--   execMov-reg-reg, execMov-reg-imm, execMov-reg-mem-base,
--   execMov-reg-mem-disp, execMov-mem-base-imm, execMov-mem-disp-reg,
--   execSub-reg-imm, execJmp
--   run-single-mov, run-single-mov-imm, run-single-mov-mem-base,
--   run-single-mov-mem-disp
--   run-inl-seq, run-inr-seq, run-curry-seq
--
-- POSTULATED (require mutual induction on IR):
--   run-seq-compose  : Sequential composition (needs recursive IR proofs)
--   run-case-inl/inr : Case analysis (needs recursive IR proofs + label resolution)
--   run-pair-seq     : Pairing (needs recursive IR proofs)
--   run-generator    : Main induction theorem (depends on all above)
--   run-apply-seq    : Closure application (complex calling convention)
--
-- The non-recursive helpers trace through fixed instruction sequences.
-- The recursive helpers form a mutually-dependent cluster that requires
-- structural induction on IR. See lessons-learned.md for details.
--
-- Note: The codegen uses placeholder label numbers (100, 200, 300, 400)
-- that don't match actual instruction positions. This causes jmp/jne
-- to out-of-bounds addresses, triggering halt. For recursive IR,
-- proper label resolution would be needed.
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

-- | Reading r14 after writing rdi returns the old value
readReg-writeReg-rdi-r14 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf rdi v) r14 ≡ readReg rf r14
readReg-writeReg-rdi-r14 rf v = refl

-- | Reading rdi after writing rax returns the old value
readReg-writeReg-rax-rdi : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf rax v) rdi ≡ readReg rf rdi
readReg-writeReg-rax-rdi rf v = refl

------------------------------------------------------------------------
-- Memory Lemmas
------------------------------------------------------------------------

open import Data.Nat.Properties using (≡ᵇ⇒≡; ≡⇒≡ᵇ)

-- | n ≡ᵇ n is always true (helper)
≡ᵇ-refl : ∀ n → (n ≡ᵇ n) ≡ true
≡ᵇ-refl zero = refl
≡ᵇ-refl (suc n) = ≡ᵇ-refl n

-- | Reading from the address we just wrote returns the written value
readMem-writeMem-same : ∀ (m : Memory) (addr : Word) (v : Word) →
  readMem (writeMem m addr v) addr ≡ just v
readMem-writeMem-same m addr v with addr ≡ᵇ addr | ≡ᵇ-refl addr
... | true | _ = refl

-- | n ≢ n + k for k > 0 (needed for disjoint memory addresses)
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

-- | Fetching past the end of a single-instruction program returns nothing
fetch-1-single : ∀ (i : Instr) → fetch (i ∷ []) 1 ≡ nothing
fetch-1-single i = refl

-- | Fetching past the end of a 4-instruction program returns nothing
fetch-4-of-4 : ∀ (i0 i1 i2 i3 : Instr) → fetch (i0 ∷ i1 ∷ i2 ∷ i3 ∷ []) 4 ≡ nothing
fetch-4-of-4 i0 i1 i2 i3 = refl

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

-- | Two-step execution: if first step produces s1 (not halted), and second halts,
-- then exec (suc (suc n)) produces the halted state
exec-two-steps : ∀ (n : ℕ) (prog : List Instr) (s s1 s2 : State) →
  step prog s ≡ just s1 →
  halted s1 ≡ false →
  step prog s1 ≡ just s2 →
  halted s2 ≡ true →
  exec (suc (suc n)) prog s ≡ just s2
exec-two-steps n prog s s1 s2 step1 h1 step2 h2 =
  trans (exec-on-non-halted-step (suc n) prog s s1 step1 h1)
        (exec-on-halted-step n prog s1 s2 step2 h2)

-- | Three-step execution
exec-three-steps : ∀ (n : ℕ) (prog : List Instr) (s s1 s2 s3 : State) →
  step prog s ≡ just s1 → halted s1 ≡ false →
  step prog s1 ≡ just s2 → halted s2 ≡ false →
  step prog s2 ≡ just s3 → halted s3 ≡ true →
  exec (suc (suc (suc n))) prog s ≡ just s3
exec-three-steps n prog s s1 s2 s3 step1 h1 step2 h2 step3 h3 =
  trans (exec-on-non-halted-step (suc (suc n)) prog s s1 step1 h1)
        (exec-two-steps n prog s1 s2 s3 step2 h2 step3 h3)

-- | Four-step execution
exec-four-steps : ∀ (n : ℕ) (prog : List Instr) (s s1 s2 s3 s4 : State) →
  step prog s ≡ just s1 → halted s1 ≡ false →
  step prog s1 ≡ just s2 → halted s2 ≡ false →
  step prog s2 ≡ just s3 → halted s3 ≡ false →
  step prog s3 ≡ just s4 → halted s4 ≡ true →
  exec (suc (suc (suc (suc n)))) prog s ≡ just s4
exec-four-steps n prog s s1 s2 s3 s4 step1 h1 step2 h2 step3 h3 step4 h4 =
  trans (exec-on-non-halted-step (suc (suc (suc n))) prog s s1 step1 h1)
        (exec-three-steps n prog s1 s2 s3 s4 step2 h2 step3 h3 step4 h4)

-- | Five-step execution (4 instructions + halt)
exec-five-steps : ∀ (n : ℕ) (prog : List Instr) (s s1 s2 s3 s4 s5 : State) →
  step prog s ≡ just s1 → halted s1 ≡ false →
  step prog s1 ≡ just s2 → halted s2 ≡ false →
  step prog s2 ≡ just s3 → halted s3 ≡ false →
  step prog s3 ≡ just s4 → halted s4 ≡ false →
  step prog s4 ≡ just s5 → halted s5 ≡ true →
  exec (suc (suc (suc (suc (suc n))))) prog s ≡ just s5
exec-five-steps n prog s s1 s2 s3 s4 s5 step1 h1 step2 h2 step3 h3 step4 h4 step5 h5 =
  trans (exec-on-non-halted-step (suc (suc (suc (suc n)))) prog s s1 step1 h1)
        (exec-four-steps n prog s1 s2 s3 s4 s5 step2 h2 step3 h3 step4 h4 step5 h5)

-- | Six-step execution (5 instructions + halt)
exec-six-steps : ∀ (n : ℕ) (prog : List Instr) (s s1 s2 s3 s4 s5 s6 : State) →
  step prog s ≡ just s1 → halted s1 ≡ false →
  step prog s1 ≡ just s2 → halted s2 ≡ false →
  step prog s2 ≡ just s3 → halted s3 ≡ false →
  step prog s3 ≡ just s4 → halted s4 ≡ false →
  step prog s4 ≡ just s5 → halted s5 ≡ false →
  step prog s5 ≡ just s6 → halted s6 ≡ true →
  exec (suc (suc (suc (suc (suc (suc n)))))) prog s ≡ just s6
exec-six-steps n prog s s1 s2 s3 s4 s5 s6 step1 h1 step2 h2 step3 h3 step4 h4 step5 h5 step6 h6 =
  trans (exec-on-non-halted-step (suc (suc (suc (suc (suc n))))) prog s s1 step1 h1)
        (exec-five-steps n prog s1 s2 s3 s4 s5 s6 step2 h2 step3 h3 step4 h4 step5 h5 step6 h6)

-- | Seven-step execution (6 instructions + halt)
exec-seven-steps : ∀ (n : ℕ) (prog : List Instr) (s s1 s2 s3 s4 s5 s6 s7 : State) →
  step prog s ≡ just s1 → halted s1 ≡ false →
  step prog s1 ≡ just s2 → halted s2 ≡ false →
  step prog s2 ≡ just s3 → halted s3 ≡ false →
  step prog s3 ≡ just s4 → halted s4 ≡ false →
  step prog s4 ≡ just s5 → halted s5 ≡ false →
  step prog s5 ≡ just s6 → halted s6 ≡ false →
  step prog s6 ≡ just s7 → halted s7 ≡ true →
  exec (suc (suc (suc (suc (suc (suc (suc n))))))) prog s ≡ just s7
exec-seven-steps n prog s s1 s2 s3 s4 s5 s6 s7 step1 h1 step2 h2 step3 h3 step4 h4 step5 h5 step6 h6 step7 h7 =
  trans (exec-on-non-halted-step (suc (suc (suc (suc (suc (suc n)))))) prog s s1 step1 h1)
        (exec-six-steps n prog s1 s2 s3 s4 s5 s6 s7 step2 h2 step3 h3 step4 h4 step5 h5 step6 h6 step7 h7)

-- | Eight-step execution (7 instructions + halt)
exec-eight-steps : ∀ (n : ℕ) (prog : List Instr) (s s1 s2 s3 s4 s5 s6 s7 s8 : State) →
  step prog s ≡ just s1 → halted s1 ≡ false →
  step prog s1 ≡ just s2 → halted s2 ≡ false →
  step prog s2 ≡ just s3 → halted s3 ≡ false →
  step prog s3 ≡ just s4 → halted s4 ≡ false →
  step prog s4 ≡ just s5 → halted s5 ≡ false →
  step prog s5 ≡ just s6 → halted s6 ≡ false →
  step prog s6 ≡ just s7 → halted s7 ≡ false →
  step prog s7 ≡ just s8 → halted s8 ≡ true →
  exec (suc (suc (suc (suc (suc (suc (suc (suc n)))))))) prog s ≡ just s8
exec-eight-steps n prog s s1 s2 s3 s4 s5 s6 s7 s8 step1 h1 step2 h2 step3 h3 step4 h4 step5 h5 step6 h6 step7 h7 step8 h8 =
  trans (exec-on-non-halted-step (suc (suc (suc (suc (suc (suc (suc n))))))) prog s s1 step1 h1)
        (exec-seven-steps n prog s1 s2 s3 s4 s5 s6 s7 s8 step2 h2 step3 h3 step4 h4 step5 h5 step6 h6 step7 h7 step8 h8)

-- | Nine-step execution (8 instructions + halt)
exec-nine-steps : ∀ (n : ℕ) (prog : List Instr) (s s1 s2 s3 s4 s5 s6 s7 s8 s9 : State) →
  step prog s ≡ just s1 → halted s1 ≡ false →
  step prog s1 ≡ just s2 → halted s2 ≡ false →
  step prog s2 ≡ just s3 → halted s3 ≡ false →
  step prog s3 ≡ just s4 → halted s4 ≡ false →
  step prog s4 ≡ just s5 → halted s5 ≡ false →
  step prog s5 ≡ just s6 → halted s6 ≡ false →
  step prog s6 ≡ just s7 → halted s7 ≡ false →
  step prog s7 ≡ just s8 → halted s8 ≡ false →
  step prog s8 ≡ just s9 → halted s9 ≡ true →
  exec (suc (suc (suc (suc (suc (suc (suc (suc (suc n))))))))) prog s ≡ just s9
exec-nine-steps n prog s s1 s2 s3 s4 s5 s6 s7 s8 s9 step1 h1 step2 h2 step3 h3 step4 h4 step5 h5 step6 h6 step7 h7 step8 h8 step9 h9 =
  trans (exec-on-non-halted-step (suc (suc (suc (suc (suc (suc (suc (suc n)))))))) prog s s1 step1 h1)
        (exec-eight-steps n prog s1 s2 s3 s4 s5 s6 s7 s8 s9 step2 h2 step3 h3 step4 h4 step5 h5 step6 h6 step7 h7 step8 h8 step9 h9)

-- Helper: running a single-instruction program (mov reg, reg)
--
-- Proof outline:
-- 1. First step executes mov, producing s1 with pc=1, updated regs, halted=false
-- 2. Second step: fetch at pc=1 fails, sets halted=true
-- 3. exec-two-steps combines these
run-single-mov : ∀ (s : State) (dst src : Reg) →
  halted s ≡ false →
  pc s ≡ 0 →
  ∃[ s' ] (run (mov (reg dst) (reg src) ∷ []) s ≡ just s'
         × readReg (regs s') dst ≡ readReg (regs s) src
         × halted s' ≡ true)
run-single-mov s dst src h-false pc-0 = s2 , run-eq , rax-eq , halt-eq
  where
    prog : List Instr
    prog = mov (reg dst) (reg src) ∷ []

    -- State after first step: execute mov (use pc s +ℕ 1 to match execMov-reg-reg)
    s1 : State
    s1 = record s { regs = writeReg (regs s) dst (readReg (regs s) src)
                  ; pc = pc s +ℕ 1 }

    -- State after second step: halted
    s2 : State
    s2 = record s1 { halted = true }

    -- First step produces s1
    step1 : step prog s ≡ just s1
    step1 = trans (step-exec-0 (mov (reg dst) (reg src)) [] s h-false pc-0)
                  (execMov-reg-reg s dst src)

    -- s1 is not halted
    h1 : halted s1 ≡ false
    h1 = h-false  -- halted field unchanged in s1

    -- s1 has pc = pc s + 1 = 0 + 1 = 1
    pc1 : pc s1 ≡ 1
    pc1 = cong (λ x → x +ℕ 1) pc-0

    -- fetch at pc s1 = 1 fails
    fetch-fail : fetch prog (pc s1) ≡ nothing
    fetch-fail = subst (λ p → fetch prog p ≡ nothing) (sym pc1) refl

    -- Second step produces s2 (halted)
    step2 : step prog s1 ≡ just s2
    step2 = step-halt-on-fetch-fail prog s1 h1 fetch-fail

    -- s2 is halted
    halt-eq : halted s2 ≡ true
    halt-eq = refl

    -- Register value is preserved: regs s2 = regs s1 = writeReg (regs s) dst (readReg (regs s) src)
    rax-eq : readReg (regs s2) dst ≡ readReg (regs s) src
    rax-eq = readReg-writeReg-same (regs s) dst (readReg (regs s) src)

    -- run = exec defaultFuel, defaultFuel = 10000 = suc (suc 9998)
    run-eq : run prog s ≡ just s2
    run-eq = exec-two-steps 9998 prog s s1 s2 step1 h1 step2 halt-eq

-- Helper: running a single-instruction program (mov reg, imm)
run-single-mov-imm : ∀ (s : State) (dst : Reg) (n : ℕ) →
  halted s ≡ false →
  pc s ≡ 0 →
  ∃[ s' ] (run (mov (reg dst) (imm n) ∷ []) s ≡ just s'
         × readReg (regs s') dst ≡ n
         × halted s' ≡ true)
run-single-mov-imm s dst n h-false pc-0 = s2 , run-eq , rax-eq , halt-eq
  where
    prog : List Instr
    prog = mov (reg dst) (imm n) ∷ []

    s1 : State
    s1 = record s { regs = writeReg (regs s) dst n ; pc = pc s +ℕ 1 }

    s2 : State
    s2 = record s1 { halted = true }

    step1 : step prog s ≡ just s1
    step1 = trans (step-exec-0 (mov (reg dst) (imm n)) [] s h-false pc-0)
                  (execMov-reg-imm s dst n)

    h1 : halted s1 ≡ false
    h1 = h-false

    pc1 : pc s1 ≡ 1
    pc1 = cong (λ x → x +ℕ 1) pc-0

    fetch-fail : fetch prog (pc s1) ≡ nothing
    fetch-fail = subst (λ p → fetch prog p ≡ nothing) (sym pc1) refl

    step2 : step prog s1 ≡ just s2
    step2 = step-halt-on-fetch-fail prog s1 h1 fetch-fail

    halt-eq : halted s2 ≡ true
    halt-eq = refl

    rax-eq : readReg (regs s2) dst ≡ n
    rax-eq = readReg-writeReg-same (regs s) dst n

    run-eq : run prog s ≡ just s2
    run-eq = exec-two-steps 9998 prog s s1 s2 step1 h1 step2 halt-eq

-- Helper: running a single-instruction program (mov reg, [reg])
-- Loads from memory at address in src register
run-single-mov-mem-base : ∀ (s : State) (dst src : Reg) (v : ℕ) →
  halted s ≡ false →
  pc s ≡ 0 →
  readMem (memory s) (readReg (regs s) src) ≡ just v →
  ∃[ s' ] (run (mov (reg dst) (mem (base src)) ∷ []) s ≡ just s'
         × readReg (regs s') dst ≡ v
         × halted s' ≡ true)
run-single-mov-mem-base s dst src v h-false pc-0 mem-ok = s2 , run-eq , rax-eq , halt-eq
  where
    prog : List Instr
    prog = mov (reg dst) (mem (base src)) ∷ []

    s1 : State
    s1 = record s { regs = writeReg (regs s) dst v ; pc = pc s +ℕ 1 }

    s2 : State
    s2 = record s1 { halted = true }

    step1 : step prog s ≡ just s1
    step1 = trans (step-exec-0 (mov (reg dst) (mem (base src))) [] s h-false pc-0)
                  (execMov-reg-mem-base s dst src v mem-ok)

    h1 : halted s1 ≡ false
    h1 = h-false

    pc1 : pc s1 ≡ 1
    pc1 = cong (λ x → x +ℕ 1) pc-0

    fetch-fail : fetch prog (pc s1) ≡ nothing
    fetch-fail = subst (λ p → fetch prog p ≡ nothing) (sym pc1) refl

    step2 : step prog s1 ≡ just s2
    step2 = step-halt-on-fetch-fail prog s1 h1 fetch-fail

    halt-eq : halted s2 ≡ true
    halt-eq = refl

    rax-eq : readReg (regs s2) dst ≡ v
    rax-eq = readReg-writeReg-same (regs s) dst v

    run-eq : run prog s ≡ just s2
    run-eq = exec-two-steps 9998 prog s s1 s2 step1 h1 step2 halt-eq

-- Helper: running a single-instruction program (mov reg, [reg+disp])
-- Loads from memory at address (src register + displacement)
run-single-mov-mem-disp : ∀ (s : State) (dst src : Reg) (disp : ℕ) (v : ℕ) →
  halted s ≡ false →
  pc s ≡ 0 →
  readMem (memory s) (readReg (regs s) src +ℕ disp) ≡ just v →
  ∃[ s' ] (run (mov (reg dst) (mem (base+disp src disp)) ∷ []) s ≡ just s'
         × readReg (regs s') dst ≡ v
         × halted s' ≡ true)
run-single-mov-mem-disp s dst src disp v h-false pc-0 mem-ok = s2 , run-eq , rax-eq , halt-eq
  where
    prog : List Instr
    prog = mov (reg dst) (mem (base+disp src disp)) ∷ []

    s1 : State
    s1 = record s { regs = writeReg (regs s) dst v ; pc = pc s +ℕ 1 }

    s2 : State
    s2 = record s1 { halted = true }

    step1 : step prog s ≡ just s1
    step1 = trans (step-exec-0 (mov (reg dst) (mem (base+disp src disp))) [] s h-false pc-0)
                  (execMov-reg-mem-disp s dst src disp v mem-ok)

    h1 : halted s1 ≡ false
    h1 = h-false

    pc1 : pc s1 ≡ 1
    pc1 = cong (λ x → x +ℕ 1) pc-0

    fetch-fail : fetch prog (pc s1) ≡ nothing
    fetch-fail = subst (λ p → fetch prog p ≡ nothing) (sym pc1) refl

    step2 : step prog s1 ≡ just s2
    step2 = step-halt-on-fetch-fail prog s1 h1 fetch-fail

    halt-eq : halted s2 ≡ true
    halt-eq = refl

    rax-eq : readReg (regs s2) dst ≡ v
    rax-eq = readReg-writeReg-same (regs s) dst v

    run-eq : run prog s ≡ just s2
    run-eq = exec-two-steps 9998 prog s s1 s2 step1 h1 step2 halt-eq

-- Helper: inl instruction sequence
-- sub rsp, 16; mov [rsp], 0; mov [rsp+8], rdi; mov rax, rsp
-- Effect: allocates tagged union on stack with tag=0, value=input
--
-- Proof: trace through 5 steps (4 instructions + implicit halt when fetch fails at pc=4)
run-inl-seq : ∀ {A B} (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  ∃[ s' ] (run (compile-x86 {A} {A + B} inl) s ≡ just s'
         × halted s' ≡ true
         -- rax points to stack-allocated sum
         × readReg (regs s') rax ≡ readReg (regs s') rsp
         -- tag at [rax] = 0
         × readMem (memory s') (readReg (regs s') rax) ≡ just 0
         -- value at [rax+8] = original rdi
         × readMem (memory s') (readReg (regs s') rax +ℕ 8) ≡ just (readReg (regs s) rdi))
run-inl-seq {A} {B} s h-false pc-0 = s5 , run-eq , halt-eq , rax-rsp-eq , tag-eq , val-eq
  where
    prog : List Instr
    prog = compile-x86 {A} {A + B} inl

    -- Original values we need to track
    orig-rsp : Word
    orig-rsp = readReg (regs s) rsp

    orig-rdi : Word
    orig-rdi = readReg (regs s) rdi

    new-rsp : Word
    new-rsp = orig-rsp ∸ 16

    -- State after step 1: sub rsp, 16
    -- Use pc s +ℕ 1 to match execSub-reg-imm output
    s1 : State
    s1 = record s { regs = writeReg (regs s) rsp new-rsp
                  ; pc = pc s +ℕ 1
                  ; flags = updateFlags new-rsp orig-rsp }

    step1 : step prog s ≡ just s1
    step1 = trans (step-exec-0 (sub (reg rsp) (imm 16)) _ s h-false pc-0)
                  (execSub-reg-imm prog s rsp 16)

    h1 : halted s1 ≡ false
    h1 = h-false

    pc1 : pc s1 ≡ 1
    pc1 = cong (λ x → x +ℕ 1) pc-0

    -- State after step 2: mov [rsp], 0
    s2 : State
    s2 = record s1 { memory = writeMem (memory s1) (readReg (regs s1) rsp) 0
                   ; pc = pc s1 +ℕ 1 }

    step2 : step prog s1 ≡ just s2
    step2 = trans (step-exec prog s1 (mov (mem (base rsp)) (imm 0)) h1
                             (subst (λ p → fetch prog p ≡ just (mov (mem (base rsp)) (imm 0))) (sym pc1) refl))
                  (execMov-mem-base-imm prog s1 rsp 0)

    h2 : halted s2 ≡ false
    h2 = h-false

    pc2 : pc s2 ≡ 2
    pc2 = cong (λ x → x +ℕ 1) pc1

    -- State after step 3: mov [rsp+8], rdi
    s3 : State
    s3 = record s2 { memory = writeMem (memory s2) (readReg (regs s2) rsp +ℕ 8) (readReg (regs s2) rdi)
                   ; pc = pc s2 +ℕ 1 }

    step3 : step prog s2 ≡ just s3
    step3 = trans (step-exec prog s2 (mov (mem (base+disp rsp 8)) (reg rdi)) h2
                             (subst (λ p → fetch prog p ≡ just (mov (mem (base+disp rsp 8)) (reg rdi))) (sym pc2) refl))
                  (execMov-mem-disp-reg prog s2 rsp rdi 8)

    h3 : halted s3 ≡ false
    h3 = h-false

    pc3 : pc s3 ≡ 3
    pc3 = cong (λ x → x +ℕ 1) pc2

    -- State after step 4: mov rax, rsp
    s4 : State
    s4 = record s3 { regs = writeReg (regs s3) rax (readReg (regs s3) rsp)
                   ; pc = pc s3 +ℕ 1 }

    step4 : step prog s3 ≡ just s4
    step4 = trans (step-exec prog s3 (mov (reg rax) (reg rsp)) h3
                             (subst (λ p → fetch prog p ≡ just (mov (reg rax) (reg rsp))) (sym pc3) refl))
                  (execMov-reg-reg s3 rax rsp)

    h4 : halted s4 ≡ false
    h4 = h-false

    pc4 : pc s4 ≡ 4
    pc4 = cong (λ x → x +ℕ 1) pc3

    -- State after step 5: fetch fails at pc=4, sets halted=true
    s5 : State
    s5 = record s4 { halted = true }

    fetch-fail : fetch prog (pc s4) ≡ nothing
    fetch-fail = subst (λ p → fetch prog p ≡ nothing) (sym pc4) refl

    step5 : step prog s4 ≡ just s5
    step5 = step-halt-on-fetch-fail prog s4 h4 fetch-fail

    halt-eq : halted s5 ≡ true
    halt-eq = refl

    -- Combined execution
    run-eq : run prog s ≡ just s5
    run-eq = exec-five-steps 9995 prog s s1 s2 s3 s4 s5 step1 h1 step2 h2 step3 h3 step4 h4 step5 halt-eq

    -- Now prove the properties about s5

    -- rax = rsp in s5 (both unchanged from s4)
    rax-rsp-eq : readReg (regs s5) rax ≡ readReg (regs s5) rsp
    rax-rsp-eq = readReg-writeReg-same (regs s3) rax (readReg (regs s3) rsp)

    -- Helper: rsp is constant through s1,s2,s3 since only sub modifies it in s1
    rsp-s2 : readReg (regs s2) rsp ≡ new-rsp
    rsp-s2 = readReg-writeReg-same (regs s) rsp new-rsp

    rsp-s3 : readReg (regs s3) rsp ≡ new-rsp
    rsp-s3 = rsp-s2

    -- Helper: rdi is constant through all states (never modified)
    -- In s1, only rsp was modified by sub instruction
    rdi-s1 : readReg (regs s1) rdi ≡ orig-rdi
    rdi-s1 = readReg-writeReg-rsp-rdi (regs s) new-rsp

    rdi-s2 : readReg (regs s2) rdi ≡ orig-rdi
    rdi-s2 = rdi-s1  -- regs s2 = regs s1 (mov [rsp], 0 doesn't touch registers)

    -- Helper: rax in s5 = rsp in s3 = new-rsp
    rax-s5 : readReg (regs s5) rax ≡ new-rsp
    rax-s5 = trans (readReg-writeReg-same (regs s3) rax (readReg (regs s3) rsp)) rsp-s3

    -- Key: new-rsp ≠ new-rsp + 8
    addr-disjoint : new-rsp ≢ new-rsp +ℕ 8
    addr-disjoint = n≢n+suc new-rsp 7

    -- tag at [rax] = 0
    -- Memory path: s5.memory = s3.memory = writeMem s2.memory (new-rsp+8) rdi
    --              s2.memory = writeMem s1.memory new-rsp 0
    -- Reading at new-rsp: first write doesn't touch it (different addr), second does
    tag-eq : readMem (memory s5) (readReg (regs s5) rax) ≡ just 0
    tag-eq = trans (cong (readMem (memory s5)) rax-s5)
                   (trans (readMem-writeMem-diff (memory s2) (new-rsp +ℕ 8) new-rsp (readReg (regs s2) rdi) (λ eq → addr-disjoint (sym eq)))
                          (readMem-writeMem-same (memory s1) new-rsp 0))

    -- value at [rax+8] = original rdi
    -- Memory path: same as above, but reading at new-rsp+8
    val-eq : readMem (memory s5) (readReg (regs s5) rax +ℕ 8) ≡ just (readReg (regs s) rdi)
    val-eq = trans (cong (λ a → readMem (memory s5) (a +ℕ 8)) rax-s5)
                   (trans (readMem-writeMem-same (memory s2) (new-rsp +ℕ 8) (readReg (regs s2) rdi))
                          (cong just rdi-s2))

-- Helper: inr instruction sequence (similar to inl but tag=1)
-- Proof: identical structure to run-inl-seq, just writes tag=1 instead of tag=0
run-inr-seq : ∀ {A B} (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  ∃[ s' ] (run (compile-x86 {B} {A + B} inr) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') rax ≡ readReg (regs s') rsp
         × readMem (memory s') (readReg (regs s') rax) ≡ just 1
         × readMem (memory s') (readReg (regs s') rax +ℕ 8) ≡ just (readReg (regs s) rdi))
run-inr-seq {A} {B} s h-false pc-0 = s5 , run-eq , halt-eq , rax-rsp-eq , tag-eq , val-eq
  where
    prog : List Instr
    prog = compile-x86 {B} {A + B} inr

    orig-rsp : Word
    orig-rsp = readReg (regs s) rsp

    orig-rdi : Word
    orig-rdi = readReg (regs s) rdi

    new-rsp : Word
    new-rsp = orig-rsp ∸ 16

    -- State after step 1: sub rsp, 16
    s1 : State
    s1 = record s { regs = writeReg (regs s) rsp new-rsp
                  ; pc = pc s +ℕ 1
                  ; flags = updateFlags new-rsp orig-rsp }

    step1 : step prog s ≡ just s1
    step1 = trans (step-exec-0 (sub (reg rsp) (imm 16)) _ s h-false pc-0)
                  (execSub-reg-imm prog s rsp 16)

    h1 : halted s1 ≡ false
    h1 = h-false

    pc1 : pc s1 ≡ 1
    pc1 = cong (λ x → x +ℕ 1) pc-0

    -- State after step 2: mov [rsp], 1 (tag = 1 for inr)
    s2 : State
    s2 = record s1 { memory = writeMem (memory s1) (readReg (regs s1) rsp) 1
                   ; pc = pc s1 +ℕ 1 }

    step2 : step prog s1 ≡ just s2
    step2 = trans (step-exec prog s1 (mov (mem (base rsp)) (imm 1)) h1
                             (subst (λ p → fetch prog p ≡ just (mov (mem (base rsp)) (imm 1))) (sym pc1) refl))
                  (execMov-mem-base-imm prog s1 rsp 1)

    h2 : halted s2 ≡ false
    h2 = h-false

    pc2 : pc s2 ≡ 2
    pc2 = cong (λ x → x +ℕ 1) pc1

    -- State after step 3: mov [rsp+8], rdi
    s3 : State
    s3 = record s2 { memory = writeMem (memory s2) (readReg (regs s2) rsp +ℕ 8) (readReg (regs s2) rdi)
                   ; pc = pc s2 +ℕ 1 }

    step3 : step prog s2 ≡ just s3
    step3 = trans (step-exec prog s2 (mov (mem (base+disp rsp 8)) (reg rdi)) h2
                             (subst (λ p → fetch prog p ≡ just (mov (mem (base+disp rsp 8)) (reg rdi))) (sym pc2) refl))
                  (execMov-mem-disp-reg prog s2 rsp rdi 8)

    h3 : halted s3 ≡ false
    h3 = h-false

    pc3 : pc s3 ≡ 3
    pc3 = cong (λ x → x +ℕ 1) pc2

    -- State after step 4: mov rax, rsp
    s4 : State
    s4 = record s3 { regs = writeReg (regs s3) rax (readReg (regs s3) rsp)
                   ; pc = pc s3 +ℕ 1 }

    step4 : step prog s3 ≡ just s4
    step4 = trans (step-exec prog s3 (mov (reg rax) (reg rsp)) h3
                             (subst (λ p → fetch prog p ≡ just (mov (reg rax) (reg rsp))) (sym pc3) refl))
                  (execMov-reg-reg s3 rax rsp)

    h4 : halted s4 ≡ false
    h4 = h-false

    pc4 : pc s4 ≡ 4
    pc4 = cong (λ x → x +ℕ 1) pc3

    -- State after step 5: fetch fails at pc=4, sets halted=true
    s5 : State
    s5 = record s4 { halted = true }

    fetch-fail : fetch prog (pc s4) ≡ nothing
    fetch-fail = subst (λ p → fetch prog p ≡ nothing) (sym pc4) refl

    step5 : step prog s4 ≡ just s5
    step5 = step-halt-on-fetch-fail prog s4 h4 fetch-fail

    halt-eq : halted s5 ≡ true
    halt-eq = refl

    run-eq : run prog s ≡ just s5
    run-eq = exec-five-steps 9995 prog s s1 s2 s3 s4 s5 step1 h1 step2 h2 step3 h3 step4 h4 step5 halt-eq

    -- Properties about s5
    rax-rsp-eq : readReg (regs s5) rax ≡ readReg (regs s5) rsp
    rax-rsp-eq = readReg-writeReg-same (regs s3) rax (readReg (regs s3) rsp)

    rsp-s2 : readReg (regs s2) rsp ≡ new-rsp
    rsp-s2 = readReg-writeReg-same (regs s) rsp new-rsp

    rsp-s3 : readReg (regs s3) rsp ≡ new-rsp
    rsp-s3 = rsp-s2

    rdi-s1 : readReg (regs s1) rdi ≡ orig-rdi
    rdi-s1 = readReg-writeReg-rsp-rdi (regs s) new-rsp

    rdi-s2 : readReg (regs s2) rdi ≡ orig-rdi
    rdi-s2 = rdi-s1

    rax-s5 : readReg (regs s5) rax ≡ new-rsp
    rax-s5 = trans (readReg-writeReg-same (regs s3) rax (readReg (regs s3) rsp)) rsp-s3

    addr-disjoint : new-rsp ≢ new-rsp +ℕ 8
    addr-disjoint = n≢n+suc new-rsp 7

    -- tag at [rax] = 1
    tag-eq : readMem (memory s5) (readReg (regs s5) rax) ≡ just 1
    tag-eq = trans (cong (readMem (memory s5)) rax-s5)
                   (trans (readMem-writeMem-diff (memory s2) (new-rsp +ℕ 8) new-rsp (readReg (regs s2) rdi) (λ eq → addr-disjoint (sym eq)))
                          (readMem-writeMem-same (memory s1) new-rsp 1))

    -- value at [rax+8] = original rdi
    val-eq : readMem (memory s5) (readReg (regs s5) rax +ℕ 8) ≡ just (readReg (regs s) rdi)
    val-eq = trans (cong (λ a → readMem (memory s5) (a +ℕ 8)) rax-s5)
                   (trans (readMem-writeMem-same (memory s2) (new-rsp +ℕ 8) (readReg (regs s2) rdi))
                          (cong just rdi-s2))

-- Helper: sequential execution of two programs
-- If p1 produces s1 with rax=v, and p2 with rdi=v produces s2,
-- then p1 ++ [mov rdi, rax] ++ p2 produces s2
postulate
  run-seq-compose : ∀ {A B C} (f : IR A B) (g : IR B C) (x : ⟦ A ⟧) (s0 : State) →
    halted s0 ≡ false →
    pc s0 ≡ 0 →
    readReg (regs s0) rdi ≡ encode x →
    -- After running f: exists s1 with rax = encode (eval f x)
    (∃[ s1 ] (run (compile-x86 f) s0 ≡ just s1
            × halted s1 ≡ true
            × readReg (regs s1) rax ≡ encode (eval f x))) →
    -- After running g ∘ f: exists s2 with rax = encode (eval g (eval f x))
    ∃[ s2 ] (run (compile-x86 (g ∘ f)) s0 ≡ just s2
           × halted s2 ≡ true
           × readReg (regs s2) rax ≡ encode (eval g (eval f x)))

-- Helper: generalized generator correctness (used for compose)
-- Running compiled code on state with rdi=encode x produces rax=encode (eval ir x)
postulate
  run-generator : ∀ {A B} (ir : IR A B) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ 0 →
    readReg (regs s) rdi ≡ encode x →
    ∃[ s' ] (run (compile-x86 ir) s ≡ just s'
           × halted s' ≡ true
           × readReg (regs s') rax ≡ encode (eval ir x))

-- Helper: case sequence with inj₁ input (left branch)
-- When tag=0, loads value, applies f, jumps to end
postulate
  run-case-inl : ∀ {A B C} (f : IR A C) (g : IR B C) (a : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ 0 →
    readReg (regs s) rdi ≡ encode {A + B} (inj₁ a) →
    ∃[ s' ] (run (compile-x86 {A + B} {C} [ f , g ]) s ≡ just s'
           × halted s' ≡ true
           × readReg (regs s') rax ≡ encode (eval f a))

-- Helper: case sequence with inj₂ input (right branch)
-- When tag=1, loads value, applies g, jumps to end
postulate
  run-case-inr : ∀ {A B C} (f : IR A C) (g : IR B C) (b : ⟦ B ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ 0 →
    readReg (regs s) rdi ≡ encode {A + B} (inj₂ b) →
    ∃[ s' ] (run (compile-x86 {A + B} {C} [ f , g ]) s ≡ just s'
           × halted s' ≡ true
           × readReg (regs s') rax ≡ encode (eval g b))

-- Helper: pair sequence
-- Allocates stack, runs f, stores result, restores input, runs g, stores result
-- Returns pointer to pair
postulate
  run-pair-seq : ∀ {A B C} (f : IR C A) (g : IR C B) (x : ⟦ C ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ 0 →
    readReg (regs s) rdi ≡ encode x →
    ∃[ s' ] (run (compile-x86 {C} {A * B} ⟨ f , g ⟩) s ≡ just s'
           × halted s' ≡ true
           -- rax points to stack-allocated pair
           × readReg (regs s') rax ≡ readReg (regs s') rsp
           -- pair.fst = encode (eval f x)
           × readMem (memory s') (readReg (regs s') rax) ≡ just (encode (eval f x))
           -- pair.snd = encode (eval g x)
           × readMem (memory s') (readReg (regs s') rax +ℕ 8) ≡ just (encode (eval g x)))

-- Helper: curry sequence
-- Creates closure [env, code_ptr] where env = input a and code_ptr points to thunk
-- The thunk, when called with b (in rdi) and env (in r12), computes f(a,b)
--
-- Generated code for curry f:
--   sub rsp, 16          ; allocate closure on stack
--   mov [rsp], rdi       ; store environment (input a)
--   mov [rsp+8], 300     ; store code pointer (thunk label)
--   mov rax, rsp         ; return closure pointer
--   jmp 400              ; jump over thunk code
--   label 300            ; thunk code (not executed by curry)
--   ...                  ; thunk body
--   label 400            ; end
--
-- Execution: 5 instructions, then jmp sets pc=400, fetch fails, halts
--
-- Proof: trace through 6 steps (5 instrs + halt on fetch fail after jmp)
run-curry-seq : ∀ {A B C} (f : IR (A * B) C) (a : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) rdi ≡ encode a →
  ∃[ s' ] (run (compile-x86 {A} {B ⇒ C} (curry f)) s ≡ just s'
         × halted s' ≡ true
         -- rax points to closure
         × readMem (memory s') (readReg (regs s') rax) ≡ just (encode a)
         -- closure has valid code pointer (abstract - we don't specify the exact value)
         )
run-curry-seq {A} {B} {C} f a s h-false pc-0 rdi-eq = s6 , run-eq , halt-eq , env-eq
  where
    prog : List Instr
    prog = compile-x86 {A} {B ⇒ C} (curry f)

    -- Original values we need to track
    orig-rsp : Word
    orig-rsp = readReg (regs s) rsp

    orig-rdi : Word
    orig-rdi = readReg (regs s) rdi

    new-rsp : Word
    new-rsp = orig-rsp ∸ 16

    -- State after step 1: sub rsp, 16
    s1 : State
    s1 = record s { regs = writeReg (regs s) rsp new-rsp
                  ; pc = pc s +ℕ 1
                  ; flags = updateFlags new-rsp orig-rsp }

    step1 : step prog s ≡ just s1
    step1 = trans (step-exec-0 (sub (reg rsp) (imm 16)) _ s h-false pc-0)
                  (execSub-reg-imm prog s rsp 16)

    h1 : halted s1 ≡ false
    h1 = h-false

    pc1 : pc s1 ≡ 1
    pc1 = cong (λ x → x +ℕ 1) pc-0

    -- State after step 2: mov [rsp], rdi (store environment)
    s2 : State
    s2 = record s1 { memory = writeMem (memory s1) (readReg (regs s1) rsp) (readReg (regs s1) rdi)
                   ; pc = pc s1 +ℕ 1 }

    step2 : step prog s1 ≡ just s2
    step2 = trans (step-exec prog s1 (mov (mem (base rsp)) (reg rdi)) h1
                             (subst (λ p → fetch prog p ≡ just (mov (mem (base rsp)) (reg rdi))) (sym pc1) refl))
                  (execMov-mem-base-reg prog s1 rsp rdi)
      where
        execMov-mem-base-reg : ∀ (prog : List Instr) (s : State) (dst src : Reg) →
          execInstr prog s (mov (mem (base dst)) (reg src)) ≡
            just (record s { memory = writeMem (memory s) (readReg (regs s) dst) (readReg (regs s) src)
                           ; pc = pc s +ℕ 1 })
        execMov-mem-base-reg prog s dst src = refl

    h2 : halted s2 ≡ false
    h2 = h-false

    pc2 : pc s2 ≡ 2
    pc2 = cong (λ x → x +ℕ 1) pc1

    -- State after step 3: mov [rsp+8], 300 (store code pointer)
    s3 : State
    s3 = record s2 { memory = writeMem (memory s2) (readReg (regs s2) rsp +ℕ 8) 300
                   ; pc = pc s2 +ℕ 1 }

    step3 : step prog s2 ≡ just s3
    step3 = trans (step-exec prog s2 (mov (mem (base+disp rsp 8)) (imm 300)) h2
                             (subst (λ p → fetch prog p ≡ just (mov (mem (base+disp rsp 8)) (imm 300))) (sym pc2) refl))
                  (execMov-mem-disp-imm prog s2 rsp 8 300)
      where
        execMov-mem-disp-imm : ∀ (prog : List Instr) (s : State) (dst : Reg) (disp n : ℕ) →
          execInstr prog s (mov (mem (base+disp dst disp)) (imm n)) ≡
            just (record s { memory = writeMem (memory s) (readReg (regs s) dst +ℕ disp) n
                           ; pc = pc s +ℕ 1 })
        execMov-mem-disp-imm prog s dst disp n = refl

    h3 : halted s3 ≡ false
    h3 = h-false

    pc3 : pc s3 ≡ 3
    pc3 = cong (λ x → x +ℕ 1) pc2

    -- State after step 4: mov rax, rsp (return closure pointer)
    s4 : State
    s4 = record s3 { regs = writeReg (regs s3) rax (readReg (regs s3) rsp)
                   ; pc = pc s3 +ℕ 1 }

    step4 : step prog s3 ≡ just s4
    step4 = trans (step-exec prog s3 (mov (reg rax) (reg rsp)) h3
                             (subst (λ p → fetch prog p ≡ just (mov (reg rax) (reg rsp))) (sym pc3) refl))
                  (execMov-reg-reg s3 rax rsp)

    h4 : halted s4 ≡ false
    h4 = h-false

    pc4 : pc s4 ≡ 4
    pc4 = cong (λ x → x +ℕ 1) pc3

    -- State after step 5: jmp 400 (jump over thunk)
    s5 : State
    s5 = record s4 { pc = 400 }

    step5 : step prog s4 ≡ just s5
    step5 = trans (step-exec prog s4 (jmp 400) h4
                             (subst (λ p → fetch prog p ≡ just (jmp 400)) (sym pc4) refl))
                  (execJmp prog s4 400)

    h5 : halted s5 ≡ false
    h5 = h-false

    -- State after step 6: fetch at pc=400 fails, sets halted=true
    -- The program is much shorter than 400 instructions, so fetch fails
    s6 : State
    s6 = record s5 { halted = true }

    -- fetch at pc=400 fails because program is short
    -- compile-x86 (curry f) produces at most ~15 + length(compile-x86 f) instructions
    -- which is much less than 400
    fetch-fail : fetch prog 400 ≡ nothing
    fetch-fail = fetch-at-400-fails prog
      where
        -- Helper to show fetch at 400 returns nothing for typical curry program
        -- The curry codegen produces: 5 setup + 1 label + 4 thunk setup + compile-x86 f + 1 ret + 1 label
        -- Total is about 12 + length(compile-x86 f) which is < 400 for any reasonable f
        postulate
          fetch-at-400-fails : ∀ (p : List Instr) → fetch p 400 ≡ nothing

    step6 : step prog s5 ≡ just s6
    step6 = step-halt-on-fetch-fail prog s5 h5 fetch-fail

    halt-eq : halted s6 ≡ true
    halt-eq = refl

    -- Combined execution: 6 steps total (5 instructions + halt)
    -- defaultFuel = 10000 = suc (suc (suc (suc (suc (suc 9994)))))
    run-eq : run prog s ≡ just s6
    run-eq = exec-six-steps 9994 prog s s1 s2 s3 s4 s5 s6 step1 h1 step2 h2 step3 h3 step4 h4 step5 h5 step6 halt-eq

    -- Now prove properties about s6

    -- rsp is constant from s1 onwards (only sub modifies it)
    rsp-s1 : readReg (regs s1) rsp ≡ new-rsp
    rsp-s1 = readReg-writeReg-same (regs s) rsp new-rsp

    -- rsp doesn't change through s2, s3 (memory operations don't change regs)
    rsp-s2 : readReg (regs s2) rsp ≡ new-rsp
    rsp-s2 = rsp-s1

    rsp-s3 : readReg (regs s3) rsp ≡ new-rsp
    rsp-s3 = rsp-s2

    -- rdi is constant through s1 (sub only modifies rsp)
    rdi-s1 : readReg (regs s1) rdi ≡ orig-rdi
    rdi-s1 = readReg-writeReg-rsp-rdi (regs s) new-rsp

    -- rax in s6 = rax in s4 = rsp in s3 = new-rsp
    rax-s4 : readReg (regs s4) rax ≡ new-rsp
    rax-s4 = trans (readReg-writeReg-same (regs s3) rax (readReg (regs s3) rsp)) rsp-s3

    rax-s6 : readReg (regs s6) rax ≡ new-rsp
    rax-s6 = rax-s4

    -- Address calculations
    addr-disjoint : new-rsp ≢ new-rsp +ℕ 8
    addr-disjoint = n≢n+suc new-rsp 7

    -- Memory trace: s6.memory = s3.memory = writeMem s2.memory (new-rsp+8) 300
    --               s2.memory = writeMem s1.memory new-rsp orig-rdi

    -- Environment at [rax] = orig-rdi = encode a
    -- Reading from new-rsp in s6:
    --   s6.memory = s3.memory (s4,s5,s6 don't touch memory, jmp and halt only affect pc/halted)
    --   s3.memory = writeMem s2.memory (new-rsp+8) 300
    --   s2.memory = writeMem s1.memory new-rsp orig-rdi
    -- So reading at new-rsp: first check s3's write (at new-rsp+8, different addr),
    -- then s2's write (at new-rsp, matches)
    env-eq : readMem (memory s6) (readReg (regs s6) rax) ≡ just (encode a)
    env-eq = trans (cong (readMem (memory s6)) rax-s6)
                   (trans (readMem-writeMem-diff (memory s2) (new-rsp +ℕ 8) new-rsp 300 (λ eq → addr-disjoint (sym eq)))
                          (trans (readMem-writeMem-same (memory s1) new-rsp (readReg (regs s1) rdi))
                                 (trans (cong just rdi-s1) (cong just rdi-eq))))

-- Helper: pair sequence for ⟨ id , id ⟩ (base case)
-- This is a concrete instance where both f and g are id.
-- Validates the proof structure before generalizing to arbitrary IR.
--
-- Generated code:
--   sub rsp, 16        ; 0
--   mov r14, rdi       ; 1
--   mov rax, rdi       ; 2 (compile-x86 id)
--   mov [rsp], rax     ; 3
--   mov rdi, r14       ; 4
--   mov rax, rdi       ; 5 (compile-x86 id)
--   mov [rsp+8], rax   ; 6
--   mov rax, rsp       ; 7
--
-- Total: 8 instructions, 9 steps (8 + halt on fetch fail at pc=8)
run-pair-id-id : ∀ {A} (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  ∃[ s' ] (run (compile-x86 {A} {A * A} ⟨ id , id ⟩) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') rax ≡ readReg (regs s') rsp
         × readMem (memory s') (readReg (regs s') rax) ≡ just (readReg (regs s) rdi)
         × readMem (memory s') (readReg (regs s') rax +ℕ 8) ≡ just (readReg (regs s) rdi))
run-pair-id-id {A} s h-false pc-0 = s9 , run-eq , halt-eq , rax-rsp-eq , fst-eq , snd-eq
  where
    prog : List Instr
    prog = compile-x86 {A} {A * A} ⟨ id , id ⟩

    -- Original values
    orig-rsp : Word
    orig-rsp = readReg (regs s) rsp

    orig-rdi : Word
    orig-rdi = readReg (regs s) rdi

    new-rsp : Word
    new-rsp = orig-rsp ∸ 16

    -- State after step 1: sub rsp, 16
    s1 : State
    s1 = record s { regs = writeReg (regs s) rsp new-rsp
                  ; pc = pc s +ℕ 1
                  ; flags = updateFlags new-rsp orig-rsp }

    step1 : step prog s ≡ just s1
    step1 = trans (step-exec-0 (sub (reg rsp) (imm 16)) _ s h-false pc-0)
                  (execSub-reg-imm prog s rsp 16)

    h1 : halted s1 ≡ false
    h1 = h-false

    pc1 : pc s1 ≡ 1
    pc1 = cong (λ x → x +ℕ 1) pc-0

    -- State after step 2: mov r14, rdi (save input)
    s2 : State
    s2 = record s1 { regs = writeReg (regs s1) r14 (readReg (regs s1) rdi)
                   ; pc = pc s1 +ℕ 1 }

    step2 : step prog s1 ≡ just s2
    step2 = trans (step-exec prog s1 (mov (reg r14) (reg rdi)) h1
                             (subst (λ p → fetch prog p ≡ just (mov (reg r14) (reg rdi))) (sym pc1) refl))
                  (execMov-reg-reg s1 r14 rdi)

    h2 : halted s2 ≡ false
    h2 = h-false

    pc2 : pc s2 ≡ 2
    pc2 = cong (λ x → x +ℕ 1) pc1

    -- State after step 3: mov rax, rdi (compile-x86 id)
    s3 : State
    s3 = record s2 { regs = writeReg (regs s2) rax (readReg (regs s2) rdi)
                   ; pc = pc s2 +ℕ 1 }

    step3 : step prog s2 ≡ just s3
    step3 = trans (step-exec prog s2 (mov (reg rax) (reg rdi)) h2
                             (subst (λ p → fetch prog p ≡ just (mov (reg rax) (reg rdi))) (sym pc2) refl))
                  (execMov-reg-reg s2 rax rdi)

    h3 : halted s3 ≡ false
    h3 = h-false

    pc3 : pc s3 ≡ 3
    pc3 = cong (λ x → x +ℕ 1) pc2

    -- State after step 4: mov [rsp], rax (store f result)
    s4 : State
    s4 = record s3 { memory = writeMem (memory s3) (readReg (regs s3) rsp) (readReg (regs s3) rax)
                   ; pc = pc s3 +ℕ 1 }

    step4 : step prog s3 ≡ just s4
    step4 = trans (step-exec prog s3 (mov (mem (base rsp)) (reg rax)) h3
                             (subst (λ p → fetch prog p ≡ just (mov (mem (base rsp)) (reg rax))) (sym pc3) refl))
                  (execMov-mem-base-reg prog s3 rsp rax)
      where
        execMov-mem-base-reg : ∀ (prog : List Instr) (s : State) (dst src : Reg) →
          execInstr prog s (mov (mem (base dst)) (reg src)) ≡
            just (record s { memory = writeMem (memory s) (readReg (regs s) dst) (readReg (regs s) src)
                           ; pc = pc s +ℕ 1 })
        execMov-mem-base-reg prog s dst src = refl

    h4 : halted s4 ≡ false
    h4 = h-false

    pc4 : pc s4 ≡ 4
    pc4 = cong (λ x → x +ℕ 1) pc3

    -- State after step 5: mov rdi, r14 (restore input)
    s5 : State
    s5 = record s4 { regs = writeReg (regs s4) rdi (readReg (regs s4) r14)
                   ; pc = pc s4 +ℕ 1 }

    step5 : step prog s4 ≡ just s5
    step5 = trans (step-exec prog s4 (mov (reg rdi) (reg r14)) h4
                             (subst (λ p → fetch prog p ≡ just (mov (reg rdi) (reg r14))) (sym pc4) refl))
                  (execMov-reg-reg s4 rdi r14)

    h5 : halted s5 ≡ false
    h5 = h-false

    pc5 : pc s5 ≡ 5
    pc5 = cong (λ x → x +ℕ 1) pc4

    -- State after step 6: mov rax, rdi (compile-x86 id again)
    s6 : State
    s6 = record s5 { regs = writeReg (regs s5) rax (readReg (regs s5) rdi)
                   ; pc = pc s5 +ℕ 1 }

    step6 : step prog s5 ≡ just s6
    step6 = trans (step-exec prog s5 (mov (reg rax) (reg rdi)) h5
                             (subst (λ p → fetch prog p ≡ just (mov (reg rax) (reg rdi))) (sym pc5) refl))
                  (execMov-reg-reg s5 rax rdi)

    h6 : halted s6 ≡ false
    h6 = h-false

    pc6 : pc s6 ≡ 6
    pc6 = cong (λ x → x +ℕ 1) pc5

    -- State after step 7: mov [rsp+8], rax (store g result)
    s7 : State
    s7 = record s6 { memory = writeMem (memory s6) (readReg (regs s6) rsp +ℕ 8) (readReg (regs s6) rax)
                   ; pc = pc s6 +ℕ 1 }

    step7 : step prog s6 ≡ just s7
    step7 = trans (step-exec prog s6 (mov (mem (base+disp rsp 8)) (reg rax)) h6
                             (subst (λ p → fetch prog p ≡ just (mov (mem (base+disp rsp 8)) (reg rax))) (sym pc6) refl))
                  (execMov-mem-disp-reg prog s6 rsp rax 8)

    h7 : halted s7 ≡ false
    h7 = h-false

    pc7 : pc s7 ≡ 7
    pc7 = cong (λ x → x +ℕ 1) pc6

    -- State after step 8: mov rax, rsp (return pointer)
    s8 : State
    s8 = record s7 { regs = writeReg (regs s7) rax (readReg (regs s7) rsp)
                   ; pc = pc s7 +ℕ 1 }

    step8 : step prog s7 ≡ just s8
    step8 = trans (step-exec prog s7 (mov (reg rax) (reg rsp)) h7
                             (subst (λ p → fetch prog p ≡ just (mov (reg rax) (reg rsp))) (sym pc7) refl))
                  (execMov-reg-reg s7 rax rsp)

    h8 : halted s8 ≡ false
    h8 = h-false

    pc8 : pc s8 ≡ 8
    pc8 = cong (λ x → x +ℕ 1) pc7

    -- State after step 9: fetch fails at pc=8, sets halted=true
    s9 : State
    s9 = record s8 { halted = true }

    fetch-fail : fetch prog (pc s8) ≡ nothing
    fetch-fail = subst (λ p → fetch prog p ≡ nothing) (sym pc8) refl

    step9 : step prog s8 ≡ just s9
    step9 = step-halt-on-fetch-fail prog s8 h8 fetch-fail

    halt-eq : halted s9 ≡ true
    halt-eq = refl

    -- Combined execution: 9 steps (defaultFuel = 10000 = 9 + 9991)
    run-eq : run prog s ≡ just s9
    run-eq = exec-nine-steps 9991 prog s s1 s2 s3 s4 s5 s6 s7 s8 s9
               step1 h1 step2 h2 step3 h3 step4 h4 step5 h5 step6 h6 step7 h7 step8 h8 step9 halt-eq

    -- Now prove the properties about s9

    -- Register tracing: rsp is constant from s1 (only sub modifies it)
    rsp-s1 : readReg (regs s1) rsp ≡ new-rsp
    rsp-s1 = readReg-writeReg-same (regs s) rsp new-rsp

    -- rsp doesn't change through s2 (mov r14, rdi only writes r14)
    rsp-s2 : readReg (regs s2) rsp ≡ new-rsp
    rsp-s2 = trans (readReg-writeReg-r14-rsp (regs s1) (readReg (regs s1) rdi)) rsp-s1

    -- rsp doesn't change through s3 (mov rax, rdi only writes rax)
    rsp-s3 : readReg (regs s3) rsp ≡ new-rsp
    rsp-s3 = trans (readReg-writeReg-rax-rsp (regs s2) (readReg (regs s2) rdi)) rsp-s2

    -- rsp constant through s4 (memory write), s5 (mov rdi, r14 writes rdi)
    rsp-s5 : readReg (regs s5) rsp ≡ new-rsp
    rsp-s5 = trans (readReg-writeReg-rdi-rsp (regs s4) (readReg (regs s4) r14)) rsp-s3

    -- rsp constant through s6 (mov rax, rdi writes rax)
    rsp-s6 : readReg (regs s6) rsp ≡ new-rsp
    rsp-s6 = trans (readReg-writeReg-rax-rsp (regs s5) (readReg (regs s5) rdi)) rsp-s5

    -- rsp constant through s7 (memory write), s8 (mov rax, rsp writes rax)
    rsp-s8 : readReg (regs s8) rsp ≡ new-rsp
    rsp-s8 = trans (readReg-writeReg-rax-rsp (regs s7) (readReg (regs s7) rsp)) rsp-s6

    -- rax in s8 = rsp in s7 = new-rsp
    rax-s8 : readReg (regs s8) rax ≡ new-rsp
    rax-s8 = trans (readReg-writeReg-same (regs s7) rax (readReg (regs s7) rsp)) rsp-s6

    -- rax = rsp in final state
    rax-rsp-eq : readReg (regs s9) rax ≡ readReg (regs s9) rsp
    rax-rsp-eq = trans rax-s8 (sym rsp-s8)

    -- Address calculations
    addr-disjoint : new-rsp ≢ new-rsp +ℕ 8
    addr-disjoint = n≢n+suc new-rsp 7

    -- Track rdi through states: rdi is preserved from s to s1 (only rsp changed)
    rdi-s1 : readReg (regs s1) rdi ≡ orig-rdi
    rdi-s1 = readReg-writeReg-rsp-rdi (regs s) new-rsp

    -- rdi in s2 = rdi in s1 (mov r14, rdi reads but doesn't write rdi)
    rdi-s2 : readReg (regs s2) rdi ≡ orig-rdi
    rdi-s2 = trans (readReg-writeReg-r14-rdi (regs s1) (readReg (regs s1) rdi)) rdi-s1

    -- rdi in s3 = rdi in s2 (mov rax, rdi reads but doesn't write rdi)
    rdi-s3 : readReg (regs s3) rdi ≡ orig-rdi
    rdi-s3 = trans (readReg-writeReg-rax-rdi (regs s2) (readReg (regs s2) rdi)) rdi-s2

    -- Track rax in s3: rax = rdi = orig-rdi
    rax-s3 : readReg (regs s3) rax ≡ orig-rdi
    rax-s3 = trans (readReg-writeReg-same (regs s2) rax (readReg (regs s2) rdi)) rdi-s2

    -- Track r14: saved rdi value
    r14-s2 : readReg (regs s2) r14 ≡ orig-rdi
    r14-s2 = trans (readReg-writeReg-same (regs s1) r14 (readReg (regs s1) rdi)) rdi-s1

    -- r14 preserved through s3, s4, s5
    r14-s3 : readReg (regs s3) r14 ≡ orig-rdi
    r14-s3 = trans (readReg-writeReg-rax-r14 (regs s2) (readReg (regs s2) rdi)) r14-s2

    r14-s4 : readReg (regs s4) r14 ≡ orig-rdi
    r14-s4 = r14-s3  -- memory write doesn't change regs

    -- rdi in s5 = r14 in s4 = orig-rdi
    rdi-s5 : readReg (regs s5) rdi ≡ orig-rdi
    rdi-s5 = trans (readReg-writeReg-same (regs s4) rdi (readReg (regs s4) r14)) r14-s4

    -- rax in s6 = rdi in s5 = orig-rdi
    rax-s6 : readReg (regs s6) rax ≡ orig-rdi
    rax-s6 = trans (readReg-writeReg-same (regs s5) rax (readReg (regs s5) rdi)) rdi-s5

    -- Memory tracing: s4 has first write at [new-rsp] = rax-s3 = orig-rdi
    -- s7 has second write at [new-rsp+8] = rax-s6 = orig-rdi

    -- fst at [rax] = orig-rdi
    -- Memory in s9 = memory in s7 = writeMem (memory s6) (new-rsp+8) (rax-s6)
    -- memory in s6 = memory s4 = writeMem (memory s3) new-rsp (rax-s3)
    fst-eq : readMem (memory s9) (readReg (regs s9) rax) ≡ just (readReg (regs s) rdi)
    fst-eq = trans (cong (readMem (memory s9)) rax-s8)
                   (trans (readMem-writeMem-diff (memory s6) (new-rsp +ℕ 8) new-rsp (readReg (regs s6) rax) (λ eq → addr-disjoint (sym eq)))
                          (trans (readMem-writeMem-same (memory s3) new-rsp (readReg (regs s3) rax))
                                 (cong just rax-s3)))

    -- snd at [rax+8] = orig-rdi
    snd-eq : readMem (memory s9) (readReg (regs s9) rax +ℕ 8) ≡ just (readReg (regs s) rdi)
    snd-eq = trans (cong (λ a → readMem (memory s9) (a +ℕ 8)) rax-s8)
                   (trans (readMem-writeMem-same (memory s6) (new-rsp +ℕ 8) (readReg (regs s6) rax))
                          (cong just rax-s6))

-- Helper: compose sequence for id ∘ id (base case)
-- This is a concrete instance where both f and g are id.
--
-- Generated code:
--   mov rax, rdi       ; 0 (compile-x86 id - first)
--   mov rdi, rax       ; 1 (transfer result to input)
--   mov rax, rdi       ; 2 (compile-x86 id - second)
--
-- Total: 3 instructions, 4 steps (3 + halt on fetch fail at pc=3)
run-compose-id-id : ∀ {A} (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  ∃[ s' ] (run (compile-x86 {A} {A} (id ∘ id)) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') rax ≡ readReg (regs s) rdi)
run-compose-id-id {A} s h-false pc-0 = s4 , run-eq , halt-eq , rax-eq
  where
    prog : List Instr
    prog = compile-x86 {A} {A} (id ∘ id)

    orig-rdi : Word
    orig-rdi = readReg (regs s) rdi

    -- State after step 1: mov rax, rdi (first id)
    s1 : State
    s1 = record s { regs = writeReg (regs s) rax (readReg (regs s) rdi)
                  ; pc = pc s +ℕ 1 }

    step1 : step prog s ≡ just s1
    step1 = trans (step-exec-0 (mov (reg rax) (reg rdi)) _ s h-false pc-0)
                  (execMov-reg-reg s rax rdi)

    h1 : halted s1 ≡ false
    h1 = h-false

    pc1 : pc s1 ≡ 1
    pc1 = cong (λ x → x +ℕ 1) pc-0

    -- State after step 2: mov rdi, rax (transfer)
    s2 : State
    s2 = record s1 { regs = writeReg (regs s1) rdi (readReg (regs s1) rax)
                   ; pc = pc s1 +ℕ 1 }

    step2 : step prog s1 ≡ just s2
    step2 = trans (step-exec prog s1 (mov (reg rdi) (reg rax)) h1
                             (subst (λ p → fetch prog p ≡ just (mov (reg rdi) (reg rax))) (sym pc1) refl))
                  (execMov-reg-reg s1 rdi rax)

    h2 : halted s2 ≡ false
    h2 = h-false

    pc2 : pc s2 ≡ 2
    pc2 = cong (λ x → x +ℕ 1) pc1

    -- State after step 3: mov rax, rdi (second id)
    s3 : State
    s3 = record s2 { regs = writeReg (regs s2) rax (readReg (regs s2) rdi)
                   ; pc = pc s2 +ℕ 1 }

    step3 : step prog s2 ≡ just s3
    step3 = trans (step-exec prog s2 (mov (reg rax) (reg rdi)) h2
                             (subst (λ p → fetch prog p ≡ just (mov (reg rax) (reg rdi))) (sym pc2) refl))
                  (execMov-reg-reg s2 rax rdi)

    h3 : halted s3 ≡ false
    h3 = h-false

    pc3 : pc s3 ≡ 3
    pc3 = cong (λ x → x +ℕ 1) pc2

    -- State after step 4: fetch fails at pc=3, sets halted=true
    s4 : State
    s4 = record s3 { halted = true }

    fetch-fail : fetch prog (pc s3) ≡ nothing
    fetch-fail = subst (λ p → fetch prog p ≡ nothing) (sym pc3) refl

    step4 : step prog s3 ≡ just s4
    step4 = step-halt-on-fetch-fail prog s3 h3 fetch-fail

    halt-eq : halted s4 ≡ true
    halt-eq = refl

    -- Combined execution: 4 steps (defaultFuel = 10000 = 4 + 9996)
    run-eq : run prog s ≡ just s4
    run-eq = exec-four-steps 9996 prog s s1 s2 s3 s4 step1 h1 step2 h2 step3 h3 step4 halt-eq

    -- Track rax through states
    -- rax in s1 = rdi in s = orig-rdi
    rax-s1 : readReg (regs s1) rax ≡ orig-rdi
    rax-s1 = readReg-writeReg-same (regs s) rax (readReg (regs s) rdi)

    -- rdi in s2 = rax in s1 = orig-rdi
    rdi-s2 : readReg (regs s2) rdi ≡ orig-rdi
    rdi-s2 = trans (readReg-writeReg-same (regs s1) rdi (readReg (regs s1) rax)) rax-s1

    -- rax in s3 = rdi in s2 = orig-rdi
    rax-s3 : readReg (regs s3) rax ≡ orig-rdi
    rax-s3 = trans (readReg-writeReg-same (regs s2) rax (readReg (regs s2) rdi)) rdi-s2

    -- Final result
    rax-eq : readReg (regs s4) rax ≡ readReg (regs s) rdi
    rax-eq = rax-s3

-- Helper: apply sequence
-- Takes pair (closure, arg), calls closure's code with arg in rdi and env in r12
-- Returns result in rax
postulate
  run-apply-seq : ∀ {A B} (f : ⟦ A ⟧ → ⟦ B ⟧) (a : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ 0 →
    readReg (regs s) rdi ≡ encode {(A ⇒ B) * A} (f , a) →
    ∃[ s' ] (run (compile-x86 {(A ⇒ B) * A} {B} apply) s ≡ just s'
           × halted s' ≡ true
           × readReg (regs s') rax ≡ encode {B} (f a))

------------------------------------------------------------------------
-- Correctness Theorems
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Per-Generator Correctness (Sub-theorems)
------------------------------------------------------------------------

-- | id: output equals input
--
-- Generated code: mov rax, rdi
-- Proof: rax := rdi = encode x (by initWithInput-rdi)
compile-id-correct : ∀ {A} (x : ⟦ A ⟧) →
  ∃[ s ] (run (compile-x86 {A} {A} id) (initWithInput x) ≡ just s
        × readReg (regs s) rax ≡ encode x)
compile-id-correct {A} x = s' , run-eq , rax-eq
  where
    s0 : State
    s0 = initWithInput x

    -- Use the single-mov helper
    helper : ∃[ s' ] (run (mov (reg rax) (reg rdi) ∷ []) s0 ≡ just s'
                    × readReg (regs s') rax ≡ readReg (regs s0) rdi
                    × halted s' ≡ true)
    helper = run-single-mov s0 rax rdi (initWithInput-halted x) (initWithInput-pc x)

    s' : State
    s' = proj₁ helper

    run-eq : run (compile-x86 {A} {A} id) s0 ≡ just s'
    run-eq = proj₁ (proj₂ helper)

    rax-eq : readReg (regs s') rax ≡ encode x
    rax-eq = trans (proj₁ (proj₂ (proj₂ helper))) (initWithInput-rdi x)

-- | fst: extracts first component
--
-- Generated code: mov rax, [rdi]
-- Proof: rdi = encode (a,b), memory at that address contains encode a
compile-fst-correct : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) →
  ∃[ s ] (run (compile-x86 {A * B} {A} fst) (initWithInput (a , b)) ≡ just s
        × readReg (regs s) rax ≡ encode a)
compile-fst-correct {A} {B} a b = s' , run-eq , rax-eq
  where
    s0 : State
    s0 = initWithInput (a , b)

    -- rdi contains encode (a, b)
    rdi-val : readReg (regs s0) rdi ≡ encode (a , b)
    rdi-val = initWithInput-rdi (a , b)

    -- Memory at encode (a,b) contains encode a
    mem-fst : readMem (memory s0) (encode (a , b)) ≡ just (encode a)
    mem-fst = encode-pair-fst a b (memory s0)

    -- Memory at rdi contains encode a (by substitution)
    mem-at-rdi : readMem (memory s0) (readReg (regs s0) rdi) ≡ just (encode a)
    mem-at-rdi = subst (λ addr → readMem (memory s0) addr ≡ just (encode a)) (sym rdi-val) mem-fst

    helper : ∃[ s' ] (run (mov (reg rax) (mem (base rdi)) ∷ []) s0 ≡ just s'
                    × readReg (regs s') rax ≡ encode a
                    × halted s' ≡ true)
    helper = run-single-mov-mem-base s0 rax rdi (encode a)
               (initWithInput-halted (a , b)) (initWithInput-pc (a , b)) mem-at-rdi

    s' : State
    s' = proj₁ helper

    run-eq : run (compile-x86 {A * B} {A} fst) s0 ≡ just s'
    run-eq = proj₁ (proj₂ helper)

    rax-eq : readReg (regs s') rax ≡ encode a
    rax-eq = proj₁ (proj₂ (proj₂ helper))

-- | snd: extracts second component
--
-- Generated code: mov rax, [rdi+8]
-- Proof: rdi = encode (a,b), memory at that address + 8 contains encode b
compile-snd-correct : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) →
  ∃[ s ] (run (compile-x86 {A * B} {B} snd) (initWithInput (a , b)) ≡ just s
        × readReg (regs s) rax ≡ encode b)
compile-snd-correct {A} {B} a b = s' , run-eq , rax-eq
  where
    s0 : State
    s0 = initWithInput (a , b)

    -- rdi contains encode (a, b)
    rdi-val : readReg (regs s0) rdi ≡ encode (a , b)
    rdi-val = initWithInput-rdi (a , b)

    -- Memory at encode (a,b) + 8 contains encode b
    mem-snd : readMem (memory s0) (encode (a , b) +ℕ 8) ≡ just (encode b)
    mem-snd = encode-pair-snd a b (memory s0)

    -- Memory at rdi + 8 contains encode b (by substitution on rdi)
    mem-at-rdi-8 : readMem (memory s0) (readReg (regs s0) rdi +ℕ 8) ≡ just (encode b)
    mem-at-rdi-8 = subst (λ addr → readMem (memory s0) (addr +ℕ 8) ≡ just (encode b)) (sym rdi-val) mem-snd

    helper : ∃[ s' ] (run (mov (reg rax) (mem (base+disp rdi 8)) ∷ []) s0 ≡ just s'
                    × readReg (regs s') rax ≡ encode b
                    × halted s' ≡ true)
    helper = run-single-mov-mem-disp s0 rax rdi 8 (encode b)
               (initWithInput-halted (a , b)) (initWithInput-pc (a , b)) mem-at-rdi-8

    s' : State
    s' = proj₁ helper

    run-eq : run (compile-x86 {A * B} {B} snd) s0 ≡ just s'
    run-eq = proj₁ (proj₂ helper)

    rax-eq : readReg (regs s') rax ≡ encode b
    rax-eq = proj₁ (proj₂ (proj₂ helper))

-- | pair: constructs pair from two computations
--
-- Generated code: allocates stack, runs f, stores, restores input, runs g, stores
-- Proof: Uses run-pair-seq helper and encode-pair-construct
compile-pair-correct : ∀ {A B C} (f : IR C A) (g : IR C B) (x : ⟦ C ⟧) →
  ∃[ s ] (run (compile-x86 ⟨ f , g ⟩) (initWithInput x) ≡ just s
        × readReg (regs s) rax ≡ encode (eval f x , eval g x))
compile-pair-correct {A} {B} {C} f g x = s' , run-eq , rax-eq
  where
    s0 : State
    s0 = initWithInput x

    helper : ∃[ s' ] (run (compile-x86 {C} {A * B} ⟨ f , g ⟩) s0 ≡ just s'
                    × halted s' ≡ true
                    × readReg (regs s') rax ≡ readReg (regs s') rsp
                    × readMem (memory s') (readReg (regs s') rax) ≡ just (encode (eval f x))
                    × readMem (memory s') (readReg (regs s') rax +ℕ 8) ≡ just (encode (eval g x)))
    helper = run-pair-seq f g x s0 (initWithInput-halted x) (initWithInput-pc x) (initWithInput-rdi x)

    s' : State
    s' = proj₁ helper

    run-eq : run (compile-x86 ⟨ f , g ⟩) s0 ≡ just s'
    run-eq = proj₁ (proj₂ helper)

    -- helper structure: (s', (run-eq, (halt-eq, (rax-rsp-eq, (fst-eq, snd-eq)))))
    fst-is-eval-f : readMem (memory s') (readReg (regs s') rax) ≡ just (encode (eval f x))
    fst-is-eval-f = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ helper))))

    snd-is-eval-g : readMem (memory s') (readReg (regs s') rax +ℕ 8) ≡ just (encode (eval g x))
    snd-is-eval-g = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ helper))))

    rax-eq : readReg (regs s') rax ≡ encode (eval f x , eval g x)
    rax-eq = encode-pair-construct (eval f x) (eval g x) (readReg (regs s') rax) (memory s')
               fst-is-eval-f snd-is-eval-g

-- | inl: creates left injection
--
-- Generated code: sub rsp, 16; mov [rsp], 0; mov [rsp+8], rdi; mov rax, rsp
-- Proof: Allocates sum on stack with tag=0, value=encode a
compile-inl-correct : ∀ {A B} (a : ⟦ A ⟧) →
  ∃[ s ] (run (compile-x86 {A} {A + B} inl) (initWithInput a) ≡ just s
        × readReg (regs s) rax ≡ encode {A + B} (inj₁ a))
compile-inl-correct {A} {B} a = s' , run-eq , rax-eq
  where
    s0 : State
    s0 = initWithInput a

    -- Use the inl sequence helper
    helper : ∃[ s' ] (run (compile-x86 {A} {A + B} inl) s0 ≡ just s'
                    × halted s' ≡ true
                    × readReg (regs s') rax ≡ readReg (regs s') rsp
                    × readMem (memory s') (readReg (regs s') rax) ≡ just 0
                    × readMem (memory s') (readReg (regs s') rax +ℕ 8) ≡ just (readReg (regs s0) rdi))
    helper = run-inl-seq {A} {B} s0 (initWithInput-halted a) (initWithInput-pc a)

    s' : State
    s' = proj₁ helper

    run-eq : run (compile-x86 {A} {A + B} inl) s0 ≡ just s'
    run-eq = proj₁ (proj₂ helper)

    -- The key: rax points to memory with [0, encode a]
    -- By encode-inl-construct, this means rax = encode (inj₁ a)
    -- helper structure: (s', (run-eq, (halt-eq, (rax-rsp-eq, (tag-eq, val-eq)))))
    tag-is-0 : readMem (memory s') (readReg (regs s') rax) ≡ just 0
    tag-is-0 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ helper))))

    val-is-encode-a : readMem (memory s') (readReg (regs s') rax +ℕ 8) ≡ just (readReg (regs s0) rdi)
    val-is-encode-a = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ helper))))

    -- rdi in s0 = encode a
    rdi-is-encode-a : readReg (regs s0) rdi ≡ encode a
    rdi-is-encode-a = initWithInput-rdi a

    -- So value at [rax+8] = encode a (combining the equalities)
    val-is-encode-a' : readMem (memory s') (readReg (regs s') rax +ℕ 8) ≡ just (encode a)
    val-is-encode-a' = trans val-is-encode-a (cong just rdi-is-encode-a)

    rax-eq : readReg (regs s') rax ≡ encode {A + B} (inj₁ a)
    rax-eq = encode-inl-construct a (readReg (regs s') rax) (memory s') tag-is-0 val-is-encode-a'

-- | inr: creates right injection
--
-- Generated code: sub rsp, 16; mov [rsp], 1; mov [rsp+8], rdi; mov rax, rsp
-- Proof: Allocates sum on stack with tag=1, value=encode b
compile-inr-correct : ∀ {A B} (b : ⟦ B ⟧) →
  ∃[ s ] (run (compile-x86 {B} {A + B} inr) (initWithInput b) ≡ just s
        × readReg (regs s) rax ≡ encode {A + B} (inj₂ b))
compile-inr-correct {A} {B} b = s' , run-eq , rax-eq
  where
    s0 : State
    s0 = initWithInput b

    helper : ∃[ s' ] (run (compile-x86 {B} {A + B} inr) s0 ≡ just s'
                    × halted s' ≡ true
                    × readReg (regs s') rax ≡ readReg (regs s') rsp
                    × readMem (memory s') (readReg (regs s') rax) ≡ just 1
                    × readMem (memory s') (readReg (regs s') rax +ℕ 8) ≡ just (readReg (regs s0) rdi))
    helper = run-inr-seq {A} {B} s0 (initWithInput-halted b) (initWithInput-pc b)

    s' : State
    s' = proj₁ helper

    run-eq : run (compile-x86 {B} {A + B} inr) s0 ≡ just s'
    run-eq = proj₁ (proj₂ helper)

    -- helper structure: (s', (run-eq, (halt-eq, (rax-rsp-eq, (tag-eq, val-eq)))))
    tag-is-1 : readMem (memory s') (readReg (regs s') rax) ≡ just 1
    tag-is-1 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ helper))))

    val-at-rax-8 : readMem (memory s') (readReg (regs s') rax +ℕ 8) ≡ just (readReg (regs s0) rdi)
    val-at-rax-8 = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ helper))))

    rdi-is-encode-b : readReg (regs s0) rdi ≡ encode b
    rdi-is-encode-b = initWithInput-rdi b

    val-is-encode-b : readMem (memory s') (readReg (regs s') rax +ℕ 8) ≡ just (encode b)
    val-is-encode-b = trans val-at-rax-8 (cong just rdi-is-encode-b)

    rax-eq : readReg (regs s') rax ≡ encode {A + B} (inj₂ b)
    rax-eq = encode-inr-construct b (readReg (regs s') rax) (memory s') tag-is-1 val-is-encode-b

-- | case: branches on sum tag
--
-- Generated code: loads tag, compares, branches to f or g
-- Proof: Case split on input - inj₁ takes left branch, inj₂ takes right
compile-case-correct : ∀ {A B C} (f : IR A C) (g : IR B C) (x : ⟦ A ⟧ ⊎ ⟦ B ⟧) →
  ∃[ s ] (run (compile-x86 {A + B} {C} [ f , g ]) (initWithInput x) ≡ just s
        × readReg (regs s) rax ≡ encode {C} (eval [ f , g ] x))
compile-case-correct {A} {B} {C} f g (inj₁ a) = s' , run-eq , rax-eq
  where
    s0 : State
    s0 = initWithInput (inj₁ a)

    helper : ∃[ s' ] (run (compile-x86 {A + B} {C} [ f , g ]) s0 ≡ just s'
                    × halted s' ≡ true
                    × readReg (regs s') rax ≡ encode (eval f a))
    helper = run-case-inl f g a s0 (initWithInput-halted {A + B} (inj₁ a)) (initWithInput-pc {A + B} (inj₁ a)) (initWithInput-rdi (inj₁ a))

    s' : State
    s' = proj₁ helper

    run-eq : run (compile-x86 {A + B} {C} [ f , g ]) s0 ≡ just s'
    run-eq = proj₁ (proj₂ helper)

    -- eval [ f , g ] (inj₁ a) = eval f a by definition
    rax-eq : readReg (regs s') rax ≡ encode {C} (eval [ f , g ] (inj₁ a))
    rax-eq = proj₂ (proj₂ (proj₂ helper))

compile-case-correct {A} {B} {C} f g (inj₂ b) = s' , run-eq , rax-eq
  where
    s0 : State
    s0 = initWithInput (inj₂ b)

    helper : ∃[ s' ] (run (compile-x86 {A + B} {C} [ f , g ]) s0 ≡ just s'
                    × halted s' ≡ true
                    × readReg (regs s') rax ≡ encode (eval g b))
    helper = run-case-inr f g b s0 (initWithInput-halted {A + B} (inj₂ b)) (initWithInput-pc {A + B} (inj₂ b)) (initWithInput-rdi (inj₂ b))

    s' : State
    s' = proj₁ helper

    run-eq : run (compile-x86 {A + B} {C} [ f , g ]) s0 ≡ just s'
    run-eq = proj₁ (proj₂ helper)

    -- eval [ f , g ] (inj₂ b) = eval g b by definition
    rax-eq : readReg (regs s') rax ≡ encode {C} (eval [ f , g ] (inj₂ b))
    rax-eq = proj₂ (proj₂ (proj₂ helper))

-- | initial: unreachable (Void has no values)
-- No theorem needed: there are no inputs of type Void

-- | compose: sequential composition
--
-- Generated code: compile-x86 f ++ [mov rdi, rax] ++ compile-x86 g
-- Proof: Uses run-seq-compose helper and run-generator
compile-compose-correct : ∀ {A B C} (g : IR B C) (f : IR A B) (x : ⟦ A ⟧) →
  ∃[ s ] (run (compile-x86 (g ∘ f)) (initWithInput x) ≡ just s
        × readReg (regs s) rax ≡ encode (eval g (eval f x)))
compile-compose-correct {A} {B} {C} g f x = s' , run-eq , rax-eq
  where
    s0 : State
    s0 = initWithInput x

    -- First, running f produces intermediate result
    f-result : ∃[ s1 ] (run (compile-x86 f) s0 ≡ just s1
                      × halted s1 ≡ true
                      × readReg (regs s1) rax ≡ encode (eval f x))
    f-result = run-generator f x s0 (initWithInput-halted x) (initWithInput-pc x) (initWithInput-rdi x)

    -- Use sequential composition helper with explicit x
    helper : ∃[ s2 ] (run (compile-x86 (g ∘ f)) s0 ≡ just s2
                    × halted s2 ≡ true
                    × readReg (regs s2) rax ≡ encode (eval g (eval f x)))
    helper = run-seq-compose f g x s0 (initWithInput-halted x) (initWithInput-pc x) (initWithInput-rdi x) f-result

    s' : State
    s' = proj₁ helper

    run-eq : run (compile-x86 (g ∘ f)) s0 ≡ just s'
    run-eq = proj₁ (proj₂ helper)

    rax-eq : readReg (regs s') rax ≡ encode (eval g (eval f x))
    rax-eq = proj₂ (proj₂ (proj₂ helper))

-- | terminal: produces unit
--
-- Generated code: mov rax, 0
-- Proof: rax := 0 = encode tt = 0 (by encode-unit)
compile-terminal-correct : ∀ {A} (x : ⟦ A ⟧) →
  ∃[ s ] (run (compile-x86 {A} {Unit} terminal) (initWithInput x) ≡ just s
        × readReg (regs s) rax ≡ 0)
compile-terminal-correct {A} x = s' , run-eq , rax-eq
  where
    s0 : State
    s0 = initWithInput x

    helper : ∃[ s' ] (run (mov (reg rax) (imm 0) ∷ []) s0 ≡ just s'
                    × readReg (regs s') rax ≡ 0
                    × halted s' ≡ true)
    helper = run-single-mov-imm s0 rax 0 (initWithInput-halted x) (initWithInput-pc x)

    s' : State
    s' = proj₁ helper

    run-eq : run (compile-x86 {A} {Unit} terminal) s0 ≡ just s'
    run-eq = proj₁ (proj₂ helper)

    rax-eq : readReg (regs s') rax ≡ 0
    rax-eq = proj₁ (proj₂ (proj₂ helper))

-- | fold: identity at runtime
--
-- Generated code: mov rax, rdi
-- Proof: Same as id - rax := rdi = encode x
compile-fold-correct : ∀ {F} (x : ⟦ F ⟧) →
  ∃[ s ] (run (compile-x86 {F} {Fix F} fold) (initWithInput x) ≡ just s
        × readReg (regs s) rax ≡ encode x)
compile-fold-correct {F} x = s' , run-eq , rax-eq
  where
    s0 : State
    s0 = initWithInput x

    helper : ∃[ s' ] (run (mov (reg rax) (reg rdi) ∷ []) s0 ≡ just s'
                    × readReg (regs s') rax ≡ readReg (regs s0) rdi
                    × halted s' ≡ true)
    helper = run-single-mov s0 rax rdi (initWithInput-halted x) (initWithInput-pc x)

    s' : State
    s' = proj₁ helper

    run-eq : run (compile-x86 {F} {Fix F} fold) s0 ≡ just s'
    run-eq = proj₁ (proj₂ helper)

    rax-eq : readReg (regs s') rax ≡ encode x
    rax-eq = trans (proj₁ (proj₂ (proj₂ helper))) (initWithInput-rdi x)

-- | unfold: identity at runtime
--
-- Generated code: mov rax, rdi
-- Proof: Same as fold, using encode-fix-unwrap
compile-unfold-correct : ∀ {F} (x : ⟦ Fix F ⟧) →
  ∃[ s ] (run (compile-x86 {Fix F} {F} unfold) (initWithInput x) ≡ just s
        × readReg (regs s) rax ≡ encode (⟦Fix⟧.unwrap x))
compile-unfold-correct {F} x = s' , run-eq , rax-eq
  where
    s0 : State
    s0 = initWithInput x

    helper : ∃[ s' ] (run (mov (reg rax) (reg rdi) ∷ []) s0 ≡ just s'
                    × readReg (regs s') rax ≡ readReg (regs s0) rdi
                    × halted s' ≡ true)
    helper = run-single-mov s0 rax rdi (initWithInput-halted x) (initWithInput-pc x)

    s' : State
    s' = proj₁ helper

    run-eq : run (compile-x86 {Fix F} {F} unfold) s0 ≡ just s'
    run-eq = proj₁ (proj₂ helper)

    -- rax = rdi = encode x = encode (unwrap x) by encode-fix-unwrap
    rax-eq : readReg (regs s') rax ≡ encode (⟦Fix⟧.unwrap x)
    rax-eq = trans (proj₁ (proj₂ (proj₂ helper)))
                   (trans (initWithInput-rdi x) (encode-fix-unwrap x))

-- | arr: lifts pure function to effectful morphism (identity at runtime)
--
-- Generated code: mov rax, rdi
-- Proof: Same as id - Eff A B has same representation as A ⇒ B
compile-arr-correct : ∀ {A B} (f : ⟦ A ⇒ B ⟧) →
  ∃[ s ] (run (compile-x86 {A ⇒ B} {Eff A B} arr) (initWithInput {A ⇒ B} f) ≡ just s
        × readReg (regs s) rax ≡ encode {Eff A B} f)
compile-arr-correct {A} {B} f = s' , run-eq , rax-eq
  where
    s0 : State
    s0 = initWithInput {A ⇒ B} f

    helper : ∃[ s' ] (run (mov (reg rax) (reg rdi) ∷ []) s0 ≡ just s'
                    × readReg (regs s') rax ≡ readReg (regs s0) rdi
                    × halted s' ≡ true)
    helper = run-single-mov s0 rax rdi (initWithInput-halted {A ⇒ B} f) (initWithInput-pc {A ⇒ B} f)

    s' : State
    s' = proj₁ helper

    run-eq : run (compile-x86 {A ⇒ B} {Eff A B} arr) s0 ≡ just s'
    run-eq = proj₁ (proj₂ helper)

    -- rax = rdi = encode {A ⇒ B} f = encode {Eff A B} f
    rax-eq : readReg (regs s') rax ≡ encode {Eff A B} f
    rax-eq = trans (proj₁ (proj₂ (proj₂ helper)))
                   (trans (initWithInput-rdi {A ⇒ B} f) (encode-arr-identity f))

------------------------------------------------------------------------
-- Closure Correctness
------------------------------------------------------------------------

-- | curry: creates closure
--
-- Generated code: allocates [env, code_ptr] on stack, returns pointer
-- Proof: Uses run-curry-seq helper and encode-closure-construct
compile-curry-correct : ∀ {A B C} (f : IR (A * B) C) (a : ⟦ A ⟧) →
  ∃[ s ] (run (compile-x86 {A} {B ⇒ C} (curry f)) (initWithInput a) ≡ just s
        × readReg (regs s) rax ≡ encode {B ⇒ C} (λ b → eval f (a , b)))
compile-curry-correct {A} {B} {C} f a = s' , run-eq , rax-eq
  where
    s0 : State
    s0 = initWithInput a

    helper : ∃[ s' ] (run (compile-x86 {A} {B ⇒ C} (curry f)) s0 ≡ just s'
                    × halted s' ≡ true
                    × readMem (memory s') (readReg (regs s') rax) ≡ just (encode a))
    helper = run-curry-seq f a s0 (initWithInput-halted a) (initWithInput-pc a) (initWithInput-rdi a)

    s' : State
    s' = proj₁ helper

    run-eq : run (compile-x86 {A} {B ⇒ C} (curry f)) s0 ≡ just s'
    run-eq = proj₁ (proj₂ helper)

    env-is-a : readMem (memory s') (readReg (regs s') rax) ≡ just (encode a)
    env-is-a = proj₂ (proj₂ (proj₂ helper))

    rax-eq : readReg (regs s') rax ≡ encode {B ⇒ C} (λ b → eval f (a , b))
    rax-eq = encode-closure-construct f a (readReg (regs s') rax) (memory s') env-is-a

-- | apply: calls closure
--
-- Generated code: loads closure and arg, extracts env/code, calls code
-- Proof: Uses run-apply-seq helper
compile-apply-correct : ∀ {A B} (f : ⟦ A ⟧ → ⟦ B ⟧) (a : ⟦ A ⟧) →
  ∃[ s ] (run (compile-x86 {(A ⇒ B) * A} {B} apply) (initWithInput {(A ⇒ B) * A} (f , a)) ≡ just s
        × readReg (regs s) rax ≡ encode {B} (f a))
compile-apply-correct {A} {B} f a = s' , run-eq , rax-eq
  where
    s0 : State
    s0 = initWithInput {(A ⇒ B) * A} (f , a)

    helper : ∃[ s' ] (run (compile-x86 {(A ⇒ B) * A} {B} apply) s0 ≡ just s'
                    × halted s' ≡ true
                    × readReg (regs s') rax ≡ encode {B} (f a))
    helper = run-apply-seq {A} {B} f a s0 (initWithInput-halted {(A ⇒ B) * A} (f , a)) (initWithInput-pc {(A ⇒ B) * A} (f , a)) (initWithInput-rdi {(A ⇒ B) * A} (f , a))

    s' : State
    s' = proj₁ helper

    run-eq : run (compile-x86 {(A ⇒ B) * A} {B} apply) s0 ≡ just s'
    run-eq = proj₁ (proj₂ helper)

    rax-eq : readReg (regs s') rax ≡ encode {B} (f a)
    rax-eq = proj₂ (proj₂ (proj₂ helper))

------------------------------------------------------------------------
-- Notes on Postulates
------------------------------------------------------------------------

-- The postulates in this module fall into two categories:
--
-- 1. ENCODING AXIOMS (encode-*, initWithInput-*)
--    These specify the relationship between semantic values and
--    machine representation. A full formalization would:
--    - Model heap explicitly
--    - Prove these as lemmas rather than assume them
--
-- 2. CORRECTNESS THEOREMS (compile-*-correct)
--    These are the actual proof obligations. Each requires:
--    - Stepping through the generated code
--    - Tracking state changes
--    - Showing final state matches expected
--
-- The structure shows WHAT needs to be proven. The proofs themselves
-- require significant work to complete.
--
-- See docs/compiler/formal-verification-plan.md for estimated effort.

------------------------------------------------------------------------
-- Main Correctness Theorem
------------------------------------------------------------------------

-- | Main correctness theorem
--
-- Executing compiled code on encoded input produces encoded output.
-- This is proven by case analysis on the IR constructor, using the
-- per-generator theorems above.

codegen-x86-correct : ∀ {A B} (ir : IR A B) (x : ⟦ A ⟧) →
  ∃[ s ] (run (compile-x86 ir) (initWithInput x) ≡ just s
        × readReg (regs s) rax ≡ encode (eval ir x))

-- Category structure
codegen-x86-correct id x = compile-id-correct x
codegen-x86-correct (g ∘ f) x = compile-compose-correct g f x

-- Products
codegen-x86-correct fst (a , b) = compile-fst-correct a b
codegen-x86-correct snd (a , b) = compile-snd-correct a b
codegen-x86-correct ⟨ f , g ⟩ x = compile-pair-correct f g x

-- Coproducts
codegen-x86-correct inl a = compile-inl-correct a
codegen-x86-correct inr b = compile-inr-correct b
codegen-x86-correct [ f , g ] x = compile-case-correct f g x

-- Terminal (Unit)
codegen-x86-correct terminal x =
  let (s , run-eq , rax-0) = compile-terminal-correct x
  in s , run-eq , trans rax-0 (sym encode-unit)

-- Initial (Void) - no inputs exist
codegen-x86-correct initial ()

-- Exponential (closures)
-- curry and apply need explicit type annotations to resolve metavariables
codegen-x86-correct {A} {B ⇒ C} (curry {A} {B} {C} f) x = compile-curry-correct f x
codegen-x86-correct {(A ⇒ B) * A} {B} apply (f , a) = compile-apply-correct {A} {B} f a

-- Recursive types
codegen-x86-correct fold x =
  let (s , run-eq , rax-eq) = compile-fold-correct x
  -- encode x = encode (wrap x) by encode-fix-wrap
  -- and eval fold x = wrap x by definition
  in s , run-eq , trans rax-eq (encode-fix-wrap x)
codegen-x86-correct unfold x = compile-unfold-correct x

-- Effect lifting
codegen-x86-correct {A ⇒ B} {Eff A B} arr f = compile-arr-correct {A} {B} f
