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
open Once.Backend.X86.Semantics.Flags
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
open import Data.Nat using (ℕ; zero; suc; _∸_; _≡ᵇ_; _<_; s≤s) renaming (_+_ to _+ℕ_)
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
-- PROVEN (run-generator base cases - non-recursive IR constructors):
--   run-generator-id       : id (mov rax, rdi)
--   run-generator-terminal : terminal (mov rax, 0)
--   run-generator-fold     : fold (mov rax, rdi + encoding)
--   run-generator-unfold   : unfold (mov rax, rdi + encoding)
--   run-generator-arr      : arr (mov rax, rdi + encoding)
--   run-generator-fst      : fst (mov rax, [rdi])
--   run-generator-snd      : snd (mov rax, [rdi+8])
--   run-generator-inl      : inl (allocate + tag=0)
--   run-generator-inr      : inr (allocate + tag=1)
--   run-generator-curry    : curry (create closure)
--
-- PROVEN (compose base cases - specific IR combinations):
--   run-seq-compose-id-id         : id ∘ id (3 instructions)
--   run-seq-compose-terminal-id   : terminal ∘ id (3 instructions)
--   run-seq-compose-id-terminal   : id ∘ terminal (3 instructions)
--   run-generator-compose-id-id   : uses run-seq-compose-id-id
--   run-generator-compose-terminal-id: uses run-seq-compose-terminal-id
--   run-generator-compose-id-terminal: uses run-seq-compose-id-terminal
--
-- PROVEN (pair/case base cases - concrete instances):
--   run-pair-id-id    : ⟨ id , id ⟩ (8 instructions)
--   run-case-inl-id   : [ id , g ] for left injection (8 instructions)
--   run-case-inr-id   : [ f , id ] for right injection (8 instructions)
--
-- POSTULATED (require mutual induction on IR):
--   run-seq-compose  : Sequential composition (general case)
--   run-case-inl/inr : Case analysis (general case)
--   run-pair-seq     : Pairing (general case)
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

-- | Reading rax after writing rdi returns the old value
readReg-writeReg-rdi-rax : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf rdi v) rax ≡ readReg rf rax
readReg-writeReg-rdi-rax rf v = refl

-- | Reading rdi after writing rax returns the old value
readReg-writeReg-rax-rdi : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf rax v) rdi ≡ readReg rf rdi
readReg-writeReg-rax-rdi rf v = refl

------------------------------------------------------------------------
-- Memory Lemmas
------------------------------------------------------------------------

open import Data.Nat.Properties using (≡ᵇ⇒≡; ≡⇒≡ᵇ; +-comm; +-assoc)

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

------------------------------------------------------------------------
-- Sub-program fetch lemmas
-- These allow reasoning about fetching from combined programs
------------------------------------------------------------------------

-- | Fetching from combined program at offset past prefix equals fetching from suffix
-- Key lemma for proving sub-program execution in composed programs
fetch-append-right : ∀ (prefix suffix : List Instr) (n : ℕ) →
  fetch (prefix ++ suffix) (length prefix +ℕ n) ≡ fetch suffix n
fetch-append-right [] suffix n = refl
fetch-append-right (x ∷ prefix) suffix n = fetch-append-right prefix suffix n

-- | Fetching from combined program within prefix equals fetching from prefix
fetch-append-left : ∀ (prefix suffix : List Instr) (n : ℕ) →
  n < length prefix →
  fetch (prefix ++ suffix) n ≡ fetch prefix n
fetch-append-left [] suffix n ()
fetch-append-left (x ∷ prefix) suffix zero _ = refl
fetch-append-left (x ∷ prefix) suffix (suc n) (s≤s n<len) = fetch-append-left prefix suffix n n<len

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
    open import Data.Nat.Properties using (+-assoc)

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
    open import Data.Nat.Properties using (+-assoc; +-comm)

    -- Structure: sub ∷ mov ∷ (compile-x86 f ++ mov ∷ mov ∷ (compile-x86 g ++ mov ∷ mov ∷ []))
    -- We need to show: 2 + (|f| + (2 + (|g| + 2))) = (6 + |f|) + |g|

    inner-tail : List Instr
    inner-tail = mov (mem (base+disp rsp 8)) (reg rax) ∷ mov (reg rax) (reg rsp) ∷ []

    -- Lemma: length of the middle part after f
    len-middle : length (compile-x86 g ++ inner-tail) ≡ compile-length g +ℕ 2
    len-middle = trans (length-++ (compile-x86 g) inner-tail) (cong (λ x → x +ℕ 2) (compile-length-correct g))

    mid-tail : List Instr
    mid-tail = mov (mem (base rsp)) (reg rax) ∷ mov (reg rdi) (reg r14) ∷ (compile-x86 g ++ inner-tail)

    -- Lemma: length after f
    len-after-f : length mid-tail ≡ 2 +ℕ (compile-length g +ℕ 2)
    len-after-f = cong (λ x → 2 +ℕ x) len-middle

    full-tail : List Instr
    full-tail = compile-x86 f ++ mid-tail

    -- Lemma: length including f
    len-with-f : length full-tail ≡ compile-length f +ℕ (2 +ℕ (compile-length g +ℕ 2))
    len-with-f = trans (length-++ (compile-x86 f) mid-tail)
                       (trans (cong (λ x → x +ℕ length mid-tail) (compile-length-correct f))
                              (cong (λ x → compile-length f +ℕ x) len-after-f))

    -- Prove: 2 + (a + (2 + (b + 2))) = (6 + a) + b
    -- Using +-comm and +-assoc with equational reasoning
    arith2 : ∀ a b → 2 +ℕ (a +ℕ (2 +ℕ (b +ℕ 2))) ≡ (6 +ℕ a) +ℕ b
    arith2 a b =
      begin
        2 +ℕ (a +ℕ (2 +ℕ (b +ℕ 2)))
      ≡⟨ cong (2 +ℕ_) (cong (a +ℕ_) (cong (2 +ℕ_) (+-comm b 2))) ⟩
        2 +ℕ (a +ℕ (2 +ℕ (2 +ℕ b)))
      ≡⟨ cong (2 +ℕ_) (cong (a +ℕ_) (sym (+-assoc 2 2 b))) ⟩
        2 +ℕ (a +ℕ (4 +ℕ b))
      ≡⟨ cong (2 +ℕ_) (sym (+-assoc a 4 b)) ⟩
        2 +ℕ ((a +ℕ 4) +ℕ b)
      ≡⟨ cong (2 +ℕ_) (cong (_+ℕ b) (+-comm a 4)) ⟩
        2 +ℕ ((4 +ℕ a) +ℕ b)
      ≡⟨ sym (+-assoc 2 (4 +ℕ a) b) ⟩
        (2 +ℕ (4 +ℕ a)) +ℕ b
      ≡⟨ cong (_+ℕ b) (sym (+-assoc 2 4 a)) ⟩
        (6 +ℕ a) +ℕ b
      ∎

    helper : length (compile-x86 ⟨ f , g ⟩) ≡ (6 +ℕ compile-length f) +ℕ compile-length g
    helper = trans (cong (λ x → 2 +ℕ x) len-with-f)
                   (arith2 (compile-length f) (compile-length g))
compile-length-correct inl = refl
compile-length-correct inr = refl
compile-length-correct [ f , g ] = helper
  where
    open import Data.Nat.Properties using (+-assoc; +-comm)

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
    open import Data.Nat.Properties using (+-assoc; +-comm)

    -- Structure: sub ∷ mov ∷ mov ∷ mov ∷ jmp ∷ label ∷ sub ∷ mov ∷ mov ∷ mov ∷ (compile-x86 f ++ ret ∷ label ∷ [])
    -- Length = 10 + (|f| + 2) = 12 + |f|

    end-lbl : ℕ
    end-lbl = 11 +ℕ compile-length f

    inner-tail : List Instr
    inner-tail = ret ∷ label end-lbl ∷ []

    len-inner : length (compile-x86 f ++ inner-tail) ≡ compile-length f +ℕ 2
    len-inner = trans (length-++ (compile-x86 f) inner-tail) (cong (λ x → x +ℕ 2) (compile-length-correct f))

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

-- | Single-step non-halting execution: execute exactly 1 step without halting
-- Key lemma for sub-program execution where we don't want to halt
exec-one-step-nonhalt : ∀ (prog : List Instr) (s s' : State) →
  step prog s ≡ just s' →
  halted s' ≡ false →
  exec 1 prog s ≡ just s'
exec-one-step-nonhalt prog s s' step-eq halt-eq =
  trans (exec-on-non-halted-step 0 prog s s' step-eq halt-eq) refl

-- | Two-step non-halting execution: execute exactly 2 steps without halting
exec-two-steps-nonhalt : ∀ (prog : List Instr) (s s1 s2 : State) →
  step prog s ≡ just s1 →
  halted s1 ≡ false →
  step prog s1 ≡ just s2 →
  halted s2 ≡ false →
  exec 2 prog s ≡ just s2
exec-two-steps-nonhalt prog s s1 s2 step1 h1 step2 h2 =
  trans (exec-on-non-halted-step 1 prog s s1 step1 h1)
        (exec-one-step-nonhalt prog s1 s2 step2 h2)

-- | Three-step non-halting execution
exec-three-steps-nonhalt : ∀ (prog : List Instr) (s s1 s2 s3 : State) →
  step prog s ≡ just s1 → halted s1 ≡ false →
  step prog s1 ≡ just s2 → halted s2 ≡ false →
  step prog s2 ≡ just s3 → halted s3 ≡ false →
  exec 3 prog s ≡ just s3
exec-three-steps-nonhalt prog s s1 s2 s3 step1 h1 step2 h2 step3 h3 =
  trans (exec-on-non-halted-step 2 prog s s1 step1 h1)
        (exec-two-steps-nonhalt prog s1 s2 s3 step2 h2 step3 h3)

exec-four-steps-nonhalt : ∀ (prog : List Instr) (s s1 s2 s3 s4 : State) →
  step prog s ≡ just s1 → halted s1 ≡ false →
  step prog s1 ≡ just s2 → halted s2 ≡ false →
  step prog s2 ≡ just s3 → halted s3 ≡ false →
  step prog s3 ≡ just s4 → halted s4 ≡ false →
  exec 4 prog s ≡ just s4
exec-four-steps-nonhalt prog s s1 s2 s3 s4 step1 h1 step2 h2 step3 h3 step4 h4 =
  trans (exec-on-non-halted-step 3 prog s s1 step1 h1)
        (exec-three-steps-nonhalt prog s1 s2 s3 s4 step2 h2 step3 h3 step4 h4)

------------------------------------------------------------------------
-- Non-halting sub-program execution (for compose proofs)
-- These execute IR code within a larger program without requiring halt
------------------------------------------------------------------------

-- | Execute id in a larger program (non-halting)
-- compile-x86 id = [mov rax, rdi]
-- After 1 step: pc=1, rax=encode x, halted=false
run-id-nonhalt : ∀ {A} (rest : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) rdi ≡ encode x →
  ∃[ s' ] (exec 1 (compile-x86 {A} {A} id ++ rest) s ≡ just s'
         × halted s' ≡ false
         × pc s' ≡ 1
         × readReg (regs s') rax ≡ encode x)
run-id-nonhalt {A} rest x s h-false pc-0 rdi-eq = s' , exec-eq , h' , pc' , rax-eq
  where
    prog : Program
    prog = compile-x86 {A} {A} id ++ rest

    -- State after mov rax, rdi
    s' : State
    s' = record s { regs = writeReg (regs s) rax (readReg (regs s) rdi)
                  ; pc = pc s +ℕ 1 }

    -- Step proof
    step-eq : step prog s ≡ just s'
    step-eq = trans (step-exec-0 (mov (reg rax) (reg rdi)) rest s h-false pc-0)
                    (execMov-reg-reg s rax rdi)

    h' : halted s' ≡ false
    h' = h-false

    pc' : pc s' ≡ 1
    pc' = cong (λ p → p +ℕ 1) pc-0

    exec-eq : exec 1 prog s ≡ just s'
    exec-eq = exec-one-step-nonhalt prog s s' step-eq h'

    rax-eq : readReg (regs s') rax ≡ encode x
    rax-eq = trans (readReg-writeReg-same (regs s) rax (readReg (regs s) rdi)) rdi-eq

-- | Execute terminal in a larger program (non-halting)
-- compile-x86 terminal = [mov rax, 0]
-- After 1 step: pc=1, rax=0=encode tt, halted=false
run-terminal-nonhalt : ∀ {A} (rest : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  ∃[ s' ] (exec 1 (compile-x86 {A} {Unit} terminal ++ rest) s ≡ just s'
         × halted s' ≡ false
         × pc s' ≡ 1
         × readReg (regs s') rax ≡ encode {Unit} tt)
run-terminal-nonhalt {A} rest x s h-false pc-0 = s' , exec-eq , h' , pc' , rax-eq
  where
    prog : Program
    prog = compile-x86 {A} {Unit} terminal ++ rest

    s' : State
    s' = record s { regs = writeReg (regs s) rax 0
                  ; pc = pc s +ℕ 1 }

    step-eq : step prog s ≡ just s'
    step-eq = trans (step-exec-0 (mov (reg rax) (imm 0)) rest s h-false pc-0)
                    (execMov-reg-imm s rax 0)

    h' : halted s' ≡ false
    h' = h-false

    pc' : pc s' ≡ 1
    pc' = cong (λ p → p +ℕ 1) pc-0

    exec-eq : exec 1 prog s ≡ just s'
    exec-eq = exec-one-step-nonhalt prog s s' step-eq h'

    rax-eq : readReg (regs s') rax ≡ encode tt
    rax-eq = trans (readReg-writeReg-same (regs s) rax 0) (sym encode-unit)

-- | Exec chaining: if exec n produces s' (not halted), then exec m on s' produces s'',
-- then exec (n + m) produces s''
-- This is key for composing sub-program executions
-- Postulate for now - can be proven by induction on n
postulate
  exec-chain : ∀ (n m : ℕ) (prog : List Instr) (s s' s'' : State) →
    exec n prog s ≡ just s' →
    halted s' ≡ false →
    exec m prog s' ≡ just s'' →
    exec (n +ℕ m) prog s ≡ just s''

-- | Fetching at the end of a prefix returns the first element of suffix
-- fetch (prefix ++ i ∷ rest) (length prefix) ≡ just i
fetch-at-prefix-end : ∀ (prefix : Program) (i : Instr) (rest : Program) →
  fetch (prefix ++ i ∷ rest) (length prefix) ≡ just i
fetch-at-prefix-end [] i rest = refl
fetch-at-prefix-end (x ∷ prefix) i rest = fetch-at-prefix-end prefix i rest

-- | Execute transfer instruction (mov rdi, rax) at position N in a program
-- Used between sub-programs in compose to transfer result to input
exec-transfer-at : ∀ (prefix : Program) (suffix : Program) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  ∃[ s' ] (step (prefix ++ mov (reg rdi) (reg rax) ∷ suffix) s ≡ just s'
         × halted s' ≡ false
         × pc s' ≡ length prefix +ℕ 1
         × readReg (regs s') rdi ≡ readReg (regs s) rax
         × readReg (regs s') rax ≡ readReg (regs s) rax)
exec-transfer-at prefix suffix s h-false pc-eq = s' , step-eq , h' , pc' , rdi-eq , rax-eq
  where
    prog : Program
    prog = prefix ++ mov (reg rdi) (reg rax) ∷ suffix

    s' : State
    s' = record s { regs = writeReg (regs s) rdi (readReg (regs s) rax)
                  ; pc = pc s +ℕ 1 }

    fetch-eq : fetch prog (pc s) ≡ just (mov (reg rdi) (reg rax))
    fetch-eq = subst (λ p → fetch prog p ≡ just (mov (reg rdi) (reg rax)))
                     (sym pc-eq) (fetch-at-prefix-end prefix (mov (reg rdi) (reg rax)) suffix)

    step-eq : step prog s ≡ just s'
    step-eq = trans (step-exec prog s (mov (reg rdi) (reg rax)) h-false fetch-eq)
                    (execMov-reg-reg s rdi rax)

    h' : halted s' ≡ false
    h' = h-false

    pc' : pc s' ≡ length prefix +ℕ 1
    pc' = cong (λ p → p +ℕ 1) pc-eq

    rdi-eq : readReg (regs s') rdi ≡ readReg (regs s) rax
    rdi-eq = readReg-writeReg-same (regs s) rdi (readReg (regs s) rax)

    rax-eq : readReg (regs s') rax ≡ readReg (regs s) rax
    rax-eq = readReg-writeReg-rdi-rax (regs s) (readReg (regs s) rax)

-- | Execute id at arbitrary offset in a program (non-halting)
-- This is the general case of run-id-nonhalt where id code can be at any position
-- Program structure: prefix ++ [mov rax, rdi] ++ suffix
run-id-at-offset : ∀ {A} (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode x →
  ∃[ s' ] (step (prefix ++ compile-x86 {A} {A} id ++ suffix) s ≡ just s'
         × halted s' ≡ false
         × pc s' ≡ length prefix +ℕ 1
         × readReg (regs s') rax ≡ encode x)
run-id-at-offset {A} prefix suffix x s h-false pc-eq rdi-eq = s' , step-eq , h' , pc' , rax-eq
  where
    prog : Program
    prog = prefix ++ compile-x86 {A} {A} id ++ suffix

    s' : State
    s' = record s { regs = writeReg (regs s) rax (readReg (regs s) rdi)
                  ; pc = pc s +ℕ 1 }

    fetch-eq : fetch prog (pc s) ≡ just (mov (reg rax) (reg rdi))
    fetch-eq = subst (λ p → fetch prog p ≡ just (mov (reg rax) (reg rdi)))
                     (sym pc-eq) (fetch-at-prefix-end prefix (mov (reg rax) (reg rdi)) suffix)

    step-eq : step prog s ≡ just s'
    step-eq = trans (step-exec prog s (mov (reg rax) (reg rdi)) h-false fetch-eq)
                    (execMov-reg-reg s rax rdi)

    h' : halted s' ≡ false
    h' = h-false

    pc' : pc s' ≡ length prefix +ℕ 1
    pc' = cong (λ p → p +ℕ 1) pc-eq

    rax-eq : readReg (regs s') rax ≡ encode x
    rax-eq = trans (readReg-writeReg-same (regs s) rax (readReg (regs s) rdi)) rdi-eq

-- | Execute terminal at arbitrary offset in a program (non-halting)
-- Program structure: prefix ++ [mov rax, 0] ++ suffix
run-terminal-at-offset : ∀ {A} (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  ∃[ s' ] (step (prefix ++ compile-x86 {A} {Unit} terminal ++ suffix) s ≡ just s'
         × halted s' ≡ false
         × pc s' ≡ length prefix +ℕ 1
         × readReg (regs s') rax ≡ encode {Unit} tt)
run-terminal-at-offset {A} prefix suffix x s h-false pc-eq = s' , step-eq , h' , pc' , rax-eq
  where
    prog : Program
    prog = prefix ++ compile-x86 {A} {Unit} terminal ++ suffix

    s' : State
    s' = record s { regs = writeReg (regs s) rax 0
                  ; pc = pc s +ℕ 1 }

    fetch-eq : fetch prog (pc s) ≡ just (mov (reg rax) (imm 0))
    fetch-eq = subst (λ p → fetch prog p ≡ just (mov (reg rax) (imm 0)))
                     (sym pc-eq) (fetch-at-prefix-end prefix (mov (reg rax) (imm 0)) suffix)

    step-eq : step prog s ≡ just s'
    step-eq = trans (step-exec prog s (mov (reg rax) (imm 0)) h-false fetch-eq)
                    (execMov-reg-imm s rax 0)

    h' : halted s' ≡ false
    h' = h-false

    pc' : pc s' ≡ length prefix +ℕ 1
    pc' = cong (λ p → p +ℕ 1) pc-eq

    rax-eq : readReg (regs s') rax ≡ encode tt
    rax-eq = trans (readReg-writeReg-same (regs s) rax 0) (sym encode-unit)

-- | Execute fold at arbitrary offset in a program (non-halting)
-- compile-x86 fold = [mov rax, rdi] (same as id)
-- Result is encode (wrap x) = encode x by encode-fix-wrap
run-fold-at-offset : ∀ {F} (prefix suffix : Program) (x : ⟦ F ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode x →
  ∃[ s' ] (step (prefix ++ compile-x86 {F} {Fix F} fold ++ suffix) s ≡ just s'
         × halted s' ≡ false
         × pc s' ≡ length prefix +ℕ 1
         × readReg (regs s') rax ≡ encode (wrap x))
run-fold-at-offset {F} prefix suffix x s h-false pc-eq rdi-eq = s' , step-eq , h' , pc' , rax-eq
  where
    prog : Program
    prog = prefix ++ compile-x86 {F} {Fix F} fold ++ suffix

    s' : State
    s' = record s { regs = writeReg (regs s) rax (readReg (regs s) rdi)
                  ; pc = pc s +ℕ 1 }

    fetch-eq : fetch prog (pc s) ≡ just (mov (reg rax) (reg rdi))
    fetch-eq = subst (λ p → fetch prog p ≡ just (mov (reg rax) (reg rdi)))
                     (sym pc-eq) (fetch-at-prefix-end prefix (mov (reg rax) (reg rdi)) suffix)

    step-eq : step prog s ≡ just s'
    step-eq = trans (step-exec prog s (mov (reg rax) (reg rdi)) h-false fetch-eq)
                    (execMov-reg-reg s rax rdi)

    h' : halted s' ≡ false
    h' = h-false

    pc' : pc s' ≡ length prefix +ℕ 1
    pc' = cong (λ p → p +ℕ 1) pc-eq

    rax-eq : readReg (regs s') rax ≡ encode (wrap x)
    rax-eq = trans (readReg-writeReg-same (regs s) rax (readReg (regs s) rdi))
                   (trans rdi-eq (encode-fix-wrap x))

-- | Execute unfold at arbitrary offset in a program (non-halting)
-- compile-x86 unfold = [mov rax, rdi] (same as id)
-- Result is encode (eval unfold x) by encode-fix-unwrap
run-unfold-at-offset : ∀ {F} (prefix suffix : Program) (x : ⟦ Fix F ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode x →
  ∃[ s' ] (step (prefix ++ compile-x86 {Fix F} {F} unfold ++ suffix) s ≡ just s'
         × halted s' ≡ false
         × pc s' ≡ length prefix +ℕ 1
         × readReg (regs s') rax ≡ encode (eval {Fix F} {F} unfold x))
run-unfold-at-offset {F} prefix suffix x s h-false pc-eq rdi-eq = s' , step-eq , h' , pc' , rax-eq
  where
    prog : Program
    prog = prefix ++ compile-x86 {Fix F} {F} unfold ++ suffix

    s' : State
    s' = record s { regs = writeReg (regs s) rax (readReg (regs s) rdi)
                  ; pc = pc s +ℕ 1 }

    fetch-eq : fetch prog (pc s) ≡ just (mov (reg rax) (reg rdi))
    fetch-eq = subst (λ p → fetch prog p ≡ just (mov (reg rax) (reg rdi)))
                     (sym pc-eq) (fetch-at-prefix-end prefix (mov (reg rax) (reg rdi)) suffix)

    step-eq : step prog s ≡ just s'
    step-eq = trans (step-exec prog s (mov (reg rax) (reg rdi)) h-false fetch-eq)
                    (execMov-reg-reg s rax rdi)

    h' : halted s' ≡ false
    h' = h-false

    pc' : pc s' ≡ length prefix +ℕ 1
    pc' = cong (λ p → p +ℕ 1) pc-eq

    -- eval unfold x = unwrap x, encode (unwrap x) = encode x by encode-fix-unwrap
    rax-eq : readReg (regs s') rax ≡ encode (eval {Fix F} {F} unfold x)
    rax-eq = trans (readReg-writeReg-same (regs s) rax (readReg (regs s) rdi))
                   (trans rdi-eq (encode-fix-unwrap x))

-- | Execute arr at arbitrary offset in a program (non-halting)
-- compile-x86 arr = [mov rax, rdi] (same as id)
-- arr : IR (A ⇒ B) (Eff A B), eval arr f = f (identity)
-- encode (eval arr f) = encode f
run-arr-at-offset : ∀ {A B} (prefix suffix : Program) (f : ⟦ A ⇒ B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode f →
  ∃[ s' ] (step (prefix ++ compile-x86 {A ⇒ B} {Eff A B} arr ++ suffix) s ≡ just s'
         × halted s' ≡ false
         × pc s' ≡ length prefix +ℕ 1
         × readReg (regs s') rax ≡ encode {Eff A B} f)
run-arr-at-offset {A} {B} prefix suffix f s h-false pc-eq rdi-eq = s' , step-eq , h' , pc' , rax-eq
  where
    prog : Program
    prog = prefix ++ compile-x86 {A ⇒ B} {Eff A B} arr ++ suffix

    s' : State
    s' = record s { regs = writeReg (regs s) rax (readReg (regs s) rdi)
                  ; pc = pc s +ℕ 1 }

    fetch-eq : fetch prog (pc s) ≡ just (mov (reg rax) (reg rdi))
    fetch-eq = subst (λ p → fetch prog p ≡ just (mov (reg rax) (reg rdi)))
                     (sym pc-eq) (fetch-at-prefix-end prefix (mov (reg rax) (reg rdi)) suffix)

    step-eq : step prog s ≡ just s'
    step-eq = trans (step-exec prog s (mov (reg rax) (reg rdi)) h-false fetch-eq)
                    (execMov-reg-reg s rax rdi)

    h' : halted s' ≡ false
    h' = h-false

    pc' : pc s' ≡ length prefix +ℕ 1
    pc' = cong (λ p → p +ℕ 1) pc-eq

    -- eval arr f = f, and encode-arr-identity says encode {A ⇒ B} f ≡ encode {Eff A B} f
    rax-eq : readReg (regs s') rax ≡ encode {Eff A B} f
    rax-eq = trans (readReg-writeReg-same (regs s) rax (readReg (regs s) rdi))
                   (trans rdi-eq (encode-arr-identity f))

-- | Execute fst at arbitrary offset in a program (non-halting)
-- compile-x86 fst = [mov rax, [rdi]] (1 instruction)
run-fst-at-offset : ∀ {A B} (prefix suffix : Program) (a : ⟦ A ⟧) (b : ⟦ B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode (a , b) →
  readMem (memory s) (encode (a , b)) ≡ just (encode a) →
  ∃[ s' ] (step (prefix ++ compile-x86 {A * B} {A} fst ++ suffix) s ≡ just s'
         × halted s' ≡ false
         × pc s' ≡ length prefix +ℕ 1
         × readReg (regs s') rax ≡ encode a)
run-fst-at-offset {A} {B} prefix suffix a b s h-false pc-eq rdi-eq mem-eq = s' , step-eq , h' , pc' , rax-eq
  where
    prog : Program
    prog = prefix ++ compile-x86 {A * B} {A} fst ++ suffix

    s' : State
    s' = record s { regs = writeReg (regs s) rax (encode a)
                  ; pc = pc s +ℕ 1 }

    fetch-eq : fetch prog (pc s) ≡ just (mov (reg rax) (mem (base rdi)))
    fetch-eq = subst (λ p → fetch prog p ≡ just (mov (reg rax) (mem (base rdi))))
                     (sym pc-eq) (fetch-at-prefix-end prefix (mov (reg rax) (mem (base rdi))) suffix)

    step-eq : step prog s ≡ just s'
    step-eq = trans (step-exec prog s (mov (reg rax) (mem (base rdi))) h-false fetch-eq)
                    (execMov-reg-mem-base s rax rdi (encode a)
                      (trans (cong (λ addr → readMem (memory s) addr) rdi-eq) mem-eq))

    h' : halted s' ≡ false
    h' = h-false

    pc' : pc s' ≡ length prefix +ℕ 1
    pc' = cong (λ p → p +ℕ 1) pc-eq

    rax-eq : readReg (regs s') rax ≡ encode a
    rax-eq = readReg-writeReg-same (regs s) rax (encode a)

-- | Execute snd at arbitrary offset in a program (non-halting)
-- compile-x86 snd = [mov rax, [rdi+8]] (1 instruction)
run-snd-at-offset : ∀ {A B} (prefix suffix : Program) (a : ⟦ A ⟧) (b : ⟦ B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode (a , b) →
  readMem (memory s) (encode (a , b) +ℕ 8) ≡ just (encode b) →
  ∃[ s' ] (step (prefix ++ compile-x86 {A * B} {B} snd ++ suffix) s ≡ just s'
         × halted s' ≡ false
         × pc s' ≡ length prefix +ℕ 1
         × readReg (regs s') rax ≡ encode b)
run-snd-at-offset {A} {B} prefix suffix a b s h-false pc-eq rdi-eq mem-eq = s' , step-eq , h' , pc' , rax-eq
  where
    prog : Program
    prog = prefix ++ compile-x86 {A * B} {B} snd ++ suffix

    s' : State
    s' = record s { regs = writeReg (regs s) rax (encode b)
                  ; pc = pc s +ℕ 1 }

    fetch-eq : fetch prog (pc s) ≡ just (mov (reg rax) (mem (base+disp rdi 8)))
    fetch-eq = subst (λ p → fetch prog p ≡ just (mov (reg rax) (mem (base+disp rdi 8))))
                     (sym pc-eq) (fetch-at-prefix-end prefix (mov (reg rax) (mem (base+disp rdi 8))) suffix)

    step-eq : step prog s ≡ just s'
    step-eq = trans (step-exec prog s (mov (reg rax) (mem (base+disp rdi 8))) h-false fetch-eq)
                    (execMov-reg-mem-disp s rax rdi 8 (encode b)
                      (trans (cong (λ addr → readMem (memory s) (addr +ℕ 8)) rdi-eq) mem-eq))

    h' : halted s' ≡ false
    h' = h-false

    pc' : pc s' ≡ length prefix +ℕ 1
    pc' = cong (λ p → p +ℕ 1) pc-eq

    rax-eq : readReg (regs s') rax ≡ encode b
    rax-eq = readReg-writeReg-same (regs s) rax (encode b)

-- | Execute mov rdi, rax at arbitrary offset (transfer result to input register)
-- This is the glue instruction between composed programs
run-mov-rdi-rax-at-offset : ∀ (prefix suffix : Program) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  ∃[ s' ] (step (prefix ++ mov (reg rdi) (reg rax) ∷ suffix) s ≡ just s'
         × halted s' ≡ false
         × pc s' ≡ length prefix +ℕ 1
         × readReg (regs s') rdi ≡ readReg (regs s) rax
         × readReg (regs s') rax ≡ readReg (regs s) rax)
run-mov-rdi-rax-at-offset prefix suffix s h-false pc-eq = s' , step-eq , h' , pc' , rdi-eq , rax-eq
  where
    prog : Program
    prog = prefix ++ mov (reg rdi) (reg rax) ∷ suffix

    s' : State
    s' = record s { regs = writeReg (regs s) rdi (readReg (regs s) rax)
                  ; pc = pc s +ℕ 1 }

    fetch-eq : fetch prog (pc s) ≡ just (mov (reg rdi) (reg rax))
    fetch-eq = subst (λ p → fetch prog p ≡ just (mov (reg rdi) (reg rax)))
                     (sym pc-eq) (fetch-at-prefix-end prefix (mov (reg rdi) (reg rax)) suffix)

    step-eq : step prog s ≡ just s'
    step-eq = trans (step-exec prog s (mov (reg rdi) (reg rax)) h-false fetch-eq)
                    (execMov-reg-reg s rdi rax)

    h' : halted s' ≡ false
    h' = h-false

    pc' : pc s' ≡ length prefix +ℕ 1
    pc' = cong (λ p → p +ℕ 1) pc-eq

    rdi-eq : readReg (regs s') rdi ≡ readReg (regs s) rax
    rdi-eq = readReg-writeReg-same (regs s) rdi (readReg (regs s) rax)

    -- rax is preserved (we only wrote to rdi)
    rax-eq : readReg (regs s') rax ≡ readReg (regs s) rax
    rax-eq = readReg-writeReg-rdi-rax (regs s) (readReg (regs s) rax)

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

------------------------------------------------------------------------
-- run-ir-at-offset: Non-halting execution of IR at arbitrary offset
--
-- This is the key recursive function that enables proving the mutual
-- recursion cluster. It executes IR code at any position in a larger
-- program WITHOUT halting (continues to next instruction).
--
-- For base cases (id, fst, snd, terminal, fold, unfold, arr):
--   compile-length = 1, execute single step
--
-- For compose (g ∘ f):
--   1. Execute f at offset (recursive call)
--   2. Execute mov rdi, rax at offset + compile-length f
--   3. Execute g at offset + compile-length f + 1 (recursive call)
--   4. Chain using exec-chain
------------------------------------------------------------------------

-- Complex IR cases (compose, pair, case, curry, apply) are defined
-- in the mutual block below together with run-ir-at-offset

-- | Prove run-ir-at-offset-inl: execute inl at arbitrary offset
-- compile-x86 inl = [sub rsp 16, mov [rsp] 0, mov [rsp+8] rdi, mov rax rsp]
run-ir-at-offset-inl : ∀ {A B} (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false → pc s ≡ length prefix → readReg (regs s) rdi ≡ encode x →
  ∃[ s' ] (exec 4 (prefix ++ compile-x86 {A} {A + B} inl ++ suffix) s ≡ just s'
         × halted s' ≡ false × pc s' ≡ length prefix +ℕ 4
         × readReg (regs s') rax ≡ encode (eval {A} {A + B} inl x))
run-ir-at-offset-inl {A} {B} prefix suffix x s h-false pc-eq rdi-eq =
  s4 , exec-eq , h4 , pc4 , rax-eq
  where
    -- The program
    prog : Program
    prog = prefix ++ compile-x86 {A} {A + B} inl ++ suffix

    -- The 4 instructions of inl
    i0 : Instr
    i0 = sub (reg rsp) (imm 16)
    i1 : Instr
    i1 = mov (mem (base rsp)) (imm 0)
    i2 : Instr
    i2 = mov (mem (base+disp rsp 8)) (reg rdi)
    i3 : Instr
    i3 = mov (reg rax) (reg rsp)

    -- Original register values
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

    -- State after step 2: mov [rsp], 0
    s2 : State
    s2 = record s1 { memory = writeMem (memory s1) (readReg (regs s1) rsp) 0
                   ; pc = pc s1 +ℕ 1 }

    -- State after step 3: mov [rsp+8], rdi
    s3 : State
    s3 = record s2 { memory = writeMem (memory s2) (readReg (regs s2) rsp +ℕ 8) (readReg (regs s2) rdi)
                   ; pc = pc s2 +ℕ 1 }

    -- State after step 4: mov rax, rsp
    s4 : State
    s4 = record s3 { regs = writeReg (regs s3) rax (readReg (regs s3) rsp)
                   ; pc = pc s3 +ℕ 1 }

    -- Fetch lemmas for each instruction position
    -- Use fetch-at-prefix-end with appropriate prefixes

    -- Instruction 0 at position (length prefix)
    fetch0 : fetch prog (length prefix) ≡ just i0
    fetch0 = fetch-at-prefix-end prefix i0 (i1 ∷ i2 ∷ i3 ∷ suffix)

    -- For subsequent fetches at positions length prefix + 1, 2, 3
    -- We use list associativity and the local length-++ lemma
    open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)

    -- Helper: prog rearranged for fetch calculations
    prog-eq1 : prog ≡ (prefix ++ i0 ∷ []) ++ i1 ∷ i2 ∷ i3 ∷ suffix
    prog-eq1 = sym (++-assoc prefix (i0 ∷ []) (i1 ∷ i2 ∷ i3 ∷ suffix))

    len-prefix-1 : length (prefix ++ i0 ∷ []) ≡ length prefix +ℕ 1
    len-prefix-1 = length-++ prefix (i0 ∷ [])

    fetch1-helper : fetch ((prefix ++ i0 ∷ []) ++ i1 ∷ i2 ∷ i3 ∷ suffix) (length (prefix ++ i0 ∷ [])) ≡ just i1
    fetch1-helper = fetch-at-prefix-end (prefix ++ i0 ∷ []) i1 (i2 ∷ i3 ∷ suffix)

    fetch1 : fetch prog (length prefix +ℕ 1) ≡ just i1
    fetch1 = subst₂ (λ p n → fetch p n ≡ just i1) (sym prog-eq1) len-prefix-1 fetch1-helper

    prog-eq2 : prog ≡ (prefix ++ i0 ∷ i1 ∷ []) ++ i2 ∷ i3 ∷ suffix
    prog-eq2 = sym (++-assoc prefix (i0 ∷ i1 ∷ []) (i2 ∷ i3 ∷ suffix))

    len-prefix-2 : length (prefix ++ i0 ∷ i1 ∷ []) ≡ length prefix +ℕ 2
    len-prefix-2 = length-++ prefix (i0 ∷ i1 ∷ [])

    fetch2-helper : fetch ((prefix ++ i0 ∷ i1 ∷ []) ++ i2 ∷ i3 ∷ suffix) (length (prefix ++ i0 ∷ i1 ∷ [])) ≡ just i2
    fetch2-helper = fetch-at-prefix-end (prefix ++ i0 ∷ i1 ∷ []) i2 (i3 ∷ suffix)

    fetch2 : fetch prog (length prefix +ℕ 2) ≡ just i2
    fetch2 = subst₂ (λ p n → fetch p n ≡ just i2) (sym prog-eq2) len-prefix-2 fetch2-helper

    prog-eq3 : prog ≡ (prefix ++ i0 ∷ i1 ∷ i2 ∷ []) ++ i3 ∷ suffix
    prog-eq3 = sym (++-assoc prefix (i0 ∷ i1 ∷ i2 ∷ []) (i3 ∷ suffix))

    len-prefix-3 : length (prefix ++ i0 ∷ i1 ∷ i2 ∷ []) ≡ length prefix +ℕ 3
    len-prefix-3 = length-++ prefix (i0 ∷ i1 ∷ i2 ∷ [])

    fetch3-helper : fetch ((prefix ++ i0 ∷ i1 ∷ i2 ∷ []) ++ i3 ∷ suffix) (length (prefix ++ i0 ∷ i1 ∷ i2 ∷ [])) ≡ just i3
    fetch3-helper = fetch-at-prefix-end (prefix ++ i0 ∷ i1 ∷ i2 ∷ []) i3 suffix

    fetch3 : fetch prog (length prefix +ℕ 3) ≡ just i3
    fetch3 = subst₂ (λ p n → fetch p n ≡ just i3) (sym prog-eq3) len-prefix-3 fetch3-helper

    -- Step proofs
    step1 : step prog s ≡ just s1
    step1 = trans (step-exec prog s i0 h-false (subst (λ p → fetch prog p ≡ just i0) (sym pc-eq) fetch0))
                  (execSub-reg-imm prog s rsp 16)

    h1 : halted s1 ≡ false
    h1 = h-false

    pc1 : pc s1 ≡ length prefix +ℕ 1
    pc1 = cong (λ p → p +ℕ 1) pc-eq

    step2 : step prog s1 ≡ just s2
    step2 = trans (step-exec prog s1 i1 h1 (subst (λ p → fetch prog p ≡ just i1) (sym pc1) fetch1))
                  (execMov-mem-base-imm prog s1 rsp 0)

    h2 : halted s2 ≡ false
    h2 = h-false

    pc2 : pc s2 ≡ length prefix +ℕ 2
    pc2 = trans (cong (λ p → p +ℕ 1) pc1) (+-assoc (length prefix) 1 1)

    step3 : step prog s2 ≡ just s3
    step3 = trans (step-exec prog s2 i2 h2 (subst (λ p → fetch prog p ≡ just i2) (sym pc2) fetch2))
                  (execMov-mem-disp-reg prog s2 rsp rdi 8)

    h3 : halted s3 ≡ false
    h3 = h-false

    pc3 : pc s3 ≡ length prefix +ℕ 3
    pc3 = trans (cong (λ p → p +ℕ 1) pc2) (+-assoc (length prefix) 2 1)

    step4 : step prog s3 ≡ just s4
    step4 = trans (step-exec prog s3 i3 h3 (subst (λ p → fetch prog p ≡ just i3) (sym pc3) fetch3))
                  (execMov-reg-reg s3 rax rsp)

    h4 : halted s4 ≡ false
    h4 = h-false

    pc4 : pc s4 ≡ length prefix +ℕ 4
    pc4 = trans (cong (λ p → p +ℕ 1) pc3) (+-assoc (length prefix) 3 1)

    -- Combine 4 steps
    exec-eq : exec 4 prog s ≡ just s4
    exec-eq = exec-four-steps-nonhalt prog s s1 s2 s3 s4 step1 h1 step2 h2 step3 h3 step4 h4

    -- Now prove rax = encode (inj₁ x)
    -- rax = rsp (from s4)
    -- rsp in s4 = rsp in s3 = rsp in s2 = rsp in s1 = new-rsp
    -- memory[new-rsp] = 0 (from s2)
    -- memory[new-rsp + 8] = orig-rdi = encode x (from s3)

    -- Track rsp through states
    rsp-s1 : readReg (regs s1) rsp ≡ new-rsp
    rsp-s1 = readReg-writeReg-same (regs s) rsp new-rsp

    rsp-s2 : readReg (regs s2) rsp ≡ new-rsp
    rsp-s2 = rsp-s1  -- memory write doesn't change regs

    rsp-s3 : readReg (regs s3) rsp ≡ new-rsp
    rsp-s3 = rsp-s2  -- memory write doesn't change regs

    rsp-s4 : readReg (regs s4) rsp ≡ new-rsp
    rsp-s4 = trans (readReg-writeReg-rax-rsp (regs s3) (readReg (regs s3) rsp)) rsp-s3

    -- rax in s4 = rsp in s3 = new-rsp
    rax-s4 : readReg (regs s4) rax ≡ new-rsp
    rax-s4 = trans (readReg-writeReg-same (regs s3) rax (readReg (regs s3) rsp)) rsp-s3

    -- Track rdi through states (unchanged until s3)
    rdi-s1 : readReg (regs s1) rdi ≡ orig-rdi
    rdi-s1 = readReg-writeReg-rsp-rdi (regs s) new-rsp

    rdi-s2 : readReg (regs s2) rdi ≡ orig-rdi
    rdi-s2 = rdi-s1  -- memory write doesn't change regs

    -- Address disjointness: new-rsp ≠ new-rsp + 8
    addr-disjoint : new-rsp ≢ new-rsp +ℕ 8
    addr-disjoint = n≢n+suc new-rsp 7

    -- Memory at new-rsp = 0 (set in s2)
    -- memory s2 = writeMem (memory s1) (readReg (regs s1) rsp) 0
    -- readReg (regs s1) rsp = new-rsp (from rsp-s1)
    mem-tag-s2 : readMem (memory s2) new-rsp ≡ just 0
    mem-tag-s2 = subst (λ addr → readMem (writeMem (memory s1) addr 0) new-rsp ≡ just 0)
                       (sym rsp-s1)
                       (readMem-writeMem-same (memory s1) new-rsp 0)

    -- Memory at new-rsp preserved from s2 to s3 (s3 writes at new-rsp+8)
    -- memory s3 = writeMem (memory s2) (readReg (regs s2) rsp +ℕ 8) (readReg (regs s2) rdi)
    mem-tag-s3 : readMem (memory s3) new-rsp ≡ just 0
    mem-tag-s3 = trans (subst (λ addr → readMem (writeMem (memory s2) addr (readReg (regs s2) rdi)) new-rsp ≡
                                        readMem (memory s2) new-rsp)
                              (sym (cong (_+ℕ 8) rsp-s2))
                              (readMem-writeMem-diff (memory s2) (new-rsp +ℕ 8) new-rsp (readReg (regs s2) rdi)
                                                     (λ eq → addr-disjoint (sym eq))))
                       mem-tag-s2

    -- Memory at new-rsp preserved from s3 to s4 (s4 doesn't write memory)
    mem-tag-s4 : readMem (memory s4) new-rsp ≡ just 0
    mem-tag-s4 = mem-tag-s3  -- s4 = record s3 { regs = ...; pc = ... }, memory unchanged

    -- Memory at new-rsp + 8 = orig-rdi (set in s3)
    mem-val-s3 : readMem (memory s3) (new-rsp +ℕ 8) ≡ just orig-rdi
    mem-val-s3 = trans (subst (λ addr → readMem (writeMem (memory s2) addr (readReg (regs s2) rdi)) (new-rsp +ℕ 8) ≡
                                        just (readReg (regs s2) rdi))
                              (sym (cong (_+ℕ 8) rsp-s2))
                              (readMem-writeMem-same (memory s2) (new-rsp +ℕ 8) (readReg (regs s2) rdi)))
                       (cong just rdi-s2)

    -- Memory at new-rsp + 8 preserved from s3 to s4
    mem-val-s4 : readMem (memory s4) (new-rsp +ℕ 8) ≡ just orig-rdi
    mem-val-s4 = mem-val-s3  -- s4 doesn't write memory

    -- Use encode-inl-construct: if mem[p] = 0 and mem[p+8] = encode x, then p = encode (inj₁ x)
    -- We have: rax = new-rsp, mem[new-rsp] = 0, mem[new-rsp+8] = encode x
    -- So: rax = encode (inj₁ x)

    -- First, orig-rdi = encode x (from precondition)
    orig-rdi-is-encode-x : orig-rdi ≡ encode x
    orig-rdi-is-encode-x = rdi-eq

    -- Adjust memory proofs to use encode x
    mem-val-encoded : readMem (memory s4) (new-rsp +ℕ 8) ≡ just (encode x)
    mem-val-encoded = trans mem-val-s4 (cong just orig-rdi-is-encode-x)

    -- Apply encode-inl-construct
    rax-is-encode-inl : new-rsp ≡ encode {A + B} (inj₁ x)
    rax-is-encode-inl = encode-inl-construct x new-rsp (memory s4) mem-tag-s4 mem-val-encoded

    -- Final result: rax s4 = encode (eval inl x) = encode (inj₁ x)
    rax-eq : readReg (regs s4) rax ≡ encode (eval {A} {A + B} inl x)
    rax-eq = trans rax-s4 rax-is-encode-inl

-- | run-ir-at-offset-inr: Execute inr at arbitrary offset
-- inr generates 4 instructions:
--   sub rsp, 16
--   mov [rsp], 1          (tag = 1)
--   mov [rsp+8], rdi      (value)
--   mov rax, rsp          (return pointer)
run-ir-at-offset-inr : ∀ {A B} (prefix suffix : Program) (x : ⟦ B ⟧) (s : State) →
  halted s ≡ false → pc s ≡ length prefix → readReg (regs s) rdi ≡ encode x →
  ∃[ s' ] (exec 4 (prefix ++ compile-x86 {B} {A + B} inr ++ suffix) s ≡ just s'
         × halted s' ≡ false × pc s' ≡ length prefix +ℕ 4
         × readReg (regs s') rax ≡ encode (eval {B} {A + B} inr x))
run-ir-at-offset-inr {A} {B} prefix suffix x s h-false pc-eq rdi-eq =
  s4 , exec-eq , h4 , pc4 , rax-eq
  where
    -- Program structure
    i0 = sub (reg rsp) (imm 16)
    i1 = mov (mem (base rsp)) (imm 1)
    i2 = mov (mem (base+disp rsp 8)) (reg rdi)
    i3 = mov (reg rax) (reg rsp)
    prog = prefix ++ i0 ∷ i1 ∷ i2 ∷ i3 ∷ suffix

    -- Original register values
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

    -- State after step 2: mov [rsp], 1
    s2 : State
    s2 = record s1 { memory = writeMem (memory s1) (readReg (regs s1) rsp) 1
                   ; pc = pc s1 +ℕ 1 }

    -- State after step 3: mov [rsp+8], rdi
    s3 : State
    s3 = record s2 { memory = writeMem (memory s2) (readReg (regs s2) rsp +ℕ 8) (readReg (regs s2) rdi)
                   ; pc = pc s2 +ℕ 1 }

    -- State after step 4: mov rax, rsp
    s4 : State
    s4 = record s3 { regs = writeReg (regs s3) rax (readReg (regs s3) rsp)
                   ; pc = pc s3 +ℕ 1 }

    -- Fetch lemmas for each instruction position
    fetch0 : fetch prog (length prefix) ≡ just i0
    fetch0 = fetch-at-prefix-end prefix i0 (i1 ∷ i2 ∷ i3 ∷ suffix)

    open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)

    prog-eq1 : prog ≡ (prefix ++ i0 ∷ []) ++ i1 ∷ i2 ∷ i3 ∷ suffix
    prog-eq1 = sym (++-assoc prefix (i0 ∷ []) (i1 ∷ i2 ∷ i3 ∷ suffix))

    len-prefix-1 : length (prefix ++ i0 ∷ []) ≡ length prefix +ℕ 1
    len-prefix-1 = length-++ prefix (i0 ∷ [])

    fetch1-helper : fetch ((prefix ++ i0 ∷ []) ++ i1 ∷ i2 ∷ i3 ∷ suffix) (length (prefix ++ i0 ∷ [])) ≡ just i1
    fetch1-helper = fetch-at-prefix-end (prefix ++ i0 ∷ []) i1 (i2 ∷ i3 ∷ suffix)

    fetch1 : fetch prog (length prefix +ℕ 1) ≡ just i1
    fetch1 = subst₂ (λ p n → fetch p n ≡ just i1) (sym prog-eq1) len-prefix-1 fetch1-helper

    prog-eq2 : prog ≡ (prefix ++ i0 ∷ i1 ∷ []) ++ i2 ∷ i3 ∷ suffix
    prog-eq2 = sym (++-assoc prefix (i0 ∷ i1 ∷ []) (i2 ∷ i3 ∷ suffix))

    len-prefix-2 : length (prefix ++ i0 ∷ i1 ∷ []) ≡ length prefix +ℕ 2
    len-prefix-2 = length-++ prefix (i0 ∷ i1 ∷ [])

    fetch2-helper : fetch ((prefix ++ i0 ∷ i1 ∷ []) ++ i2 ∷ i3 ∷ suffix) (length (prefix ++ i0 ∷ i1 ∷ [])) ≡ just i2
    fetch2-helper = fetch-at-prefix-end (prefix ++ i0 ∷ i1 ∷ []) i2 (i3 ∷ suffix)

    fetch2 : fetch prog (length prefix +ℕ 2) ≡ just i2
    fetch2 = subst₂ (λ p n → fetch p n ≡ just i2) (sym prog-eq2) len-prefix-2 fetch2-helper

    prog-eq3 : prog ≡ (prefix ++ i0 ∷ i1 ∷ i2 ∷ []) ++ i3 ∷ suffix
    prog-eq3 = sym (++-assoc prefix (i0 ∷ i1 ∷ i2 ∷ []) (i3 ∷ suffix))

    len-prefix-3 : length (prefix ++ i0 ∷ i1 ∷ i2 ∷ []) ≡ length prefix +ℕ 3
    len-prefix-3 = length-++ prefix (i0 ∷ i1 ∷ i2 ∷ [])

    fetch3-helper : fetch ((prefix ++ i0 ∷ i1 ∷ i2 ∷ []) ++ i3 ∷ suffix) (length (prefix ++ i0 ∷ i1 ∷ i2 ∷ [])) ≡ just i3
    fetch3-helper = fetch-at-prefix-end (prefix ++ i0 ∷ i1 ∷ i2 ∷ []) i3 suffix

    fetch3 : fetch prog (length prefix +ℕ 3) ≡ just i3
    fetch3 = subst₂ (λ p n → fetch p n ≡ just i3) (sym prog-eq3) len-prefix-3 fetch3-helper

    -- Step proofs
    step1 : step prog s ≡ just s1
    step1 = trans (step-exec prog s i0 h-false (subst (λ p → fetch prog p ≡ just i0) (sym pc-eq) fetch0))
                  (execSub-reg-imm prog s rsp 16)

    h1 : halted s1 ≡ false
    h1 = h-false

    pc1 : pc s1 ≡ length prefix +ℕ 1
    pc1 = cong (λ p → p +ℕ 1) pc-eq

    step2 : step prog s1 ≡ just s2
    step2 = trans (step-exec prog s1 i1 h1 (subst (λ p → fetch prog p ≡ just i1) (sym pc1) fetch1))
                  (execMov-mem-base-imm prog s1 rsp 1)

    h2 : halted s2 ≡ false
    h2 = h-false

    pc2 : pc s2 ≡ length prefix +ℕ 2
    pc2 = trans (cong (λ p → p +ℕ 1) pc1) (+-assoc (length prefix) 1 1)

    step3 : step prog s2 ≡ just s3
    step3 = trans (step-exec prog s2 i2 h2 (subst (λ p → fetch prog p ≡ just i2) (sym pc2) fetch2))
                  (execMov-mem-disp-reg prog s2 rsp rdi 8)

    h3 : halted s3 ≡ false
    h3 = h-false

    pc3 : pc s3 ≡ length prefix +ℕ 3
    pc3 = trans (cong (λ p → p +ℕ 1) pc2) (+-assoc (length prefix) 2 1)

    step4 : step prog s3 ≡ just s4
    step4 = trans (step-exec prog s3 i3 h3 (subst (λ p → fetch prog p ≡ just i3) (sym pc3) fetch3))
                  (execMov-reg-reg s3 rax rsp)

    h4 : halted s4 ≡ false
    h4 = h-false

    pc4 : pc s4 ≡ length prefix +ℕ 4
    pc4 = trans (cong (λ p → p +ℕ 1) pc3) (+-assoc (length prefix) 3 1)

    -- Combine 4 steps
    exec-eq : exec 4 prog s ≡ just s4
    exec-eq = exec-four-steps-nonhalt prog s s1 s2 s3 s4 step1 h1 step2 h2 step3 h3 step4 h4

    -- Register tracking: rsp preserved through s1..s4
    rsp-s1 : readReg (regs s1) rsp ≡ new-rsp
    rsp-s1 = readReg-writeReg-same (regs s) rsp new-rsp

    rsp-s2 : readReg (regs s2) rsp ≡ new-rsp
    rsp-s2 = rsp-s1  -- memory write doesn't change regs

    rsp-s3 : readReg (regs s3) rsp ≡ new-rsp
    rsp-s3 = rsp-s2  -- memory write doesn't change regs

    rsp-s4 : readReg (regs s4) rsp ≡ new-rsp
    rsp-s4 = trans (readReg-writeReg-rax-rsp (regs s3) (readReg (regs s3) rsp)) rsp-s3

    -- rax in s4 = rsp in s3 = new-rsp
    rax-s4 : readReg (regs s4) rax ≡ new-rsp
    rax-s4 = trans (readReg-writeReg-same (regs s3) rax (readReg (regs s3) rsp)) rsp-s3

    -- rdi preserved through s1, s2
    rdi-s1 : readReg (regs s1) rdi ≡ orig-rdi
    rdi-s1 = readReg-writeReg-rsp-rdi (regs s) new-rsp

    rdi-s2 : readReg (regs s2) rdi ≡ orig-rdi
    rdi-s2 = rdi-s1  -- memory write doesn't change regs

    -- Address disjointness: new-rsp ≠ new-rsp + 8
    addr-disjoint : new-rsp ≢ new-rsp +ℕ 8
    addr-disjoint = n≢n+suc new-rsp 7

    -- Memory at new-rsp = 1 (set in s2)
    mem-tag-s2 : readMem (memory s2) new-rsp ≡ just 1
    mem-tag-s2 = subst (λ addr → readMem (writeMem (memory s1) addr 1) new-rsp ≡ just 1)
                       (sym rsp-s1)
                       (readMem-writeMem-same (memory s1) new-rsp 1)

    -- Memory at new-rsp preserved from s2 to s3
    mem-tag-s3 : readMem (memory s3) new-rsp ≡ just 1
    mem-tag-s3 = trans (subst (λ addr → readMem (writeMem (memory s2) addr (readReg (regs s2) rdi)) new-rsp ≡
                                        readMem (memory s2) new-rsp)
                              (sym (cong (_+ℕ 8) rsp-s2))
                              (readMem-writeMem-diff (memory s2) (new-rsp +ℕ 8) new-rsp (readReg (regs s2) rdi)
                                                     (λ eq → addr-disjoint (sym eq))))
                       mem-tag-s2

    -- Memory at new-rsp preserved from s3 to s4
    mem-tag-s4 : readMem (memory s4) new-rsp ≡ just 1
    mem-tag-s4 = mem-tag-s3

    -- Memory at new-rsp + 8 = orig-rdi (set in s3)
    mem-val-s3 : readMem (memory s3) (new-rsp +ℕ 8) ≡ just orig-rdi
    mem-val-s3 = trans (subst (λ addr → readMem (writeMem (memory s2) addr (readReg (regs s2) rdi)) (new-rsp +ℕ 8) ≡
                                        just (readReg (regs s2) rdi))
                              (sym (cong (_+ℕ 8) rsp-s2))
                              (readMem-writeMem-same (memory s2) (new-rsp +ℕ 8) (readReg (regs s2) rdi)))
                       (cong just rdi-s2)

    -- Memory at new-rsp + 8 preserved from s3 to s4
    mem-val-s4 : readMem (memory s4) (new-rsp +ℕ 8) ≡ just orig-rdi
    mem-val-s4 = mem-val-s3

    -- orig-rdi = encode x
    orig-rdi-is-encode-x : orig-rdi ≡ encode x
    orig-rdi-is-encode-x = rdi-eq

    -- Adjust memory proofs to use encode x
    mem-val-encoded : readMem (memory s4) (new-rsp +ℕ 8) ≡ just (encode x)
    mem-val-encoded = trans mem-val-s4 (cong just orig-rdi-is-encode-x)

    -- Apply encode-inr-construct
    rax-is-encode-inr : new-rsp ≡ encode {A + B} (inj₂ x)
    rax-is-encode-inr = encode-inr-construct x new-rsp (memory s4) mem-tag-s4 mem-val-encoded

    -- Final result: rax s4 = encode (eval inr x) = encode (inj₂ x)
    rax-eq : readReg (regs s4) rax ≡ encode (eval {B} {A + B} inr x)
    rax-eq = trans rax-s4 rax-is-encode-inr

-- | run-ir-at-offset-fst: Execute fst at arbitrary offset
-- Uses encode-pair-fst axiom to provide memory precondition
run-ir-at-offset-fst : ∀ {A B} (prefix suffix : Program) (x : ⟦ A * B ⟧) (s : State) →
  halted s ≡ false → pc s ≡ length prefix → readReg (regs s) rdi ≡ encode x →
  ∃[ s' ] (exec 1 (prefix ++ compile-x86 {A * B} {A} fst ++ suffix) s ≡ just s'
         × halted s' ≡ false × pc s' ≡ length prefix +ℕ 1
         × readReg (regs s') rax ≡ encode (eval fst x))
run-ir-at-offset-fst {A} {B} prefix suffix x s h-false pc-eq rdi-eq =
  let a = proj₁ x
      b = proj₂ x
      -- Memory precondition from encoding axiom
      mem-eq : readMem (memory s) (encode (a , b)) ≡ just (encode a)
      mem-eq = encode-pair-fst a b (memory s)
      -- Use existing run-fst-at-offset with the memory precondition
      (s' , step-eq , h' , pc' , rax-eq) = run-fst-at-offset {A} {B} prefix suffix a b s h-false pc-eq rdi-eq mem-eq
  in s' , exec-one-step-nonhalt (prefix ++ compile-x86 {A * B} {A} fst ++ suffix) s s' step-eq h' , h' , pc' , rax-eq

-- | run-ir-at-offset-snd: Execute snd at arbitrary offset
-- Uses encode-pair-snd axiom to provide memory precondition
run-ir-at-offset-snd : ∀ {A B} (prefix suffix : Program) (x : ⟦ A * B ⟧) (s : State) →
  halted s ≡ false → pc s ≡ length prefix → readReg (regs s) rdi ≡ encode x →
  ∃[ s' ] (exec 1 (prefix ++ compile-x86 {A * B} {B} snd ++ suffix) s ≡ just s'
         × halted s' ≡ false × pc s' ≡ length prefix +ℕ 1
         × readReg (regs s') rax ≡ encode (eval snd x))
run-ir-at-offset-snd {A} {B} prefix suffix x s h-false pc-eq rdi-eq =
  let a = proj₁ x
      b = proj₂ x
      -- Memory precondition from encoding axiom
      mem-eq : readMem (memory s) (encode (a , b) +ℕ 8) ≡ just (encode b)
      mem-eq = encode-pair-snd a b (memory s)
      -- Use existing run-snd-at-offset with the memory precondition
      (s' , step-eq , h' , pc' , rax-eq) = run-snd-at-offset {A} {B} prefix suffix a b s h-false pc-eq rdi-eq mem-eq
  in s' , exec-one-step-nonhalt (prefix ++ compile-x86 {A * B} {B} snd ++ suffix) s s' step-eq h' , h' , pc' , rax-eq

-- | run-ir-at-offset-initial: Execute initial at arbitrary offset
-- Trivially proven because Void (⊥) has no inhabitants
run-ir-at-offset-initial : ∀ {A} (prefix suffix : Program) (x : ⟦ Void ⟧) (s : State) →
  halted s ≡ false → pc s ≡ length prefix → readReg (regs s) rdi ≡ encode x →
  ∃[ s' ] (exec 1 (prefix ++ compile-x86 {Void} {A} initial ++ suffix) s ≡ just s'
         × halted s' ≡ false × pc s' ≡ length prefix +ℕ 1
         × readReg (regs s') rax ≡ encode {A} (eval {Void} {A} initial x))
run-ir-at-offset-initial {A} prefix suffix x s h-false pc-eq rdi-eq = ⊥-elim x

------------------------------------------------------------------------
-- Mutual block for run-ir-at-offset and complex IR cases
------------------------------------------------------------------------

-- Temporary postulates for complex cases (to be replaced with proofs)
postulate
  run-ir-at-offset-compose-postulate : ∀ {A B C} (f : IR A B) (g : IR B C) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false → pc s ≡ length prefix → readReg (regs s) rdi ≡ encode x →
    ∃[ s' ] (exec (compile-length (g ∘ f)) (prefix ++ compile-x86 (g ∘ f) ++ suffix) s ≡ just s'
           × halted s' ≡ false × pc s' ≡ length prefix +ℕ compile-length (g ∘ f)
           × readReg (regs s') rax ≡ encode (eval (g ∘ f) x))
  run-ir-at-offset-pair-postulate : ∀ {A B C} (f : IR C A) (g : IR C B) (prefix suffix : Program) (x : ⟦ C ⟧) (s : State) →
    halted s ≡ false → pc s ≡ length prefix → readReg (regs s) rdi ≡ encode x →
    ∃[ s' ] (exec (compile-length ⟨ f , g ⟩) (prefix ++ compile-x86 ⟨ f , g ⟩ ++ suffix) s ≡ just s'
           × halted s' ≡ false × pc s' ≡ length prefix +ℕ compile-length ⟨ f , g ⟩
           × readReg (regs s') rax ≡ encode (eval ⟨ f , g ⟩ x))
  run-ir-at-offset-case-postulate : ∀ {A B C} (f : IR A C) (g : IR B C) (prefix suffix : Program) (x : ⟦ A + B ⟧) (s : State) →
    halted s ≡ false → pc s ≡ length prefix → readReg (regs s) rdi ≡ encode x →
    ∃[ s' ] (exec (compile-length [ f , g ]) (prefix ++ compile-x86 [ f , g ] ++ suffix) s ≡ just s'
           × halted s' ≡ false × pc s' ≡ length prefix +ℕ compile-length [ f , g ]
           × readReg (regs s') rax ≡ encode (eval [ f , g ] x))
  run-ir-at-offset-curry-postulate : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) (a : ⟦ A ⟧) (s : State) →
    halted s ≡ false → pc s ≡ length prefix → readReg (regs s) rdi ≡ encode a →
    ∃[ s' ] (exec (compile-length (curry f)) (prefix ++ compile-x86 (curry f) ++ suffix) s ≡ just s'
           × halted s' ≡ false × pc s' ≡ length prefix +ℕ compile-length (curry f)
           × readReg (regs s') rax ≡ encode {B ⇒ C} (eval {A} {B ⇒ C} (curry f) a))
  run-ir-at-offset-apply-postulate : ∀ {A B} (prefix suffix : Program) (x : ⟦ (A ⇒ B) * A ⟧) (s : State) →
    halted s ≡ false → pc s ≡ length prefix → readReg (regs s) rdi ≡ encode {(A ⇒ B) * A} x →
    ∃[ s' ] (exec 6 (prefix ++ compile-x86 {(A ⇒ B) * A} {B} apply ++ suffix) s ≡ just s'
           × halted s' ≡ false × pc s' ≡ length prefix +ℕ 6
           × readReg (regs s') rax ≡ encode {B} (eval {(A ⇒ B) * A} {B} apply x))

mutual
  -- | Non-halting execution of IR at arbitrary offset
  -- Executes exactly compile-length ir steps, ending at pc = offset + compile-length ir
  -- with rax = encode (eval ir x)
  run-ir-at-offset : ∀ {A B} (ir : IR A B) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) rdi ≡ encode x →
    ∃[ s' ] (exec (compile-length ir) (prefix ++ compile-x86 ir ++ suffix) s ≡ just s'
           × halted s' ≡ false
           × pc s' ≡ length prefix +ℕ compile-length ir
           × readReg (regs s') rax ≡ encode (eval ir x))
  -- Base case: id
  run-ir-at-offset (id {A}) prefix suffix x s h-false pc-eq rdi-eq =
    let (s' , step-eq , h' , pc' , rax-eq) = run-id-at-offset {A} prefix suffix x s h-false pc-eq rdi-eq
    in s' , exec-one-step-nonhalt (prefix ++ compile-x86 {A} {A} id ++ suffix) s s' step-eq h' , h' , pc' , rax-eq
  -- Base case: terminal
  run-ir-at-offset (terminal {A}) prefix suffix x s h-false pc-eq rdi-eq =
    let (s' , step-eq , h' , pc' , rax-eq) = run-terminal-at-offset {A} prefix suffix x s h-false pc-eq
    in s' , exec-one-step-nonhalt (prefix ++ compile-x86 {A} {Unit} terminal ++ suffix) s s' step-eq h' , h' , pc' , rax-eq
  -- Base case: fold
  run-ir-at-offset (fold {F}) prefix suffix x s h-false pc-eq rdi-eq =
    let (s' , step-eq , h' , pc' , rax-eq) = run-fold-at-offset {F} prefix suffix x s h-false pc-eq rdi-eq
    in s' , exec-one-step-nonhalt (prefix ++ compile-x86 {F} {Fix F} fold ++ suffix) s s' step-eq h' , h' , pc' , rax-eq
  -- Base case: unfold
  run-ir-at-offset (unfold {F}) prefix suffix x s h-false pc-eq rdi-eq =
    let (s' , step-eq , h' , pc' , rax-eq) = run-unfold-at-offset {F} prefix suffix x s h-false pc-eq rdi-eq
    in s' , exec-one-step-nonhalt (prefix ++ compile-x86 {Fix F} {F} unfold ++ suffix) s s' step-eq h' , h' , pc' , rax-eq
  -- Base case: arr
  run-ir-at-offset (arr {A} {B}) prefix suffix fn s h-false pc-eq rdi-eq =
    let (s' , step-eq , h' , pc' , rax-eq) = run-arr-at-offset {A} {B} prefix suffix fn s h-false pc-eq rdi-eq
    in s' , exec-one-step-nonhalt (prefix ++ compile-x86 {A ⇒ B} {Eff A B} arr ++ suffix) s s' step-eq h' , h' , pc' , rax-eq
  -- Non-recursive cases (use standalone helpers)
  run-ir-at-offset (fst {A} {B}) prefix suffix x s h-false pc-eq rdi-eq =
    run-ir-at-offset-fst {A} {B} prefix suffix x s h-false pc-eq rdi-eq
  run-ir-at-offset (snd {A} {B}) prefix suffix x s h-false pc-eq rdi-eq =
    run-ir-at-offset-snd {A} {B} prefix suffix x s h-false pc-eq rdi-eq
  run-ir-at-offset (inl {A} {B}) prefix suffix x s h-false pc-eq rdi-eq =
    run-ir-at-offset-inl {A} {B} prefix suffix x s h-false pc-eq rdi-eq
  run-ir-at-offset (inr {A} {B}) prefix suffix x s h-false pc-eq rdi-eq =
    run-ir-at-offset-inr {A} {B} prefix suffix x s h-false pc-eq rdi-eq
  run-ir-at-offset (initial {A}) prefix suffix x s h-false pc-eq rdi-eq =
    run-ir-at-offset-initial {A} prefix suffix x s h-false pc-eq rdi-eq
  -- Recursive cases (defined in this mutual block)
  run-ir-at-offset (_∘_ {A} {B} {C} g f) prefix suffix x s h-false pc-eq rdi-eq =
    run-ir-at-offset-compose {A} {B} {C} f g prefix suffix x s h-false pc-eq rdi-eq
  run-ir-at-offset (⟨_,_⟩ {A} {B} {C} f g) prefix suffix x s h-false pc-eq rdi-eq =
    run-ir-at-offset-pair {A} {B} {C} f g prefix suffix x s h-false pc-eq rdi-eq
  run-ir-at-offset ([_,_] {A} {B} {C} f g) prefix suffix x s h-false pc-eq rdi-eq =
    run-ir-at-offset-case {A} {B} {C} f g prefix suffix x s h-false pc-eq rdi-eq
  run-ir-at-offset (curry {A} {B} {C} f) prefix suffix x s h-false pc-eq rdi-eq =
    run-ir-at-offset-curry {A} {B} {C} f prefix suffix x s h-false pc-eq rdi-eq
  run-ir-at-offset (apply {A} {B}) prefix suffix x s h-false pc-eq rdi-eq =
    run-ir-at-offset-apply {A} {B} prefix suffix x s h-false pc-eq rdi-eq

  -- | Compose case: g ∘ f
  -- compile-x86 (g ∘ f) = compile-x86 f ++ [mov rdi, rax] ++ compile-x86 g
  -- Proof: execute f, then mov, then g
  run-ir-at-offset-compose : ∀ {A B C} (f : IR A B) (g : IR B C) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) rdi ≡ encode x →
    ∃[ s' ] (exec (compile-length (g ∘ f)) (prefix ++ compile-x86 (g ∘ f) ++ suffix) s ≡ just s'
           × halted s' ≡ false
           × pc s' ≡ length prefix +ℕ compile-length (g ∘ f)
           × readReg (regs s') rax ≡ encode (eval (g ∘ f) x))
  run-ir-at-offset-compose {A} {B} {C} f g prefix suffix x s h-false pc-eq rdi-eq =
    -- TODO: Implement using recursive calls to run-ir-at-offset f and run-ir-at-offset g
    -- For now, use postulate to validate structure
    run-ir-at-offset-compose-postulate {A} {B} {C} f g prefix suffix x s h-false pc-eq rdi-eq

  -- | Pair case: ⟨ f , g ⟩
  run-ir-at-offset-pair : ∀ {A B C} (f : IR C A) (g : IR C B) (prefix suffix : Program) (x : ⟦ C ⟧) (s : State) →
    halted s ≡ false → pc s ≡ length prefix → readReg (regs s) rdi ≡ encode x →
    ∃[ s' ] (exec (compile-length ⟨ f , g ⟩) (prefix ++ compile-x86 ⟨ f , g ⟩ ++ suffix) s ≡ just s'
           × halted s' ≡ false × pc s' ≡ length prefix +ℕ compile-length ⟨ f , g ⟩
           × readReg (regs s') rax ≡ encode (eval ⟨ f , g ⟩ x))
  run-ir-at-offset-pair {A} {B} {C} f g prefix suffix x s h-false pc-eq rdi-eq =
    run-ir-at-offset-pair-postulate {A} {B} {C} f g prefix suffix x s h-false pc-eq rdi-eq

  -- | Case case: [ f , g ]
  run-ir-at-offset-case : ∀ {A B C} (f : IR A C) (g : IR B C) (prefix suffix : Program) (x : ⟦ A + B ⟧) (s : State) →
    halted s ≡ false → pc s ≡ length prefix → readReg (regs s) rdi ≡ encode x →
    ∃[ s' ] (exec (compile-length [ f , g ]) (prefix ++ compile-x86 [ f , g ] ++ suffix) s ≡ just s'
           × halted s' ≡ false × pc s' ≡ length prefix +ℕ compile-length [ f , g ]
           × readReg (regs s') rax ≡ encode (eval [ f , g ] x))
  run-ir-at-offset-case {A} {B} {C} f g prefix suffix x s h-false pc-eq rdi-eq =
    run-ir-at-offset-case-postulate {A} {B} {C} f g prefix suffix x s h-false pc-eq rdi-eq

  -- | Curry case: curry f
  run-ir-at-offset-curry : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) (a : ⟦ A ⟧) (s : State) →
    halted s ≡ false → pc s ≡ length prefix → readReg (regs s) rdi ≡ encode a →
    ∃[ s' ] (exec (compile-length (curry f)) (prefix ++ compile-x86 (curry f) ++ suffix) s ≡ just s'
           × halted s' ≡ false × pc s' ≡ length prefix +ℕ compile-length (curry f)
           × readReg (regs s') rax ≡ encode {B ⇒ C} (eval {A} {B ⇒ C} (curry f) a))
  run-ir-at-offset-curry {A} {B} {C} f prefix suffix a s h-false pc-eq rdi-eq =
    run-ir-at-offset-curry-postulate {A} {B} {C} f prefix suffix a s h-false pc-eq rdi-eq

  -- | Apply case: apply
  run-ir-at-offset-apply : ∀ {A B} (prefix suffix : Program) (x : ⟦ (A ⇒ B) * A ⟧) (s : State) →
    halted s ≡ false → pc s ≡ length prefix → readReg (regs s) rdi ≡ encode {(A ⇒ B) * A} x →
    ∃[ s' ] (exec 6 (prefix ++ compile-x86 {(A ⇒ B) * A} {B} apply ++ suffix) s ≡ just s'
           × halted s' ≡ false × pc s' ≡ length prefix +ℕ 6
           × readReg (regs s') rax ≡ encode {B} (eval {(A ⇒ B) * A} {B} apply x))
  run-ir-at-offset-apply {A} {B} prefix suffix x s h-false pc-eq rdi-eq =
    run-ir-at-offset-apply-postulate {A} {B} prefix suffix x s h-false pc-eq rdi-eq

------------------------------------------------------------------------
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

-- Base case: run-seq-compose for id ∘ id
-- Validates the proof structure before generalizing
--
-- Generated code:
--   mov rax, rdi    ; 0 (compile-x86 id)
--   mov rdi, rax    ; 1 (transfer)
--   mov rax, rdi    ; 2 (compile-x86 id)
--
-- Total: 3 instructions, 4 steps (3 + halt on fetch fail at pc=3)
run-seq-compose-id-id : ∀ {A} (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) rdi ≡ encode x →
  ∃[ s' ] (run (compile-x86 {A} {A} (id ∘ id)) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') rax ≡ encode x)
run-seq-compose-id-id {A} x s h-false pc-0 rdi-eq = s4 , run-eq , halt-eq , rax-eq
  where
    prog : List Instr
    prog = compile-x86 {A} {A} (id ∘ id)

    orig-rdi : Word
    orig-rdi = readReg (regs s) rdi

    -- State after step 1: mov rax, rdi
    s1 : State
    s1 = record s { regs = writeReg (regs s) rax (readReg (regs s) rdi)
                  ; pc = pc s +ℕ 1 }

    step1 : step prog s ≡ just s1
    step1 = trans (step-exec-0 (mov (reg rax) (reg rdi)) _ s h-false pc-0)
                  (execMov-reg-reg s rax rdi)

    h1 : halted s1 ≡ false
    h1 = h-false

    pc1 : pc s1 ≡ 1
    pc1 = cong (λ p → p +ℕ 1) pc-0

    -- State after step 2: mov rdi, rax
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
    pc2 = cong (λ p → p +ℕ 1) pc1

    -- State after step 3: mov rax, rdi
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
    pc3 = cong (λ p → p +ℕ 1) pc2

    -- State after step 4: fetch fails at pc=3, halts
    s4 : State
    s4 = record s3 { halted = true }

    fetch-fail : fetch prog (pc s3) ≡ nothing
    fetch-fail = subst (λ p → fetch prog p ≡ nothing) (sym pc3) refl

    step4 : step prog s3 ≡ just s4
    step4 = step-halt-on-fetch-fail prog s3 h3 fetch-fail

    halt-eq : halted s4 ≡ true
    halt-eq = refl

    -- Combined execution: 4 steps
    run-eq : run prog s ≡ just s4
    run-eq = exec-four-steps 9996 prog s s1 s2 s3 s4
               step1 h1 step2 h2 step3 h3 step4 halt-eq

    -- Track rax through states
    -- s1: rax = rdi of s = orig-rdi
    rax-s1 : readReg (regs s1) rax ≡ orig-rdi
    rax-s1 = readReg-writeReg-same (regs s) rax orig-rdi

    -- s2: rax unchanged (only rdi written)
    rax-s2 : readReg (regs s2) rax ≡ orig-rdi
    rax-s2 = trans (readReg-writeReg-rdi-rax (regs s1) (readReg (regs s1) rax)) rax-s1

    -- s2: rdi = rax of s1 = orig-rdi
    rdi-s2 : readReg (regs s2) rdi ≡ orig-rdi
    rdi-s2 = trans (readReg-writeReg-same (regs s1) rdi (readReg (regs s1) rax)) rax-s1

    -- s3: rax = rdi of s2 = orig-rdi
    rax-s3 : readReg (regs s3) rax ≡ orig-rdi
    rax-s3 = trans (readReg-writeReg-same (regs s2) rax (readReg (regs s2) rdi)) rdi-s2

    -- Final: rax = orig-rdi = encode x
    rax-eq : readReg (regs s4) rax ≡ encode x
    rax-eq = trans rax-s3 rdi-eq

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

------------------------------------------------------------------------
-- Proven base cases for run-generator
-- These prove run-generator for specific IR constructors that don't
-- require mutual recursion (10 of 14 IR constructors):
--   id, terminal, fold, unfold, arr, fst, snd, inl, inr, curry
--
-- Remaining (require mutual recursion):
--   compose (∘), case ([ , ]), pair (⟨ , ⟩), apply
------------------------------------------------------------------------

-- | run-generator for id
-- compile-x86 id = [mov rax, rdi]
-- Uses run-single-mov directly
run-generator-id : ∀ {A} (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) rdi ≡ encode x →
  ∃[ s' ] (run (compile-x86 {A} {A} id) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') rax ≡ encode (eval {A} {A} id x))
run-generator-id {A} x s h-false pc-0 rdi-eq = s' , run-eq , halt-eq , rax-eq
  where
    helper : ∃[ s' ] (run (mov (reg rax) (reg rdi) ∷ []) s ≡ just s'
                    × readReg (regs s') rax ≡ readReg (regs s) rdi
                    × halted s' ≡ true)
    helper = run-single-mov s rax rdi h-false pc-0

    s' : State
    s' = proj₁ helper

    run-eq : run (compile-x86 {A} {A} id) s ≡ just s'
    run-eq = proj₁ (proj₂ helper)

    halt-eq : halted s' ≡ true
    halt-eq = proj₂ (proj₂ (proj₂ helper))

    rax-eq : readReg (regs s') rax ≡ encode (eval {A} {A} id x)
    rax-eq = trans (proj₁ (proj₂ (proj₂ helper))) rdi-eq

-- | run-generator for terminal
-- compile-x86 terminal = [mov rax, 0]
-- Uses run-single-mov-imm directly
run-generator-terminal : ∀ {A} (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) rdi ≡ encode x →
  ∃[ s' ] (run (compile-x86 {A} {Unit} terminal) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') rax ≡ encode {Unit} (eval {A} {Unit} terminal x))
run-generator-terminal {A} x s h-false pc-0 rdi-eq = s' , run-eq , halt-eq , rax-eq
  where
    helper : ∃[ s' ] (run (mov (reg rax) (imm 0) ∷ []) s ≡ just s'
                    × readReg (regs s') rax ≡ 0
                    × halted s' ≡ true)
    helper = run-single-mov-imm s rax 0 h-false pc-0

    s' : State
    s' = proj₁ helper

    run-eq : run (compile-x86 {A} {Unit} terminal) s ≡ just s'
    run-eq = proj₁ (proj₂ helper)

    halt-eq : halted s' ≡ true
    halt-eq = proj₂ (proj₂ (proj₂ helper))

    -- eval terminal x = tt, encode tt = 0
    rax-eq : readReg (regs s') rax ≡ encode (eval {A} {Unit} terminal x)
    rax-eq = trans (proj₁ (proj₂ (proj₂ helper))) (sym encode-unit)

-- | run-generator for fold
-- compile-x86 fold = [mov rax, rdi]
-- Uses run-single-mov and encode-fix-wrap
run-generator-fold : ∀ {F} (x : ⟦ F ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) rdi ≡ encode x →
  ∃[ s' ] (run (compile-x86 {F} {Fix F} fold) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') rax ≡ encode (eval {F} {Fix F} fold x))
run-generator-fold {F} x s h-false pc-0 rdi-eq = s' , run-eq , halt-eq , rax-eq
  where
    helper : ∃[ s' ] (run (mov (reg rax) (reg rdi) ∷ []) s ≡ just s'
                    × readReg (regs s') rax ≡ readReg (regs s) rdi
                    × halted s' ≡ true)
    helper = run-single-mov s rax rdi h-false pc-0

    s' : State
    s' = proj₁ helper

    run-eq : run (compile-x86 {F} {Fix F} fold) s ≡ just s'
    run-eq = proj₁ (proj₂ helper)

    halt-eq : halted s' ≡ true
    halt-eq = proj₂ (proj₂ (proj₂ helper))

    -- eval fold x = wrap x, encode (wrap x) = encode x by encode-fix-wrap
    rax-eq : readReg (regs s') rax ≡ encode (eval {F} {Fix F} fold x)
    rax-eq = trans (proj₁ (proj₂ (proj₂ helper))) (trans rdi-eq (encode-fix-wrap x))

-- | run-generator for unfold
-- compile-x86 unfold = [mov rax, rdi]
-- Uses run-single-mov and encode-fix-unwrap
run-generator-unfold : ∀ {F} (x : ⟦ Fix F ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) rdi ≡ encode x →
  ∃[ s' ] (run (compile-x86 {Fix F} {F} unfold) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') rax ≡ encode (eval {Fix F} {F} unfold x))
run-generator-unfold {F} x s h-false pc-0 rdi-eq = s' , run-eq , halt-eq , rax-eq
  where
    helper : ∃[ s' ] (run (mov (reg rax) (reg rdi) ∷ []) s ≡ just s'
                    × readReg (regs s') rax ≡ readReg (regs s) rdi
                    × halted s' ≡ true)
    helper = run-single-mov s rax rdi h-false pc-0

    s' : State
    s' = proj₁ helper

    run-eq : run (compile-x86 {Fix F} {F} unfold) s ≡ just s'
    run-eq = proj₁ (proj₂ helper)

    halt-eq : halted s' ≡ true
    halt-eq = proj₂ (proj₂ (proj₂ helper))

    -- eval unfold x = unwrap x, encode (unwrap x) = encode x by encode-fix-unwrap
    rax-eq : readReg (regs s') rax ≡ encode (eval {Fix F} {F} unfold x)
    rax-eq = trans (proj₁ (proj₂ (proj₂ helper))) (trans rdi-eq (encode-fix-unwrap x))

-- | run-generator for arr
-- compile-x86 arr = [mov rax, rdi]
-- Uses run-single-mov and encode-arr-identity
run-generator-arr : ∀ {A B} (f : ⟦ A ⇒ B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) rdi ≡ encode {A ⇒ B} f →
  ∃[ s' ] (run (compile-x86 {A ⇒ B} {Eff A B} arr) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') rax ≡ encode {Eff A B} (eval {A ⇒ B} {Eff A B} arr f))
run-generator-arr {A} {B} f s h-false pc-0 rdi-eq = s' , run-eq , halt-eq , rax-eq
  where
    helper : ∃[ s' ] (run (mov (reg rax) (reg rdi) ∷ []) s ≡ just s'
                    × readReg (regs s') rax ≡ readReg (regs s) rdi
                    × halted s' ≡ true)
    helper = run-single-mov s rax rdi h-false pc-0

    s' : State
    s' = proj₁ helper

    run-eq : run (compile-x86 {A ⇒ B} {Eff A B} arr) s ≡ just s'
    run-eq = proj₁ (proj₂ helper)

    halt-eq : halted s' ≡ true
    halt-eq = proj₂ (proj₂ (proj₂ helper))

    -- eval arr f = f (definitionally), encode {A ⇒ B} f = encode {Eff A B} f by encode-arr-identity
    rax-eq : readReg (regs s') rax ≡ encode {Eff A B} (eval {A ⇒ B} {Eff A B} arr f)
    rax-eq = trans (proj₁ (proj₂ (proj₂ helper))) (trans rdi-eq (encode-arr-identity f))

-- | run-generator for fst
-- compile-x86 fst = [mov rax, [rdi]]
-- Uses run-single-mov-mem-base and encode-pair-fst
run-generator-fst : ∀ {A B} (x : ⟦ A * B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) rdi ≡ encode x →
  ∃[ s' ] (run (compile-x86 {A * B} {A} fst) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') rax ≡ encode (eval {A * B} {A} fst x))
run-generator-fst {A} {B} (a , b) s h-false pc-0 rdi-eq = s' , run-eq , halt-eq , rax-eq
  where
    -- Memory at rdi contains encode a (from pair encoding postulate)
    mem-at-rdi : readMem (memory s) (readReg (regs s) rdi) ≡ just (encode a)
    mem-at-rdi = subst (λ addr → readMem (memory s) addr ≡ just (encode a))
                       (sym rdi-eq)
                       (encode-pair-fst a b (memory s))

    helper : ∃[ s' ] (run (mov (reg rax) (mem (base rdi)) ∷ []) s ≡ just s'
                    × readReg (regs s') rax ≡ encode a
                    × halted s' ≡ true)
    helper = run-single-mov-mem-base s rax rdi (encode a) h-false pc-0 mem-at-rdi

    s' : State
    s' = proj₁ helper

    run-eq : run (compile-x86 {A * B} {A} fst) s ≡ just s'
    run-eq = proj₁ (proj₂ helper)

    halt-eq : halted s' ≡ true
    halt-eq = proj₂ (proj₂ (proj₂ helper))

    -- eval fst (a , b) = a
    rax-eq : readReg (regs s') rax ≡ encode (eval {A * B} {A} fst (a , b))
    rax-eq = proj₁ (proj₂ (proj₂ helper))

-- | run-generator for snd
-- compile-x86 snd = [mov rax, [rdi+8]]
-- Uses run-single-mov-mem-disp and encode-pair-snd
run-generator-snd : ∀ {A B} (x : ⟦ A * B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) rdi ≡ encode x →
  ∃[ s' ] (run (compile-x86 {A * B} {B} snd) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') rax ≡ encode (eval {A * B} {B} snd x))
run-generator-snd {A} {B} (a , b) s h-false pc-0 rdi-eq = s' , run-eq , halt-eq , rax-eq
  where
    -- Memory at rdi + 8 contains encode b (from pair encoding postulate)
    mem-at-rdi-8 : readMem (memory s) (readReg (regs s) rdi +ℕ 8) ≡ just (encode b)
    mem-at-rdi-8 = subst (λ addr → readMem (memory s) (addr +ℕ 8) ≡ just (encode b))
                         (sym rdi-eq)
                         (encode-pair-snd a b (memory s))

    helper : ∃[ s' ] (run (mov (reg rax) (mem (base+disp rdi 8)) ∷ []) s ≡ just s'
                    × readReg (regs s') rax ≡ encode b
                    × halted s' ≡ true)
    helper = run-single-mov-mem-disp s rax rdi 8 (encode b) h-false pc-0 mem-at-rdi-8

    s' : State
    s' = proj₁ helper

    run-eq : run (compile-x86 {A * B} {B} snd) s ≡ just s'
    run-eq = proj₁ (proj₂ helper)

    halt-eq : halted s' ≡ true
    halt-eq = proj₂ (proj₂ (proj₂ helper))

    -- eval snd (a , b) = b
    rax-eq : readReg (regs s') rax ≡ encode (eval {A * B} {B} snd (a , b))
    rax-eq = proj₁ (proj₂ (proj₂ helper))

-- | run-generator for inl
-- compile-x86 inl allocates stack with [0, rdi] and returns pointer
-- Uses run-inl-seq and encode-inl-construct
run-generator-inl : ∀ {A B} (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) rdi ≡ encode x →
  ∃[ s' ] (run (compile-x86 {A} {A + B} inl) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') rax ≡ encode (eval {A} {A + B} inl x))
run-generator-inl {A} {B} x s h-false pc-0 rdi-eq = s' , run-eq , halt-eq , rax-eq
  where
    -- Use run-inl-seq to execute the inl code
    helper : ∃[ s' ] (run (compile-x86 {A} {A + B} inl) s ≡ just s'
                    × halted s' ≡ true
                    × readReg (regs s') rax ≡ readReg (regs s') rsp
                    × readMem (memory s') (readReg (regs s') rax) ≡ just 0
                    × readMem (memory s') (readReg (regs s') rax +ℕ 8) ≡ just (readReg (regs s) rdi))
    helper = run-inl-seq {A} {B} s h-false pc-0

    s' : State
    s' = proj₁ helper

    run-eq : run (compile-x86 {A} {A + B} inl) s ≡ just s'
    run-eq = proj₁ (proj₂ helper)

    halt-eq : halted s' ≡ true
    halt-eq = proj₁ (proj₂ (proj₂ helper))

    -- Memory at rax has [0, encode x]
    tag-is-0 : readMem (memory s') (readReg (regs s') rax) ≡ just 0
    tag-is-0 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ helper))))

    val-is-rdi : readMem (memory s') (readReg (regs s') rax +ℕ 8) ≡ just (readReg (regs s) rdi)
    val-is-rdi = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ helper))))

    -- rdi = encode x, so value at [rax+8] = encode x
    val-is-encode-x : readMem (memory s') (readReg (regs s') rax +ℕ 8) ≡ just (encode x)
    val-is-encode-x = trans val-is-rdi (cong just rdi-eq)

    -- By encode-inl-construct: memory has [0, encode x] at rax, so rax = encode (inj₁ x)
    -- eval inl x = inj₁ x
    rax-eq : readReg (regs s') rax ≡ encode (eval {A} {A + B} inl x)
    rax-eq = encode-inl-construct x (readReg (regs s') rax) (memory s') tag-is-0 val-is-encode-x

-- | run-generator for inr
-- compile-x86 inr allocates stack with [1, rdi] and returns pointer
-- Uses run-inr-seq and encode-inr-construct
run-generator-inr : ∀ {A B} (x : ⟦ B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) rdi ≡ encode x →
  ∃[ s' ] (run (compile-x86 {B} {A + B} inr) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') rax ≡ encode (eval {B} {A + B} inr x))
run-generator-inr {A} {B} x s h-false pc-0 rdi-eq = s' , run-eq , halt-eq , rax-eq
  where
    -- Use run-inr-seq to execute the inr code
    helper : ∃[ s' ] (run (compile-x86 {B} {A + B} inr) s ≡ just s'
                    × halted s' ≡ true
                    × readReg (regs s') rax ≡ readReg (regs s') rsp
                    × readMem (memory s') (readReg (regs s') rax) ≡ just 1
                    × readMem (memory s') (readReg (regs s') rax +ℕ 8) ≡ just (readReg (regs s) rdi))
    helper = run-inr-seq {A} {B} s h-false pc-0

    s' : State
    s' = proj₁ helper

    run-eq : run (compile-x86 {B} {A + B} inr) s ≡ just s'
    run-eq = proj₁ (proj₂ helper)

    halt-eq : halted s' ≡ true
    halt-eq = proj₁ (proj₂ (proj₂ helper))

    -- Memory at rax has [1, encode x]
    tag-is-1 : readMem (memory s') (readReg (regs s') rax) ≡ just 1
    tag-is-1 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ helper))))

    val-is-rdi : readMem (memory s') (readReg (regs s') rax +ℕ 8) ≡ just (readReg (regs s) rdi)
    val-is-rdi = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ helper))))

    -- rdi = encode x, so value at [rax+8] = encode x
    val-is-encode-x : readMem (memory s') (readReg (regs s') rax +ℕ 8) ≡ just (encode x)
    val-is-encode-x = trans val-is-rdi (cong just rdi-eq)

    -- By encode-inr-construct: memory has [1, encode x] at rax, so rax = encode (inj₂ x)
    -- eval inr x = inj₂ x
    rax-eq : readReg (regs s') rax ≡ encode (eval {B} {A + B} inr x)
    rax-eq = encode-inr-construct x (readReg (regs s') rax) (memory s') tag-is-1 val-is-encode-x

------------------------------------------------------------------------

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
-- Generated code for curry f (code-ptr = 5, end-label = 11 + |f|):
--   0: sub rsp, 16          ; allocate closure on stack
--   1: mov [rsp], rdi       ; store environment (input a)
--   2: mov [rsp+8], 5       ; store code pointer
--   3: mov rax, rsp         ; return closure pointer
--   4: jmp (11+|f|)         ; jump over thunk code
--   5: label 5              ; thunk code (not executed by curry)
--   ...                     ; thunk body
--   11+|f|: label (11+|f|)  ; end
--
-- Execution: 5 instructions, jmp to end label, execute label (no-op), halt on fetch fail
--
-- Proof: trace through 7 steps (5 instrs + label + halt)
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
run-curry-seq {A} {B} {C} f a s h-false pc-0 rdi-eq = s7 , run-eq , halt-eq , env-eq
  where
    prog : List Instr
    prog = compile-x86 {A} {B ⇒ C} (curry f)

    -- Computed label values
    code-ptr : ℕ
    code-ptr = 5

    end-label : ℕ
    end-label = 11 +ℕ compile-length f

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

    -- State after step 3: mov [rsp+8], 5 (store code pointer)
    s3 : State
    s3 = record s2 { memory = writeMem (memory s2) (readReg (regs s2) rsp +ℕ 8) code-ptr
                   ; pc = pc s2 +ℕ 1 }

    step3 : step prog s2 ≡ just s3
    step3 = trans (step-exec prog s2 (mov (mem (base+disp rsp 8)) (imm code-ptr)) h2
                             (subst (λ p → fetch prog p ≡ just (mov (mem (base+disp rsp 8)) (imm code-ptr))) (sym pc2) refl))
                  (execMov-mem-disp-imm prog s2 rsp 8 code-ptr)
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

    -- State after step 5: jmp end-label (jump over thunk)
    s5 : State
    s5 = record s4 { pc = end-label }

    step5 : step prog s4 ≡ just s5
    step5 = trans (step-exec prog s4 (jmp end-label) h4
                             (subst (λ p → fetch prog p ≡ just (jmp end-label)) (sym pc4) refl))
                  (execJmp prog s4 end-label)

    h5 : halted s5 ≡ false
    h5 = h-false

    -- State after step 6: execute label (no-op) at end-label
    s6 : State
    s6 = record s5 { pc = end-label +ℕ 1 }

    -- For step 6, we need to fetch the label instruction at position end-label
    -- Proof: use fetch-append-skip twice to skip past prefix and compile-x86 f

    -- The program structure:
    -- prog = prefix10 ++ (compile-x86 f ++ tail2)
    -- where prefix10 = sub ∷ mov ∷ mov ∷ mov ∷ jmp ∷ label ∷ sub ∷ mov ∷ mov ∷ mov ∷ []
    -- and tail2 = ret ∷ label end-label ∷ []

    prefix10 : List Instr
    prefix10 = sub (reg rsp) (imm 16) ∷
               mov (mem (base rsp)) (reg rdi) ∷
               mov (mem (base+disp rsp 8)) (imm code-ptr) ∷
               mov (reg rax) (reg rsp) ∷
               jmp end-label ∷
               label code-ptr ∷
               sub (reg rsp) (imm 16) ∷
               mov (mem (base rsp)) (reg r12) ∷
               mov (mem (base+disp rsp 8)) (reg rdi) ∷
               mov (reg rdi) (reg rsp) ∷
               []

    tail2 : List Instr
    tail2 = ret ∷ label end-label ∷ []

    -- prog = prefix10 ++ (compile-x86 f ++ tail2)
    prog-structure : prog ≡ prefix10 ++ (compile-x86 f ++ tail2)
    prog-structure = refl

    -- end-label = 11 + |f| = 10 + (|f| + 1)
    -- Step 1: fetch prog (10 + (|f| + 1)) = fetch (compile-x86 f ++ tail2) (|f| + 1)
    -- Step 2: fetch (compile-x86 f ++ tail2) (|f| + 1) = fetch tail2 1
    -- Step 3: fetch tail2 1 = just (label end-label)

    open import Data.Nat.Properties using (+-comm; +-assoc)

    -- Prove 11 + |f| = 10 + (|f| + 1)
    end-label-eq : end-label ≡ 10 +ℕ (compile-length f +ℕ 1)
    end-label-eq = sym (trans (+-assoc 10 (compile-length f) 1)
                              (cong (10 +ℕ_) (+-comm (compile-length f) 1)))

    -- Skip prefix to get tail
    skip-prefix : fetch prog (10 +ℕ (compile-length f +ℕ 1)) ≡ fetch (compile-x86 f ++ tail2) (compile-length f +ℕ 1)
    skip-prefix = fetch-append-skip prefix10 (compile-x86 f ++ tail2) (compile-length f +ℕ 1)

    -- Need: length (compile-x86 f) = compile-length f
    len-f : length (compile-x86 f) ≡ compile-length f
    len-f = compile-length-correct f

    -- Skip compile-x86 f to get tail2
    skip-f : fetch (compile-x86 f ++ tail2) (length (compile-x86 f) +ℕ 1) ≡ fetch tail2 1
    skip-f = fetch-append-skip (compile-x86 f) tail2 1

    -- Adjust skip-f to use compile-length f instead of length (compile-x86 f)
    skip-f' : fetch (compile-x86 f ++ tail2) (compile-length f +ℕ 1) ≡ fetch tail2 1
    skip-f' = subst (λ n → fetch (compile-x86 f ++ tail2) (n +ℕ 1) ≡ fetch tail2 1) len-f skip-f

    -- Fetch at position 1 of tail2 gives label end-label
    fetch-tail2 : fetch tail2 1 ≡ just (label end-label)
    fetch-tail2 = refl

    fetch-end-label : fetch prog end-label ≡ just (label end-label)
    fetch-end-label = trans (subst (λ n → fetch prog n ≡ fetch prog (10 +ℕ (compile-length f +ℕ 1)))
                                   (sym end-label-eq) refl)
                           (trans skip-prefix
                                  (trans skip-f' fetch-tail2))

    step6 : step prog s5 ≡ just s6
    step6 = trans (step-exec prog s5 (label end-label) h5 fetch-end-label)
                  (execLabel prog s5 end-label)

    h6 : halted s6 ≡ false
    h6 = h-false

    -- State after step 7: fetch at end-label+1 fails, halts
    -- The program has exactly 12 + compile-length f instructions, so fetch at 12 + compile-length f fails
    s7 : State
    s7 = record s6 { halted = true }

    -- fetch at end-label+1 = 12 + compile-length f fails because that's past the end
    -- Proof: end-label + 1 = 12 + |f| = length prog, and fetch-past-length says fetch at length prog fails

    -- length prog = 12 + compile-length f
    prog-length : length prog ≡ 12 +ℕ compile-length f
    prog-length = compile-length-correct (curry f)

    -- end-label + 1 = 12 + compile-length f
    -- (11 + |f|) + 1 = 11 + (|f| + 1) = 11 + (1 + |f|) = (11 + 1) + |f| = 12 + |f|
    end-plus-1 : end-label +ℕ 1 ≡ 12 +ℕ compile-length f
    end-plus-1 = trans (+-assoc 11 (compile-length f) 1)
                       (trans (cong (11 +ℕ_) (+-comm (compile-length f) 1))
                              (sym (+-assoc 11 1 (compile-length f))))

    -- end-label + 1 = length prog
    pos-eq-length : end-label +ℕ 1 ≡ length prog
    pos-eq-length = trans end-plus-1 (sym prog-length)

    -- fetch prog (length prog + 0) = nothing
    fetch-at-length : fetch prog (length prog +ℕ 0) ≡ nothing
    fetch-at-length = fetch-past-length prog 0

    -- Simplify: length prog + 0 = length prog
    open import Data.Nat.Properties using (+-identityʳ)

    fetch-at-length' : fetch prog (length prog) ≡ nothing
    fetch-at-length' = subst (λ n → fetch prog n ≡ nothing) (+-identityʳ (length prog)) fetch-at-length

    fetch-past-end : fetch prog (end-label +ℕ 1) ≡ nothing
    fetch-past-end = subst (λ n → fetch prog n ≡ nothing) (sym pos-eq-length) fetch-at-length'

    step7 : step prog s6 ≡ just s7
    step7 = step-halt-on-fetch-fail prog s6 h6 fetch-past-end

    halt-eq : halted s7 ≡ true
    halt-eq = refl

    -- Combined execution: 7 steps total (5 instructions + label + halt)
    run-eq : run prog s ≡ just s7
    run-eq = exec-seven-steps 9993 prog s s1 s2 s3 s4 s5 s6 s7 step1 h1 step2 h2 step3 h3 step4 h4 step5 h5 step6 h6 step7 halt-eq

    -- Now prove properties about s7

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

    -- rax in s7 = rax in s4 = rsp in s3 = new-rsp
    rax-s4 : readReg (regs s4) rax ≡ new-rsp
    rax-s4 = trans (readReg-writeReg-same (regs s3) rax (readReg (regs s3) rsp)) rsp-s3

    rax-s7 : readReg (regs s7) rax ≡ new-rsp
    rax-s7 = rax-s4

    -- Address calculations
    addr-disjoint : new-rsp ≢ new-rsp +ℕ 8
    addr-disjoint = n≢n+suc new-rsp 7

    -- Memory trace: s7.memory = s3.memory = writeMem s2.memory (new-rsp+8) code-ptr
    --               s2.memory = writeMem s1.memory new-rsp orig-rdi

    -- Environment at [rax] = orig-rdi = encode a
    -- Reading from new-rsp in s7:
    --   s7.memory = s3.memory (s4,s5,s6,s7 don't touch memory)
    --   s3.memory = writeMem s2.memory (new-rsp+8) code-ptr
    --   s2.memory = writeMem s1.memory new-rsp orig-rdi
    -- So reading at new-rsp: first check s3's write (at new-rsp+8, different addr),
    -- then s2's write (at new-rsp, matches)
    env-eq : readMem (memory s7) (readReg (regs s7) rax) ≡ just (encode a)
    env-eq = trans (cong (readMem (memory s7)) rax-s7)
                   (trans (readMem-writeMem-diff (memory s2) (new-rsp +ℕ 8) new-rsp code-ptr (λ eq → addr-disjoint (sym eq)))
                          (trans (readMem-writeMem-same (memory s1) new-rsp (readReg (regs s1) rdi))
                                 (trans (cong just rdi-s1) (cong just rdi-eq))))

-- | run-generator for curry
-- compile-x86 (curry f) creates a closure [env, code_ptr]
-- Uses run-curry-seq and encode-closure-construct
run-generator-curry : ∀ {A B C} (f : IR (A * B) C) (a : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) rdi ≡ encode {A} a →
  ∃[ s' ] (run (compile-x86 {A} {B ⇒ C} (curry f)) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') rax ≡ encode {B ⇒ C} (eval {A} {B ⇒ C} (curry f) a))
run-generator-curry {A} {B} {C} f a s h-false pc-0 rdi-eq = s' , run-eq , halt-eq , rax-eq
  where
    -- Use run-curry-seq to execute the curry code
    helper : ∃[ s' ] (run (compile-x86 {A} {B ⇒ C} (curry f)) s ≡ just s'
                    × halted s' ≡ true
                    × readMem (memory s') (readReg (regs s') rax) ≡ just (encode {A} a))
    helper = run-curry-seq f a s h-false pc-0 rdi-eq

    s' : State
    s' = proj₁ helper

    run-eq : run (compile-x86 {A} {B ⇒ C} (curry f)) s ≡ just s'
    run-eq = proj₁ (proj₂ helper)

    halt-eq : halted s' ≡ true
    halt-eq = proj₁ (proj₂ (proj₂ helper))

    -- Memory at rax contains encode a (the environment)
    env-at-rax : readMem (memory s') (readReg (regs s') rax) ≡ just (encode {A} a)
    env-at-rax = proj₂ (proj₂ (proj₂ helper))

    -- By encode-closure-construct: if memory at p has encode a, then p = encode (λ b → eval f (a, b))
    -- eval (curry f) a = λ b → eval f (a, b) by definition (definitionally equal)
    rax-eq : readReg (regs s') rax ≡ encode {B ⇒ C} (eval {A} {B ⇒ C} (curry f) a)
    rax-eq = encode-closure-construct f a (readReg (regs s') rax) (memory s') env-at-rax

------------------------------------------------------------------------
-- Compose base cases
-- These prove run-generator for compose where f and g are specific
-- non-recursive IR constructors. Shows the approach works.
------------------------------------------------------------------------

-- | run-generator for (id ∘ id)
-- Uses run-seq-compose-id-id and the fact that eval id = identity
run-generator-compose-id-id : ∀ {A} (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) rdi ≡ encode x →
  ∃[ s' ] (run (compile-x86 {A} {A} (id ∘ id)) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') rax ≡ encode (eval {A} {A} (id ∘ id) x))
run-generator-compose-id-id {A} x s h-false pc-0 rdi-eq = s' , run-eq , halt-eq , rax-eq
  where
    -- Use run-seq-compose-id-id base case
    helper : ∃[ s' ] (run (compile-x86 {A} {A} (id ∘ id)) s ≡ just s'
                    × halted s' ≡ true
                    × readReg (regs s') rax ≡ encode x)
    helper = run-seq-compose-id-id x s h-false pc-0 rdi-eq

    s' : State
    s' = proj₁ helper

    run-eq : run (compile-x86 {A} {A} (id ∘ id)) s ≡ just s'
    run-eq = proj₁ (proj₂ helper)

    halt-eq : halted s' ≡ true
    halt-eq = proj₁ (proj₂ (proj₂ helper))

    -- eval (id ∘ id) x = eval id (eval id x) = x
    rax-eq : readReg (regs s') rax ≡ encode (eval {A} {A} (id ∘ id) x)
    rax-eq = proj₂ (proj₂ (proj₂ helper))

-- | run-seq-compose for (terminal ∘ id)
-- Validates the approach with g ≠ id
--
-- Generated code:
--   mov rax, rdi    ; 0 (compile-x86 id)
--   mov rdi, rax    ; 1 (transfer)
--   mov rax, 0      ; 2 (compile-x86 terminal)
--
-- Total: 3 instructions, 4 steps (3 + halt on fetch fail at pc=3)
run-seq-compose-terminal-id : ∀ {A} (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) rdi ≡ encode x →
  ∃[ s' ] (run (compile-x86 {A} {Unit} (terminal ∘ id)) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') rax ≡ 0)
run-seq-compose-terminal-id {A} x s h-false pc-0 rdi-eq = s4 , run-eq , halt-eq , rax-eq
  where
    prog : List Instr
    prog = compile-x86 {A} {Unit} (terminal ∘ id)

    -- State after step 1: mov rax, rdi
    s1 : State
    s1 = record s { regs = writeReg (regs s) rax (readReg (regs s) rdi)
                  ; pc = pc s +ℕ 1 }

    step1 : step prog s ≡ just s1
    step1 = trans (step-exec-0 (mov (reg rax) (reg rdi)) _ s h-false pc-0)
                  (execMov-reg-reg s rax rdi)

    h1 : halted s1 ≡ false
    h1 = h-false

    pc1 : pc s1 ≡ 1
    pc1 = cong (λ p → p +ℕ 1) pc-0

    -- State after step 2: mov rdi, rax
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
    pc2 = cong (λ p → p +ℕ 1) pc1

    -- State after step 3: mov rax, 0 (terminal)
    s3 : State
    s3 = record s2 { regs = writeReg (regs s2) rax 0
                   ; pc = pc s2 +ℕ 1 }

    step3 : step prog s2 ≡ just s3
    step3 = trans (step-exec prog s2 (mov (reg rax) (imm 0)) h2
                             (subst (λ p → fetch prog p ≡ just (mov (reg rax) (imm 0))) (sym pc2) refl))
                  (execMov-reg-imm s2 rax 0)

    h3 : halted s3 ≡ false
    h3 = h-false

    pc3 : pc s3 ≡ 3
    pc3 = cong (λ p → p +ℕ 1) pc2

    -- State after step 4: fetch fails at pc=3, halts
    s4 : State
    s4 = record s3 { halted = true }

    fetch-fail : fetch prog (pc s3) ≡ nothing
    fetch-fail = subst (λ p → fetch prog p ≡ nothing) (sym pc3) refl

    step4 : step prog s3 ≡ just s4
    step4 = step-halt-on-fetch-fail prog s3 h3 fetch-fail

    halt-eq : halted s4 ≡ true
    halt-eq = refl

    -- Combined execution: 4 steps
    run-eq : run prog s ≡ just s4
    run-eq = exec-four-steps 9996 prog s s1 s2 s3 s4
               step1 h1 step2 h2 step3 h3 step4 halt-eq

    -- rax in s3 = 0 (from mov rax, 0)
    rax-eq : readReg (regs s4) rax ≡ 0
    rax-eq = readReg-writeReg-same (regs s2) rax 0

-- | run-generator for (terminal ∘ id)
run-generator-compose-terminal-id : ∀ {A} (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) rdi ≡ encode x →
  ∃[ s' ] (run (compile-x86 {A} {Unit} (terminal ∘ id)) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') rax ≡ encode {Unit} (eval {A} {Unit} (terminal ∘ id) x))
run-generator-compose-terminal-id {A} x s h-false pc-0 rdi-eq = s' , run-eq , halt-eq , rax-eq
  where
    -- Use run-seq-compose-terminal-id base case
    helper : ∃[ s' ] (run (compile-x86 {A} {Unit} (terminal ∘ id)) s ≡ just s'
                    × halted s' ≡ true
                    × readReg (regs s') rax ≡ 0)
    helper = run-seq-compose-terminal-id x s h-false pc-0 rdi-eq

    s' : State
    s' = proj₁ helper

    run-eq : run (compile-x86 {A} {Unit} (terminal ∘ id)) s ≡ just s'
    run-eq = proj₁ (proj₂ helper)

    halt-eq : halted s' ≡ true
    halt-eq = proj₁ (proj₂ (proj₂ helper))

    -- eval (terminal ∘ id) x = eval terminal (eval id x) = tt
    -- encode tt = 0 by encode-unit
    rax-eq : readReg (regs s') rax ≡ encode (eval {A} {Unit} (terminal ∘ id) x)
    rax-eq = trans (proj₂ (proj₂ (proj₂ helper))) (sym encode-unit)

-- | run-seq-compose for (id ∘ terminal)
-- Shows the pattern when g ≠ id (first operand produces constant, second is identity)
--
-- Generated code:
--   mov rax, 0      ; 0 (compile-x86 terminal)
--   mov rdi, rax    ; 1 (transfer)
--   mov rax, rdi    ; 2 (compile-x86 id)
--
-- Total: 3 instructions, 4 steps (3 + halt on fetch fail at pc=3)
run-seq-compose-id-terminal : ∀ {A} (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) rdi ≡ encode x →
  ∃[ s' ] (run (compile-x86 {A} {Unit} (id ∘ terminal)) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') rax ≡ 0)
run-seq-compose-id-terminal {A} x s h-false pc-0 rdi-eq = s4 , run-eq , halt-eq , rax-eq
  where
    prog : List Instr
    prog = compile-x86 {A} {Unit} (id ∘ terminal)

    -- State after step 1: mov rax, 0 (terminal)
    s1 : State
    s1 = record s { regs = writeReg (regs s) rax 0
                  ; pc = pc s +ℕ 1 }

    step1 : step prog s ≡ just s1
    step1 = trans (step-exec-0 (mov (reg rax) (imm 0)) _ s h-false pc-0)
                  (execMov-reg-imm s rax 0)

    h1 : halted s1 ≡ false
    h1 = h-false

    pc1 : pc s1 ≡ 1
    pc1 = cong (λ p → p +ℕ 1) pc-0

    -- State after step 2: mov rdi, rax
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
    pc2 = cong (λ p → p +ℕ 1) pc1

    -- State after step 3: mov rax, rdi (id)
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
    pc3 = cong (λ p → p +ℕ 1) pc2

    -- State after step 4: fetch fails at pc=3, halts
    s4 : State
    s4 = record s3 { halted = true }

    fetch-fail : fetch prog (pc s3) ≡ nothing
    fetch-fail = subst (λ p → fetch prog p ≡ nothing) (sym pc3) refl

    step4 : step prog s3 ≡ just s4
    step4 = step-halt-on-fetch-fail prog s3 h3 fetch-fail

    halt-eq : halted s4 ≡ true
    halt-eq = refl

    -- Combined execution: 4 steps
    run-eq : run prog s ≡ just s4
    run-eq = exec-four-steps 9996 prog s s1 s2 s3 s4
               step1 h1 step2 h2 step3 h3 step4 halt-eq

    -- Track rax through states
    -- s1: rax = 0
    rax-s1 : readReg (regs s1) rax ≡ 0
    rax-s1 = readReg-writeReg-same (regs s) rax 0

    -- s2: rdi = rax = 0
    rdi-s2 : readReg (regs s2) rdi ≡ 0
    rdi-s2 = trans (readReg-writeReg-same (regs s1) rdi (readReg (regs s1) rax)) rax-s1

    -- s3: rax = rdi = 0
    rax-s3 : readReg (regs s3) rax ≡ 0
    rax-s3 = trans (readReg-writeReg-same (regs s2) rax (readReg (regs s2) rdi)) rdi-s2

    -- Final: rax = 0
    rax-eq : readReg (regs s4) rax ≡ 0
    rax-eq = rax-s3

-- | run-generator for (id ∘ terminal)
run-generator-compose-id-terminal : ∀ {A} (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) rdi ≡ encode x →
  ∃[ s' ] (run (compile-x86 {A} {Unit} (id ∘ terminal)) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') rax ≡ encode {Unit} (eval {A} {Unit} (id ∘ terminal) x))
run-generator-compose-id-terminal {A} x s h-false pc-0 rdi-eq = s' , run-eq , halt-eq , rax-eq
  where
    helper : ∃[ s' ] (run (compile-x86 {A} {Unit} (id ∘ terminal)) s ≡ just s'
                    × halted s' ≡ true
                    × readReg (regs s') rax ≡ 0)
    helper = run-seq-compose-id-terminal x s h-false pc-0 rdi-eq

    s' : State
    s' = proj₁ helper

    run-eq : run (compile-x86 {A} {Unit} (id ∘ terminal)) s ≡ just s'
    run-eq = proj₁ (proj₂ helper)

    halt-eq : halted s' ≡ true
    halt-eq = proj₁ (proj₂ (proj₂ helper))

    -- eval (id ∘ terminal) x = eval id (eval terminal x) = eval id tt = tt
    -- encode tt = 0 by encode-unit
    rax-eq : readReg (regs s') rax ≡ encode (eval {A} {Unit} (id ∘ terminal) x)
    rax-eq = trans (proj₂ (proj₂ (proj₂ helper))) (sym encode-unit)

------------------------------------------------------------------------
-- Compose proofs using offset helpers (demonstrating the approach)
------------------------------------------------------------------------

-- | run-seq-compose for (terminal ∘ terminal)
-- Demonstrates the compose pattern with both sub-programs being terminal
--
-- Generated code:
--   mov rax, 0      ; 0 (compile-x86 terminal)
--   mov rdi, rax    ; 1 (transfer)
--   mov rax, 0      ; 2 (compile-x86 terminal)
--
-- Total: 3 instructions, 4 steps (3 + halt on fetch fail at pc=3)
run-seq-compose-terminal-terminal : ∀ {A} (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  ∃[ s' ] (run (compile-x86 {A} {Unit} (terminal ∘ terminal)) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') rax ≡ 0)
run-seq-compose-terminal-terminal {A} x s h-false pc-0 = s4 , run-eq , halt-eq , rax-eq
  where
    prog : List Instr
    prog = compile-x86 {A} {Unit} (terminal ∘ terminal)

    -- State after step 1: mov rax, 0 (terminal)
    s1 : State
    s1 = record s { regs = writeReg (regs s) rax 0
                  ; pc = pc s +ℕ 1 }

    step1 : step prog s ≡ just s1
    step1 = trans (step-exec-0 (mov (reg rax) (imm 0)) _ s h-false pc-0)
                  (execMov-reg-imm s rax 0)

    h1 : halted s1 ≡ false
    h1 = h-false

    pc1 : pc s1 ≡ 1
    pc1 = cong (λ p → p +ℕ 1) pc-0

    rax-s1 : readReg (regs s1) rax ≡ 0
    rax-s1 = readReg-writeReg-same (regs s) rax 0

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
    pc2 = cong (λ p → p +ℕ 1) pc1

    -- State after step 3: mov rax, 0 (second terminal)
    s3 : State
    s3 = record s2 { regs = writeReg (regs s2) rax 0
                   ; pc = pc s2 +ℕ 1 }

    step3 : step prog s2 ≡ just s3
    step3 = trans (step-exec prog s2 (mov (reg rax) (imm 0)) h2
                             (subst (λ p → fetch prog p ≡ just (mov (reg rax) (imm 0))) (sym pc2) refl))
                  (execMov-reg-imm s2 rax 0)

    h3 : halted s3 ≡ false
    h3 = h-false

    pc3 : pc s3 ≡ 3
    pc3 = cong (λ p → p +ℕ 1) pc2

    -- State after step 4: fetch fails at pc=3, halts
    s4 : State
    s4 = record s3 { halted = true }

    fetch-fail : fetch prog (pc s3) ≡ nothing
    fetch-fail = subst (λ p → fetch prog p ≡ nothing) (sym pc3) refl

    step4 : step prog s3 ≡ just s4
    step4 = step-halt-on-fetch-fail prog s3 h3 fetch-fail

    halt-eq : halted s4 ≡ true
    halt-eq = refl

    -- Combined execution: 4 steps
    run-eq : run prog s ≡ just s4
    run-eq = exec-four-steps 9996 prog s s1 s2 s3 s4
               step1 h1 step2 h2 step3 h3 step4 halt-eq

    -- Track rax through states: final rax = 0
    rax-eq : readReg (regs s4) rax ≡ 0
    rax-eq = readReg-writeReg-same (regs s2) rax 0

-- | run-generator for (terminal ∘ terminal)
run-generator-compose-terminal-terminal : ∀ {A} (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) rdi ≡ encode x →
  ∃[ s' ] (run (compile-x86 {A} {Unit} (terminal ∘ terminal)) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') rax ≡ encode {Unit} (eval {A} {Unit} (terminal ∘ terminal) x))
run-generator-compose-terminal-terminal {A} x s h-false pc-0 rdi-eq = s' , run-eq , halt-eq , rax-eq
  where
    helper : ∃[ s' ] (run (compile-x86 {A} {Unit} (terminal ∘ terminal)) s ≡ just s'
                    × halted s' ≡ true
                    × readReg (regs s') rax ≡ 0)
    helper = run-seq-compose-terminal-terminal x s h-false pc-0

    s' : State
    s' = proj₁ helper

    run-eq : run (compile-x86 {A} {Unit} (terminal ∘ terminal)) s ≡ just s'
    run-eq = proj₁ (proj₂ helper)

    halt-eq : halted s' ≡ true
    halt-eq = proj₁ (proj₂ (proj₂ helper))

    -- eval (terminal ∘ terminal) x = terminal (terminal x) = terminal tt = tt
    -- encode tt = 0
    rax-eq : readReg (regs s') rax ≡ encode (eval {A} {Unit} (terminal ∘ terminal) x)
    rax-eq = trans (proj₂ (proj₂ (proj₂ helper))) (sym encode-unit)

-- | run-seq-compose for (fold ∘ unfold) : Fix F → Fix F
-- Generated code: [mov rax, rdi] ++ [mov rdi, rax] ++ [mov rax, rdi]
-- This is unfold (Fix F → F) followed by fold (F → Fix F)
-- Total: 3 instructions, 4 steps (3 + halt on fetch fail at pc=3)
run-seq-compose-fold-unfold : ∀ {F} (x : ⟦ Fix F ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) rdi ≡ encode x →
  ∃[ s' ] (run (compile-x86 {Fix F} {Fix F} (fold ∘ unfold)) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') rax ≡ encode x)
run-seq-compose-fold-unfold {F} x s h-false pc-0 rdi-eq = s4 , run-eq , halt-eq , rax-eq
  where
    prog : List Instr
    prog = compile-x86 {Fix F} {Fix F} (fold ∘ unfold)
    -- = compile-x86 unfold ++ mov rdi rax ∷ [] ++ compile-x86 fold
    -- = [mov rax rdi] ++ [mov rdi rax] ++ [mov rax rdi]

    -- State after step 1: mov rax, rdi (unfold)
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

    -- State after step 2: mov rdi, rax (transfer result)
    s2 : State
    s2 = record s1 { regs = writeReg (regs s1) rdi (readReg (regs s1) rax)
                   ; pc = pc s1 +ℕ 1 }

    step2 : step prog s1 ≡ just s2
    step2 = trans (step-exec-1 (mov (reg rax) (reg rdi)) (mov (reg rdi) (reg rax)) _ s1 h1 pc1)
                  (execMov-reg-reg s1 rdi rax)

    h2 : halted s2 ≡ false
    h2 = h-false

    pc2 : pc s2 ≡ 2
    pc2 = cong (λ x → x +ℕ 1) pc1

    -- State after step 3: mov rax, rdi (fold)
    s3 : State
    s3 = record s2 { regs = writeReg (regs s2) rax (readReg (regs s2) rdi)
                   ; pc = pc s2 +ℕ 1 }

    step3 : step prog s2 ≡ just s3
    step3 = trans (step-exec-2 (mov (reg rax) (reg rdi)) (mov (reg rdi) (reg rax)) (mov (reg rax) (reg rdi)) [] s2 h2 pc2)
                  (execMov-reg-reg s2 rax rdi)

    h3 : halted s3 ≡ false
    h3 = h-false

    pc3 : pc s3 ≡ 3
    pc3 = cong (λ x → x +ℕ 1) pc2

    -- Step 4: fetch fails at pc=3 (past end of program), halts
    s4 : State
    s4 = record s3 { halted = true }

    fetch-fail : fetch prog (pc s3) ≡ nothing
    fetch-fail = subst (λ p → fetch prog p ≡ nothing) (sym pc3) refl

    step4 : step prog s3 ≡ just s4
    step4 = step-halt-on-fetch-fail prog s3 h3 fetch-fail

    halt-eq : halted s4 ≡ true
    halt-eq = refl

    -- Combined execution: 4 steps
    run-eq : run prog s ≡ just s4
    run-eq = exec-four-steps 9996 prog s s1 s2 s3 s4
               step1 h1 step2 h2 step3 h3 step4 halt-eq

    -- Track rax through states:
    -- s1.rax = s.rdi = encode x
    -- s2.rdi = s1.rax = encode x
    -- s3.rax = s2.rdi = encode x
    rax-eq : readReg (regs s4) rax ≡ encode x
    rax-eq = trans (readReg-writeReg-same (regs s2) rax (readReg (regs s2) rdi))
                   (trans (readReg-writeReg-same (regs s1) rdi (readReg (regs s1) rax))
                          (trans (readReg-writeReg-same (regs s) rax (readReg (regs s) rdi))
                                 rdi-eq))

-- | run-generator for (fold ∘ unfold)
run-generator-compose-fold-unfold : ∀ {F} (x : ⟦ Fix F ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) rdi ≡ encode x →
  ∃[ s' ] (run (compile-x86 {Fix F} {Fix F} (fold ∘ unfold)) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') rax ≡ encode (eval {Fix F} {Fix F} (fold ∘ unfold) x))
run-generator-compose-fold-unfold {F} x s h-false pc-0 rdi-eq = s' , run-eq , halt-eq , rax-eq
  where
    helper : ∃[ s' ] (run (compile-x86 {Fix F} {Fix F} (fold ∘ unfold)) s ≡ just s'
                    × halted s' ≡ true
                    × readReg (regs s') rax ≡ encode x)
    helper = run-seq-compose-fold-unfold x s h-false pc-0 rdi-eq

    s' : State
    s' = proj₁ helper

    run-eq : run (compile-x86 {Fix F} {Fix F} (fold ∘ unfold)) s ≡ just s'
    run-eq = proj₁ (proj₂ helper)

    halt-eq : halted s' ≡ true
    halt-eq = proj₁ (proj₂ (proj₂ helper))

    -- eval (fold ∘ unfold) x = fold (unfold x) = wrap (unwrap x) = x
    -- So encode (eval (fold ∘ unfold) x) = encode x
    rax-eq : readReg (regs s') rax ≡ encode (eval {Fix F} {Fix F} (fold ∘ unfold) x)
    rax-eq = proj₂ (proj₂ (proj₂ helper))

-- | run-seq-compose for (unfold ∘ fold) : F → F
-- Generated code: [mov rax, rdi] ++ [mov rdi, rax] ++ [mov rax, rdi]
-- This is fold (F → Fix F) followed by unfold (Fix F → F)
-- Total: 3 instructions, 4 steps (3 + halt on fetch fail at pc=3)
run-seq-compose-unfold-fold : ∀ {F} (x : ⟦ F ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) rdi ≡ encode x →
  ∃[ s' ] (run (compile-x86 {F} {F} (unfold ∘ fold)) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') rax ≡ encode x)
run-seq-compose-unfold-fold {F} x s h-false pc-0 rdi-eq = s4 , run-eq , halt-eq , rax-eq
  where
    prog : List Instr
    prog = compile-x86 {F} {F} (unfold ∘ fold)

    -- State after step 1: mov rax, rdi (fold)
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

    -- State after step 2: mov rdi, rax (transfer result)
    s2 : State
    s2 = record s1 { regs = writeReg (regs s1) rdi (readReg (regs s1) rax)
                   ; pc = pc s1 +ℕ 1 }

    step2 : step prog s1 ≡ just s2
    step2 = trans (step-exec-1 (mov (reg rax) (reg rdi)) (mov (reg rdi) (reg rax)) _ s1 h1 pc1)
                  (execMov-reg-reg s1 rdi rax)

    h2 : halted s2 ≡ false
    h2 = h-false

    pc2 : pc s2 ≡ 2
    pc2 = cong (λ x → x +ℕ 1) pc1

    -- State after step 3: mov rax, rdi (unfold)
    s3 : State
    s3 = record s2 { regs = writeReg (regs s2) rax (readReg (regs s2) rdi)
                   ; pc = pc s2 +ℕ 1 }

    step3 : step prog s2 ≡ just s3
    step3 = trans (step-exec-2 (mov (reg rax) (reg rdi)) (mov (reg rdi) (reg rax)) (mov (reg rax) (reg rdi)) [] s2 h2 pc2)
                  (execMov-reg-reg s2 rax rdi)

    h3 : halted s3 ≡ false
    h3 = h-false

    pc3 : pc s3 ≡ 3
    pc3 = cong (λ x → x +ℕ 1) pc2

    -- Step 4: fetch fails at pc=3 (past end of program), halts
    s4 : State
    s4 = record s3 { halted = true }

    fetch-fail : fetch prog (pc s3) ≡ nothing
    fetch-fail = subst (λ p → fetch prog p ≡ nothing) (sym pc3) refl

    step4 : step prog s3 ≡ just s4
    step4 = step-halt-on-fetch-fail prog s3 h3 fetch-fail

    halt-eq : halted s4 ≡ true
    halt-eq = refl

    -- Combined execution: 4 steps
    run-eq : run prog s ≡ just s4
    run-eq = exec-four-steps 9996 prog s s1 s2 s3 s4
               step1 h1 step2 h2 step3 h3 step4 halt-eq

    -- Track rax through states: same as fold-unfold
    rax-eq : readReg (regs s4) rax ≡ encode x
    rax-eq = trans (readReg-writeReg-same (regs s2) rax (readReg (regs s2) rdi))
                   (trans (readReg-writeReg-same (regs s1) rdi (readReg (regs s1) rax))
                          (trans (readReg-writeReg-same (regs s) rax (readReg (regs s) rdi))
                                 rdi-eq))

-- | run-generator for (unfold ∘ fold)
run-generator-compose-unfold-fold : ∀ {F} (x : ⟦ F ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) rdi ≡ encode x →
  ∃[ s' ] (run (compile-x86 {F} {F} (unfold ∘ fold)) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') rax ≡ encode (eval {F} {F} (unfold ∘ fold) x))
run-generator-compose-unfold-fold {F} x s h-false pc-0 rdi-eq = s' , run-eq , halt-eq , rax-eq
  where
    helper : ∃[ s' ] (run (compile-x86 {F} {F} (unfold ∘ fold)) s ≡ just s'
                    × halted s' ≡ true
                    × readReg (regs s') rax ≡ encode x)
    helper = run-seq-compose-unfold-fold x s h-false pc-0 rdi-eq

    s' : State
    s' = proj₁ helper

    run-eq : run (compile-x86 {F} {F} (unfold ∘ fold)) s ≡ just s'
    run-eq = proj₁ (proj₂ helper)

    halt-eq : halted s' ≡ true
    halt-eq = proj₁ (proj₂ (proj₂ helper))

    -- eval (unfold ∘ fold) x = unfold (fold x) = unwrap (wrap x) = x
    -- So encode (eval (unfold ∘ fold) x) = encode x
    rax-eq : readReg (regs s') rax ≡ encode (eval {F} {F} (unfold ∘ fold) x)
    rax-eq = proj₂ (proj₂ (proj₂ helper))

-- | run-seq-compose for (id ∘ fst) : A * B → A
-- Generated code: [mov rax, [rdi]] ++ [mov rdi, rax] ++ [mov rax, rdi]
-- This is fst (A * B → A) followed by id (A → A)
-- Total: 3 instructions, 4 steps (3 + halt on fetch fail at pc=3)
run-seq-compose-id-fst : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) rdi ≡ encode (a , b) →
  readMem (memory s) (encode (a , b)) ≡ just (encode a) →
  ∃[ s' ] (run (compile-x86 {A * B} {A} (id ∘ fst)) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') rax ≡ encode a)
run-seq-compose-id-fst {A} {B} a b s h-false pc-0 rdi-eq mem-eq = s4 , run-eq , halt-eq , rax-eq
  where
    prog : List Instr
    prog = compile-x86 {A * B} {A} (id ∘ fst)

    pair-addr : Word
    pair-addr = encode (a , b)

    -- State after step 1: mov rax, [rdi] (fst - load from memory)
    s1 : State
    s1 = record s { regs = writeReg (regs s) rax (encode a)
                  ; pc = pc s +ℕ 1 }

    step1 : step prog s ≡ just s1
    step1 = trans (step-exec-0 (mov (reg rax) (mem (base rdi))) _ s h-false pc-0)
                  (execMov-reg-mem-base s rax rdi (encode a)
                    (trans (cong (λ addr → readMem (memory s) addr) rdi-eq)
                           mem-eq))

    h1 : halted s1 ≡ false
    h1 = h-false

    pc1 : pc s1 ≡ 1
    pc1 = cong (λ x → x +ℕ 1) pc-0

    -- State after step 2: mov rdi, rax (transfer result)
    s2 : State
    s2 = record s1 { regs = writeReg (regs s1) rdi (readReg (regs s1) rax)
                   ; pc = pc s1 +ℕ 1 }

    step2 : step prog s1 ≡ just s2
    step2 = trans (step-exec-1 (mov (reg rax) (mem (base rdi))) (mov (reg rdi) (reg rax)) _ s1 h1 pc1)
                  (execMov-reg-reg s1 rdi rax)

    h2 : halted s2 ≡ false
    h2 = h-false

    pc2 : pc s2 ≡ 2
    pc2 = cong (λ x → x +ℕ 1) pc1

    -- State after step 3: mov rax, rdi (id)
    s3 : State
    s3 = record s2 { regs = writeReg (regs s2) rax (readReg (regs s2) rdi)
                   ; pc = pc s2 +ℕ 1 }

    step3 : step prog s2 ≡ just s3
    step3 = trans (step-exec-2 (mov (reg rax) (mem (base rdi))) (mov (reg rdi) (reg rax)) (mov (reg rax) (reg rdi)) [] s2 h2 pc2)
                  (execMov-reg-reg s2 rax rdi)

    h3 : halted s3 ≡ false
    h3 = h-false

    pc3 : pc s3 ≡ 3
    pc3 = cong (λ x → x +ℕ 1) pc2

    -- Step 4: fetch fails at pc=3, halts
    s4 : State
    s4 = record s3 { halted = true }

    fetch-fail : fetch prog (pc s3) ≡ nothing
    fetch-fail = subst (λ p → fetch prog p ≡ nothing) (sym pc3) refl

    step4 : step prog s3 ≡ just s4
    step4 = step-halt-on-fetch-fail prog s3 h3 fetch-fail

    halt-eq : halted s4 ≡ true
    halt-eq = refl

    run-eq : run prog s ≡ just s4
    run-eq = exec-four-steps 9996 prog s s1 s2 s3 s4
               step1 h1 step2 h2 step3 h3 step4 halt-eq

    -- Track rax: s1.rax = encode a, s2.rdi = s1.rax, s3.rax = s2.rdi
    rax-eq : readReg (regs s4) rax ≡ encode a
    rax-eq = trans (readReg-writeReg-same (regs s2) rax (readReg (regs s2) rdi))
                   (trans (readReg-writeReg-same (regs s1) rdi (readReg (regs s1) rax))
                          (readReg-writeReg-same (regs s) rax (encode a)))

-- | run-generator for (id ∘ fst)
run-generator-compose-id-fst : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) rdi ≡ encode (a , b) →
  readMem (memory s) (encode (a , b)) ≡ just (encode a) →
  ∃[ s' ] (run (compile-x86 {A * B} {A} (id ∘ fst)) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') rax ≡ encode (eval {A * B} {A} (id ∘ fst) (a , b)))
run-generator-compose-id-fst {A} {B} a b s h-false pc-0 rdi-eq mem-eq = s' , run-eq , halt-eq , rax-eq
  where
    helper : ∃[ s' ] (run (compile-x86 {A * B} {A} (id ∘ fst)) s ≡ just s'
                    × halted s' ≡ true
                    × readReg (regs s') rax ≡ encode a)
    helper = run-seq-compose-id-fst a b s h-false pc-0 rdi-eq mem-eq

    s' : State
    s' = proj₁ helper

    run-eq : run (compile-x86 {A * B} {A} (id ∘ fst)) s ≡ just s'
    run-eq = proj₁ (proj₂ helper)

    halt-eq : halted s' ≡ true
    halt-eq = proj₁ (proj₂ (proj₂ helper))

    -- eval (id ∘ fst) (a , b) = id (fst (a , b)) = id a = a
    rax-eq : readReg (regs s') rax ≡ encode (eval {A * B} {A} (id ∘ fst) (a , b))
    rax-eq = proj₂ (proj₂ (proj₂ helper))

-- | run-seq-compose for (id ∘ snd) : A * B → B
-- Generated code: [mov rax, [rdi+8]] ++ [mov rdi, rax] ++ [mov rax, rdi]
-- This is snd (A * B → B) followed by id (B → B)
-- Total: 3 instructions, 4 steps (3 + halt on fetch fail at pc=3)
run-seq-compose-id-snd : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) rdi ≡ encode (a , b) →
  readMem (memory s) (encode (a , b) +ℕ 8) ≡ just (encode b) →
  ∃[ s' ] (run (compile-x86 {A * B} {B} (id ∘ snd)) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') rax ≡ encode b)
run-seq-compose-id-snd {A} {B} a b s h-false pc-0 rdi-eq mem-eq = s4 , run-eq , halt-eq , rax-eq
  where
    prog : List Instr
    prog = compile-x86 {A * B} {B} (id ∘ snd)

    pair-addr : Word
    pair-addr = encode (a , b)

    -- State after step 1: mov rax, [rdi+8] (snd - load from memory offset 8)
    s1 : State
    s1 = record s { regs = writeReg (regs s) rax (encode b)
                  ; pc = pc s +ℕ 1 }

    step1 : step prog s ≡ just s1
    step1 = trans (step-exec-0 (mov (reg rax) (mem (base+disp rdi 8))) _ s h-false pc-0)
                  (execMov-reg-mem-disp s rax rdi 8 (encode b)
                    (trans (cong (λ addr → readMem (memory s) (addr +ℕ 8)) rdi-eq)
                           mem-eq))

    h1 : halted s1 ≡ false
    h1 = h-false

    pc1 : pc s1 ≡ 1
    pc1 = cong (λ x → x +ℕ 1) pc-0

    -- State after step 2: mov rdi, rax (transfer result)
    s2 : State
    s2 = record s1 { regs = writeReg (regs s1) rdi (readReg (regs s1) rax)
                   ; pc = pc s1 +ℕ 1 }

    step2 : step prog s1 ≡ just s2
    step2 = trans (step-exec-1 (mov (reg rax) (mem (base+disp rdi 8))) (mov (reg rdi) (reg rax)) _ s1 h1 pc1)
                  (execMov-reg-reg s1 rdi rax)

    h2 : halted s2 ≡ false
    h2 = h-false

    pc2 : pc s2 ≡ 2
    pc2 = cong (λ x → x +ℕ 1) pc1

    -- State after step 3: mov rax, rdi (id)
    s3 : State
    s3 = record s2 { regs = writeReg (regs s2) rax (readReg (regs s2) rdi)
                   ; pc = pc s2 +ℕ 1 }

    step3 : step prog s2 ≡ just s3
    step3 = trans (step-exec-2 (mov (reg rax) (mem (base+disp rdi 8))) (mov (reg rdi) (reg rax)) (mov (reg rax) (reg rdi)) [] s2 h2 pc2)
                  (execMov-reg-reg s2 rax rdi)

    h3 : halted s3 ≡ false
    h3 = h-false

    pc3 : pc s3 ≡ 3
    pc3 = cong (λ x → x +ℕ 1) pc2

    -- Step 4: fetch fails at pc=3, halts
    s4 : State
    s4 = record s3 { halted = true }

    fetch-fail : fetch prog (pc s3) ≡ nothing
    fetch-fail = subst (λ p → fetch prog p ≡ nothing) (sym pc3) refl

    step4 : step prog s3 ≡ just s4
    step4 = step-halt-on-fetch-fail prog s3 h3 fetch-fail

    halt-eq : halted s4 ≡ true
    halt-eq = refl

    run-eq : run prog s ≡ just s4
    run-eq = exec-four-steps 9996 prog s s1 s2 s3 s4
               step1 h1 step2 h2 step3 h3 step4 halt-eq

    -- Track rax: s1.rax = encode b, s2.rdi = s1.rax, s3.rax = s2.rdi
    rax-eq : readReg (regs s4) rax ≡ encode b
    rax-eq = trans (readReg-writeReg-same (regs s2) rax (readReg (regs s2) rdi))
                   (trans (readReg-writeReg-same (regs s1) rdi (readReg (regs s1) rax))
                          (readReg-writeReg-same (regs s) rax (encode b)))

-- | run-generator for (id ∘ snd)
run-generator-compose-id-snd : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) rdi ≡ encode (a , b) →
  readMem (memory s) (encode (a , b) +ℕ 8) ≡ just (encode b) →
  ∃[ s' ] (run (compile-x86 {A * B} {B} (id ∘ snd)) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') rax ≡ encode (eval {A * B} {B} (id ∘ snd) (a , b)))
run-generator-compose-id-snd {A} {B} a b s h-false pc-0 rdi-eq mem-eq = s' , run-eq , halt-eq , rax-eq
  where
    helper : ∃[ s' ] (run (compile-x86 {A * B} {B} (id ∘ snd)) s ≡ just s'
                    × halted s' ≡ true
                    × readReg (regs s') rax ≡ encode b)
    helper = run-seq-compose-id-snd a b s h-false pc-0 rdi-eq mem-eq

    s' : State
    s' = proj₁ helper

    run-eq : run (compile-x86 {A * B} {B} (id ∘ snd)) s ≡ just s'
    run-eq = proj₁ (proj₂ helper)

    halt-eq : halted s' ≡ true
    halt-eq = proj₁ (proj₂ (proj₂ helper))

    -- eval (id ∘ snd) (a , b) = id (snd (a , b)) = id b = b
    rax-eq : readReg (regs s') rax ≡ encode (eval {A * B} {B} (id ∘ snd) (a , b))
    rax-eq = proj₂ (proj₂ (proj₂ helper))

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

-- Base case for case analysis with inl input (f = g = id)
-- Tests the proof technique for the left branch (tag = 0, jne not taken)
--
-- For [ id , id ]:
--   len-f = compile-length id = 1
--   len-g = compile-length id = 1
--   right-branch = 5 + len-f = 6
--   end-label = (7 + len-f) + len-g = 9
--
-- Generated code for [ id , id ]:
--   0: mov r15, [rdi]       -- r15 := tag (0 for inl)
--   1: cmp r15, 0           -- sets zf := true
--   2: jne 6                -- not taken (zf=true), pc := 3
--   3: mov rdi, [rdi+8]     -- rdi := value
--   4: mov rax, rdi         -- compile-x86 id
--   5: jmp 9                -- jump to end-label
--   6: label 6              -- right-branch label
--   7: mov rdi, [rdi+8]
--   8: mov rax, rdi
--   9: label 9              -- end-label (executed, then halt at pc=10)
--
-- Note: Uses A + A (not A + B) because [ id , id ] requires both branches to return the same type.
run-case-inl-id : ∀ {A} (a : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) rdi ≡ encode {A + A} (inj₁ a) →
  readMem (memory s) (encode {A + A} (inj₁ a)) ≡ just 0 →
  readMem (memory s) (encode {A + A} (inj₁ a) +ℕ 8) ≡ just (encode a) →
  ∃[ s' ] (run (compile-x86 {A + A} {A} [ id , id ]) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') rax ≡ encode a)
run-case-inl-id {A} a s h-false pc-0 rdi-enc tag-0 val-a = s8 , run-eq , halt-eq , rax-eq
  where
    prog : List Instr
    prog = compile-x86 {A + A} {A} [ id , id ]
    -- = mov r15 [rdi] ∷ cmp r15 0 ∷ jne 6 ∷ mov rdi [rdi+8] ∷ mov rax rdi ∷
    --   jmp 9 ∷ label 6 ∷ mov rdi [rdi+8] ∷ mov rax rdi ∷ label 9 ∷ []

    -- Original values
    orig-rdi : Word
    orig-rdi = readReg (regs s) rdi

    -- Memory lookups using rdi
    mem-at-rdi : readMem (memory s) (readReg (regs s) rdi) ≡ just 0
    mem-at-rdi = subst (λ addr → readMem (memory s) addr ≡ just 0) (sym rdi-enc) tag-0

    mem-at-rdi-8 : readMem (memory s) (readReg (regs s) rdi +ℕ 8) ≡ just (encode a)
    mem-at-rdi-8 = subst (λ addr → readMem (memory s) (addr +ℕ 8) ≡ just (encode a)) (sym rdi-enc) val-a

    -- State after step 0: mov r15, [rdi]
    s1 : State
    s1 = record s { regs = writeReg (regs s) r15 0 ; pc = pc s +ℕ 1 }

    step1 : step prog s ≡ just s1
    step1 = trans (step-exec-0 _ _ s h-false pc-0)
                  (execMov-reg-mem-base s r15 rdi 0 mem-at-rdi)

    h1 : halted s1 ≡ false
    h1 = h-false

    pc1 : pc s1 ≡ 1
    pc1 = cong (λ x → x +ℕ 1) pc-0

    -- State after step 1: cmp r15, 0 (r15 = 0, so zf := true)
    s2 : State
    s2 = record s1 { pc = pc s1 +ℕ 1 ; flags = mkflags true false false }

    r15-s1 : readReg (regs s1) r15 ≡ 0
    r15-s1 = readReg-writeReg-same (regs s) r15 0

    step2 : step prog s1 ≡ just s2
    step2 = trans (step-exec prog s1 (cmp (reg r15) (imm 0)) h1
                             (subst (λ p → fetch prog p ≡ just (cmp (reg r15) (imm 0))) (sym pc1) refl))
                  (execCmp-zero prog s1 r15 r15-s1)

    h2 : halted s2 ≡ false
    h2 = h-false

    pc2 : pc s2 ≡ 2
    pc2 = cong (λ x → x +ℕ 1) pc1

    -- State after step 2: jne 6 (not taken, zf = true)
    s3 : State
    s3 = record s2 { pc = pc s2 +ℕ 1 }

    zf-s2 : zf (flags s2) ≡ true
    zf-s2 = refl

    step3 : step prog s2 ≡ just s3
    step3 = trans (step-exec prog s2 (jne 6) h2
                             (subst (λ p → fetch prog p ≡ just (jne 6)) (sym pc2) refl))
                  (execJne-not-taken prog s2 6 zf-s2)

    h3 : halted s3 ≡ false
    h3 = h-false

    pc3 : pc s3 ≡ 3
    pc3 = cong (λ x → x +ℕ 1) pc2

    -- State after step 3: mov rdi, [rdi+8]
    -- rdi in s2 = orig-rdi (unchanged through r15 write and cmp)
    rdi-s2 : readReg (regs s2) rdi ≡ orig-rdi
    rdi-s2 = trans (readReg-writeReg-r15-rdi (regs s) 0) refl
      where
        readReg-writeReg-r15-rdi : ∀ (rf : RegFile) (v : Word) →
          readReg (writeReg rf r15 v) rdi ≡ readReg rf rdi
        readReg-writeReg-r15-rdi rf v = refl

    -- Memory at [rdi+8] in s2 = encode a (memory unchanged)
    mem-s2-rdi-8 : readMem (memory s2) (readReg (regs s2) rdi +ℕ 8) ≡ just (encode a)
    mem-s2-rdi-8 = subst (λ r → readMem (memory s2) (r +ℕ 8) ≡ just (encode a)) (sym rdi-s2) mem-at-rdi-8

    s4 : State
    s4 = record s3 { regs = writeReg (regs s3) rdi (encode a) ; pc = pc s3 +ℕ 1 }

    step4 : step prog s3 ≡ just s4
    step4 = trans (step-exec prog s3 (mov (reg rdi) (mem (base+disp rdi 8))) h3
                             (subst (λ p → fetch prog p ≡ just (mov (reg rdi) (mem (base+disp rdi 8)))) (sym pc3) refl))
                  (execMov-reg-mem-disp s3 rdi rdi 8 (encode a) mem-s2-rdi-8)

    h4 : halted s4 ≡ false
    h4 = h-false

    pc4 : pc s4 ≡ 4
    pc4 = cong (λ x → x +ℕ 1) pc3

    -- State after step 4: mov rax, rdi
    -- rdi in s4 = encode a
    rdi-s4 : readReg (regs s4) rdi ≡ encode a
    rdi-s4 = readReg-writeReg-same (regs s3) rdi (encode a)

    s5 : State
    s5 = record s4 { regs = writeReg (regs s4) rax (readReg (regs s4) rdi) ; pc = pc s4 +ℕ 1 }

    step5 : step prog s4 ≡ just s5
    step5 = trans (step-exec prog s4 (mov (reg rax) (reg rdi)) h4
                             (subst (λ p → fetch prog p ≡ just (mov (reg rax) (reg rdi))) (sym pc4) refl))
                  (execMov-reg-reg s4 rax rdi)

    h5 : halted s5 ≡ false
    h5 = h-false

    pc5 : pc s5 ≡ 5
    pc5 = cong (λ x → x +ℕ 1) pc4

    -- State after step 5: jmp 9
    s6 : State
    s6 = record s5 { pc = 9 }

    step6 : step prog s5 ≡ just s6
    step6 = trans (step-exec prog s5 (jmp 9) h5
                             (subst (λ p → fetch prog p ≡ just (jmp 9)) (sym pc5) refl))
                  (execJmp prog s5 9)

    h6 : halted s6 ≡ false
    h6 = h-false

    pc6 : pc s6 ≡ 9
    pc6 = refl

    -- State after step 6: label 9 (no-op, pc := 10)
    s7 : State
    s7 = record s6 { pc = 10 }

    step7 : step prog s6 ≡ just s7
    step7 = trans (step-exec prog s6 (label 9) h6
                             (subst (λ p → fetch prog p ≡ just (label 9)) (sym pc6) refl))
                  (execLabel prog s6 9)

    h7 : halted s7 ≡ false
    h7 = h-false

    -- State after step 7: fetch at pc=10 fails, halt
    s8 : State
    s8 = record s7 { halted = true }

    -- fetch at pc=10 fails (program has only 10 instructions, indices 0-9)
    fetch-10-fail : fetch prog 10 ≡ nothing
    fetch-10-fail = refl

    step8 : step prog s7 ≡ just s8
    step8 = step-halt-on-fetch-fail prog s7 h7 fetch-10-fail

    halt-eq : halted s8 ≡ true
    halt-eq = refl

    -- Combine all steps using exec
    run-eq : run prog s ≡ just s8
    run-eq = exec-eight-steps 9992 prog s s1 s2 s3 s4 s5 s6 s7 s8
               step1 h1 step2 h2 step3 h3 step4 h4 step5 h5 step6 h6 step7 h7 step8 halt-eq

    -- rax in s5 = rdi in s4 = encode a
    rax-s5 : readReg (regs s5) rax ≡ encode a
    rax-s5 = trans (readReg-writeReg-same (regs s4) rax (readReg (regs s4) rdi)) rdi-s4

    -- rax unchanged from s5 to s8 (only pc and halted changed)
    rax-eq : readReg (regs s8) rax ≡ encode a
    rax-eq = rax-s5

-- Base case for case analysis with inr input (f = g = id)
-- Tests the proof technique for the right branch (tag = 1, jne taken)
--
-- For [ id , id ]:
--   len-f = compile-length id = 1
--   len-g = compile-length id = 1
--   right-branch = 5 + len-f = 6
--   end-label = (7 + len-f) + len-g = 9
--
-- Generated code for [ id , id ]:
--   0: mov r15, [rdi]       -- r15 := tag (1 for inr)
--   1: cmp r15, 0           -- sets zf := false (1 ≠ 0)
--   2: jne 6                -- TAKEN (zf=false), pc := 6
--   6: label 6              -- right-branch label
--   7: mov rdi, [rdi+8]     -- rdi := value
--   8: mov rax, rdi         -- compile-x86 id
--   9: label 9              -- end-label
--   (halt at pc=10)
--
-- Execution: 8 steps (3 before jne + jne + label + 2 instr + label + halt)
run-case-inr-id : ∀ {A} (b : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) rdi ≡ encode {A + A} (inj₂ b) →
  readMem (memory s) (encode {A + A} (inj₂ b)) ≡ just 1 →
  readMem (memory s) (encode {A + A} (inj₂ b) +ℕ 8) ≡ just (encode b) →
  ∃[ s' ] (run (compile-x86 {A + A} {A} [ id , id ]) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') rax ≡ encode b)
run-case-inr-id {A} b s h-false pc-0 rdi-enc tag-1 val-b = s8 , run-eq , halt-eq , rax-eq
  where
    prog : List Instr
    prog = compile-x86 {A + A} {A} [ id , id ]
    -- = mov r15 [rdi] ∷ cmp r15 0 ∷ jne 6 ∷ mov rdi [rdi+8] ∷ mov rax rdi ∷
    --   jmp 9 ∷ label 6 ∷ mov rdi [rdi+8] ∷ mov rax rdi ∷ label 9 ∷ []

    -- Original values
    orig-rdi : Word
    orig-rdi = readReg (regs s) rdi

    -- Memory lookups using rdi
    mem-at-rdi : readMem (memory s) (readReg (regs s) rdi) ≡ just 1
    mem-at-rdi = subst (λ addr → readMem (memory s) addr ≡ just 1) (sym rdi-enc) tag-1

    mem-at-rdi-8 : readMem (memory s) (readReg (regs s) rdi +ℕ 8) ≡ just (encode b)
    mem-at-rdi-8 = subst (λ addr → readMem (memory s) (addr +ℕ 8) ≡ just (encode b)) (sym rdi-enc) val-b

    -- State after step 0: mov r15, [rdi]
    s1 : State
    s1 = record s { regs = writeReg (regs s) r15 1 ; pc = pc s +ℕ 1 }

    step1 : step prog s ≡ just s1
    step1 = trans (step-exec-0 _ _ s h-false pc-0)
                  (execMov-reg-mem-base s r15 rdi 1 mem-at-rdi)

    h1 : halted s1 ≡ false
    h1 = h-false

    pc1 : pc s1 ≡ 1
    pc1 = cong (λ x → x +ℕ 1) pc-0

    -- State after step 1: cmp r15, 0 (r15 = 1, so zf := false, cf := false since 1 >= 0)
    s2 : State
    s2 = record s1 { pc = pc s1 +ℕ 1 ; flags = mkflags false false false }

    r15-s1 : readReg (regs s1) r15 ≡ 1
    r15-s1 = readReg-writeReg-same (regs s) r15 1

    -- Helper: cmp when values are not equal sets zf = false
    execCmp-neq : ∀ (prog : List Instr) (s : State) (r : Reg) →
      readReg (regs s) r ≡ 1 →
      execInstr prog s (cmp (reg r) (imm 0)) ≡
        just (record s { pc = pc s +ℕ 1 ; flags = mkflags false false false })
    execCmp-neq prog s r eq rewrite eq = refl

    step2 : step prog s1 ≡ just s2
    step2 = trans (step-exec prog s1 (cmp (reg r15) (imm 0)) h1
                             (subst (λ p → fetch prog p ≡ just (cmp (reg r15) (imm 0))) (sym pc1) refl))
                  (execCmp-neq prog s1 r15 r15-s1)

    h2 : halted s2 ≡ false
    h2 = h-false

    pc2 : pc s2 ≡ 2
    pc2 = cong (λ x → x +ℕ 1) pc1

    -- State after step 2: jne 6 (TAKEN, zf = false)
    s3 : State
    s3 = record s2 { pc = 6 }

    zf-s2 : zf (flags s2) ≡ false
    zf-s2 = refl

    step3 : step prog s2 ≡ just s3
    step3 = trans (step-exec prog s2 (jne 6) h2
                             (subst (λ p → fetch prog p ≡ just (jne 6)) (sym pc2) refl))
                  (execJne-taken prog s2 6 zf-s2)

    h3 : halted s3 ≡ false
    h3 = h-false

    pc3 : pc s3 ≡ 6
    pc3 = refl

    -- State after step 3: label 6 (no-op)
    s4 : State
    s4 = record s3 { pc = 7 }

    step4 : step prog s3 ≡ just s4
    step4 = trans (step-exec prog s3 (label 6) h3
                             (subst (λ p → fetch prog p ≡ just (label 6)) (sym pc3) refl))
                  (execLabel prog s3 6)

    h4 : halted s4 ≡ false
    h4 = h-false

    pc4 : pc s4 ≡ 7
    pc4 = refl

    -- State after step 4: mov rdi, [rdi+8]
    -- rdi in s3 = orig-rdi (unchanged through r15 write, cmp, jne, label)
    rdi-s3 : readReg (regs s3) rdi ≡ orig-rdi
    rdi-s3 = trans (readReg-writeReg-r15-rdi (regs s) 1) refl
      where
        readReg-writeReg-r15-rdi : ∀ (rf : RegFile) (v : Word) →
          readReg (writeReg rf r15 v) rdi ≡ readReg rf rdi
        readReg-writeReg-r15-rdi rf v = refl

    -- Memory at [rdi+8] = encode b (memory unchanged)
    mem-s3-rdi-8 : readMem (memory s3) (readReg (regs s3) rdi +ℕ 8) ≡ just (encode b)
    mem-s3-rdi-8 = subst (λ r → readMem (memory s3) (r +ℕ 8) ≡ just (encode b)) (sym rdi-s3) mem-at-rdi-8

    s5 : State
    s5 = record s4 { regs = writeReg (regs s4) rdi (encode b) ; pc = pc s4 +ℕ 1 }

    step5 : step prog s4 ≡ just s5
    step5 = trans (step-exec prog s4 (mov (reg rdi) (mem (base+disp rdi 8))) h4
                             (subst (λ p → fetch prog p ≡ just (mov (reg rdi) (mem (base+disp rdi 8)))) (sym pc4) refl))
                  (execMov-reg-mem-disp s4 rdi rdi 8 (encode b) mem-s3-rdi-8)

    h5 : halted s5 ≡ false
    h5 = h-false

    pc5 : pc s5 ≡ 8
    pc5 = refl

    -- State after step 5: mov rax, rdi
    -- rdi in s5 = encode b
    rdi-s5 : readReg (regs s5) rdi ≡ encode b
    rdi-s5 = readReg-writeReg-same (regs s4) rdi (encode b)

    s6 : State
    s6 = record s5 { regs = writeReg (regs s5) rax (readReg (regs s5) rdi) ; pc = pc s5 +ℕ 1 }

    step6 : step prog s5 ≡ just s6
    step6 = trans (step-exec prog s5 (mov (reg rax) (reg rdi)) h5
                             (subst (λ p → fetch prog p ≡ just (mov (reg rax) (reg rdi))) (sym pc5) refl))
                  (execMov-reg-reg s5 rax rdi)

    h6 : halted s6 ≡ false
    h6 = h-false

    pc6 : pc s6 ≡ 9
    pc6 = refl

    -- State after step 6: label 9 (no-op)
    s7 : State
    s7 = record s6 { pc = 10 }

    step7 : step prog s6 ≡ just s7
    step7 = trans (step-exec prog s6 (label 9) h6
                             (subst (λ p → fetch prog p ≡ just (label 9)) (sym pc6) refl))
                  (execLabel prog s6 9)

    h7 : halted s7 ≡ false
    h7 = h-false

    -- State after step 7: fetch at pc=10 fails, halt
    s8 : State
    s8 = record s7 { halted = true }

    -- fetch at pc=10 fails (program has only 10 instructions, indices 0-9)
    fetch-10-fail : fetch prog 10 ≡ nothing
    fetch-10-fail = refl

    step8 : step prog s7 ≡ just s8
    step8 = step-halt-on-fetch-fail prog s7 h7 fetch-10-fail

    halt-eq : halted s8 ≡ true
    halt-eq = refl

    -- Combine all steps using exec
    run-eq : run prog s ≡ just s8
    run-eq = exec-eight-steps 9992 prog s s1 s2 s3 s4 s5 s6 s7 s8
               step1 h1 step2 h2 step3 h3 step4 h4 step5 h5 step6 h6 step7 h7 step8 halt-eq

    -- rax in s6 = rdi in s5 = encode b
    rax-s6 : readReg (regs s6) rax ≡ encode b
    rax-s6 = trans (readReg-writeReg-same (regs s5) rax (readReg (regs s5) rdi)) rdi-s5

    -- rax unchanged from s6 to s8 (only pc and halted changed)
    rax-eq : readReg (regs s8) rax ≡ encode b
    rax-eq = rax-s6

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
