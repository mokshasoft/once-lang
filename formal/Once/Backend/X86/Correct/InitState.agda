------------------------------------------------------------------------
-- Once.Backend.X86.Correct.InitState
--
-- Initial state setup for x86-64 execution.
-- These are independent (Level 0) - no dependencies on other Correct/* modules.
--
-- KEY CHANGES:
-- 1. Parameterized over abstract StackPointer/HeapPointer (no magic numbers)
-- 2. Uses stateful encoding to properly allocate input values in memory
-- 3. Stack capacity comes from StackPointer's interval membership
------------------------------------------------------------------------

module Once.Backend.X86.Correct.InitState where

open import Once.Type
open import Once.Semantics  -- Word is from X86.Semantics

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State
open Once.Backend.X86.Semantics.Flags

-- Import stateful encoding (replaces postulated encode)
open import Once.StatefulEncoding
  using (encode-s;
         encode-pair-fst-thm; encode-pair-snd-thm;
         encode-inl-tag-thm; encode-inl-val-thm;
         encode-inr-tag-thm; encode-inr-val-thm)
open import Once.Memory
  using (AllocState; alloc-state; heap-ptr; init-alloc-state)
  renaming (mem to alloc-mem)
import Once.Memory as Mem

-- Import validity predicates (both abstract and stateful versions)
open import Once.Backend.X86.Correct.MemoryValid
  using (PairAt; pair-at; InlAt; inl-at; InrAt; inr-at;
         PairAtS; pair-at-s; InlAtS; inl-at-s; InrAtS; inr-at-s)

open import Once.Postulates
  using (encode)

-- Import StackInvariant for initial state proof
open import Once.Backend.X86.Correct.StackInvariant
  using (StackInvariant; RbpInvariant; r15-in-heap)
-- Import encode-in-heap-sem for proving r15 is in heap
open import Once.Backend.X86.Correct.StackInstantiation
  using (encode-in-heap-sem)
open import Once.Backend.X86.Layout
  using (StackPointer; HeapPointer; InStack; InHeap; in-stack)
open import Once.Backend.X86.Layout using () renaming (addr to sp-addr; haddr to hp-addr)

open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Initial State Setup (Parameterized)
------------------------------------------------------------------------

-- | Create initial state with input in rdi
--
-- Now parameterized over StackPointer - no hard-coded addresses!
-- The StackPointer bundles:
--   - addr: the stack base address (abstract)
--   - in-stack: proof that addr is in the stack region
--
-- Sets up machine state ready to execute generated code:
--   - rdi contains encoded input
--   - r15 contains encoded input (always in heap - eliminates r15-unused case)
--   - Memory contains encoded heap objects
--   - rsp = rbp = sp.addr (stack pointer = frame pointer at entry)
--   - pc = 0
--   - halted = false
initWithInput : ∀ {A} → (sp : StackPointer) → ⟦ A ⟧ → State
initWithInput {A} sp x = mkstate
  (writeReg (writeReg (writeReg (writeReg emptyRegFile rdi (encode x)) rsp (sp-addr sp)) rbp (sp-addr sp)) r15 (encode x))
  encodedMemory
  initFlags
  0
  false
  where
    -- Memory containing encoded values
    -- The encoding postulates (encode-pair-fst, encode-inl-tag, etc.) in
    -- Once.Postulates already assert that reading from any memory at
    -- encode addresses returns the correct components. This models a
    -- "magic heap" where all semantic values are pre-allocated.
    -- We use emptyMemory here; the encoding postulates handle the rest.
    encodedMemory : Memory
    encodedMemory = emptyMemory

-- | The input is placed in rdi (proven from definition)
initWithInput-rdi : ∀ {A} (sp : StackPointer) (x : ⟦ A ⟧) →
  readReg (regs (initWithInput sp x)) rdi ≡ encode x
initWithInput-rdi sp x = refl

-- | Initial state is not halted (proven from definition)
initWithInput-halted : ∀ {A} (sp : StackPointer) (x : ⟦ A ⟧) → halted (initWithInput sp x) ≡ false
initWithInput-halted sp x = refl

-- | Initial state has pc = 0 (proven from definition)
initWithInput-pc : ∀ {A} (sp : StackPointer) (x : ⟦ A ⟧) → pc (initWithInput sp x) ≡ 0
initWithInput-pc sp x = refl

-- | Initial state satisfies StackInvariant (r15 in heap)
-- The initial state sets r15 = encode x, which is in heap
initWithInput-stack-inv : ∀ {A} (sp : StackPointer) (x : ⟦ A ⟧) → StackInvariant (initWithInput sp x)
initWithInput-stack-inv {A} sp x = r15-in-heap (encode-in-heap-sem x)
  -- r15 = encode x, and encode-in-heap-sem proves encode x is in heap

-- | Initial state has sufficient stack capacity
open import Data.Nat using (ℕ; _>_; _≤_)
open import Data.Nat.Properties using (≤-refl)
open import Once.Backend.X86.Correct.StackInstantiation
  using (StackCapacity; rsp-bound-to-capacity; capacity-2-to-rsp-bound; slots; pair-alloc)

-- | Stack capacity for initial state
-- The capacity comes from the StackPointer's properties.
-- We require that the caller provides a StackPointer with sufficient capacity.
initWithInput-stack-capacity : ∀ {A} (sp : StackPointer) (x : ⟦ A ⟧) →
  sp-addr sp > pair-alloc →
  StackCapacity (initWithInput sp x) 2
initWithInput-stack-capacity sp x addr-bound =
  rsp-bound-to-capacity 2 (initWithInput sp x) (in-stack sp) addr-bound

-- | Initial state has sufficient rsp (derived from capacity)
initWithInput-rsp-sufficient : ∀ {A} (sp : StackPointer) (x : ⟦ A ⟧) →
  sp-addr sp > pair-alloc →
  readReg (regs (initWithInput sp x)) rsp > pair-alloc
initWithInput-rsp-sufficient sp x addr-bound =
  capacity-2-to-rsp-bound (initWithInput sp x) (initWithInput-stack-capacity sp x addr-bound)

-- | Initial state satisfies RbpInvariant
-- Both rsp and rbp are set to sp.addr. The rbp-frame is the initial stack frame.
initWithInput-rbp-inv : ∀ {A} (sp : StackPointer) (x : ⟦ A ⟧) → RbpInvariant (initWithInput sp x)
initWithInput-rbp-inv sp x = record
  { rbp-frame = sp
  ; rbp-is-base = refl   -- rbp = sp.addr = sp-addr sp
  ; frame-bound = ≤-refl -- sp-addr sp ≥ sp-addr sp = rsp
  }

------------------------------------------------------------------------
-- Stateful Initial State Setup (Parameterized)
------------------------------------------------------------------------

-- | Record containing the initial state plus validity evidence
record InitResult (A : Type) : Set where
  field
    state : State              -- The machine state
    alloc : AllocState         -- Final allocation state
    input-addr : Word          -- Address where input is encoded
    rdi-eq : readReg (regs state) rdi ≡ input-addr

open InitResult public

-- | Create initial state with STATEFUL encoding
--
-- Now parameterized over StackPointer AND HeapPointer!
-- - StackPointer provides the stack base address
-- - HeapPointer provides the heap start address for allocation
--
-- Unlike initWithInput, this version:
--   1. Actually allocates x in memory using encode-s
--   2. Uses that memory in the State
--   3. Returns the allocation address
--
-- The key property: memory ACTUALLY contains the encoded value,
-- so encoding theorems can be applied without postulates.
initWithInputStateful : ∀ {A} → (sp : StackPointer) → (hp : HeapPointer) → ⟦ A ⟧ → InitResult A
initWithInputStateful {A} sp hp x = record
  { state = mkstate
      (writeReg (writeReg (writeReg emptyRegFile rdi x-addr) rsp (sp-addr sp)) rbp (sp-addr sp))
      (alloc-mem x-alloc)  -- Use the memory with allocated x!
      initFlags
      0
      false
  ; alloc = x-alloc
  ; input-addr = x-addr
  ; rdi-eq = refl
  }
  where
    -- Start with heap at the provided HeapPointer address
    init-heap : AllocState
    init-heap = alloc-state emptyMemory (hp-addr hp)

    -- Encode x, allocating it in memory
    encode-result : Word × AllocState
    encode-result = encode-s {A} x init-heap

    x-addr : Word
    x-addr = proj₁ encode-result

    x-alloc : AllocState
    x-alloc = proj₂ encode-result

-- | The stateful input is placed in rdi
initWithInputStateful-rdi : ∀ {A} (sp : StackPointer) (hp : HeapPointer) (x : ⟦ A ⟧) →
  readReg (regs (state (initWithInputStateful sp hp x))) rdi ≡ input-addr (initWithInputStateful sp hp x)
initWithInputStateful-rdi sp hp x = rdi-eq (initWithInputStateful sp hp x)

-- | Stateful initial state is not halted
initWithInputStateful-halted : ∀ {A} (sp : StackPointer) (hp : HeapPointer) (x : ⟦ A ⟧) →
  halted (state (initWithInputStateful sp hp x)) ≡ false
initWithInputStateful-halted sp hp x = refl

-- | Stateful initial state has pc = 0
initWithInputStateful-pc : ∀ {A} (sp : StackPointer) (hp : HeapPointer) (x : ⟦ A ⟧) →
  pc (state (initWithInputStateful sp hp x)) ≡ 0
initWithInputStateful-pc sp hp x = refl

-- Additional imports for validity lemmas
open import Data.Maybe using (just)
open import Data.Nat using () renaming (_+_ to _+ℕ_)

------------------------------------------------------------------------
-- Input Validity Lemmas (Parameterized)
--
-- These lemmas prove that when initWithInputStateful allocates a
-- compound value, the memory satisfies the stateful validity predicate.
-- PROVEN from StatefulEncoding theorems - no postulates!
------------------------------------------------------------------------

-- | For pair inputs, the initial memory satisfies PairAtS
initWithInputStateful-pair-valid : ∀ {A B} (sp : StackPointer) (hp : HeapPointer) (a : ⟦ A ⟧) (b : ⟦ B ⟧) →
  let init-heap = alloc-state emptyMemory (hp-addr hp)
      (addr-a , st₁) = encode-s {A} a init-heap
      (addr-b , st₂) = encode-s {B} b st₁
      result = initWithInputStateful {A * B} sp hp (a , b)
      m = memory (state result)
      addr-pair = input-addr result
  in PairAtS addr-a addr-b addr-pair m
initWithInputStateful-pair-valid {A} {B} sp hp a b = pair-at-s fst-valid snd-valid
  where
    init-heap : AllocState
    init-heap = alloc-state emptyMemory (hp-addr hp)

    -- PROVEN from StatefulEncoding theorems
    fst-valid = encode-pair-fst-thm {A} {B} a b init-heap
    snd-valid = encode-pair-snd-thm {A} {B} a b init-heap

-- | For left sum inputs, the initial memory satisfies InlAtS
initWithInputStateful-inl-valid : ∀ {A B} (sp : StackPointer) (hp : HeapPointer) (a : ⟦ A ⟧) →
  let init-heap = alloc-state emptyMemory (hp-addr hp)
      (addr-a , st₁) = encode-s {A} a init-heap
      result = initWithInputStateful {A + B} sp hp (inj₁ a)
      m = memory (state result)
      addr-sum = input-addr result
  in InlAtS addr-a addr-sum m
initWithInputStateful-inl-valid {A} {B} sp hp a = inl-at-s tag-valid val-valid
  where
    init-heap : AllocState
    init-heap = alloc-state emptyMemory (hp-addr hp)

    -- PROVEN from StatefulEncoding theorems
    tag-valid = encode-inl-tag-thm {A} {B} a init-heap
    val-valid = encode-inl-val-thm {A} {B} a init-heap

-- | For right sum inputs, the initial memory satisfies InrAtS
initWithInputStateful-inr-valid : ∀ {A B} (sp : StackPointer) (hp : HeapPointer) (b : ⟦ B ⟧) →
  let init-heap = alloc-state emptyMemory (hp-addr hp)
      (addr-b , st₁) = encode-s {B} b init-heap
      result = initWithInputStateful {A + B} sp hp (inj₂ b)
      m = memory (state result)
      addr-sum = input-addr result
  in InrAtS addr-b addr-sum m
initWithInputStateful-inr-valid {A} {B} sp hp b = inr-at-s tag-valid val-valid
  where
    init-heap : AllocState
    init-heap = alloc-state emptyMemory (hp-addr hp)

    -- PROVEN from StatefulEncoding theorems
    tag-valid = encode-inr-tag-thm {A} {B} b init-heap
    val-valid = encode-inr-val-thm {A} {B} b init-heap
