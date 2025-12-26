------------------------------------------------------------------------
-- Once.Backend.X86.Correct.InitState
--
-- Initial state setup for x86-64 execution.
-- These are independent (Level 0) - no dependencies on other Correct/* modules.
--
-- KEY CHANGE: Uses stateful encoding to properly allocate input values
-- in memory. This eliminates the "magic heap" approach where postulates
-- claimed validity for emptyMemory.
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

-- Import validity predicates
open import Once.Backend.X86.Correct.MemoryValid
  using (PairAt; pair-at; InlAt; inl-at; InrAt; inr-at)

-- Keep old encode for backwards compatibility during transition
open import Once.Postulates
  using (encode)

open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

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
--   - rsp = rbp = large value (stack pointer = frame pointer at entry)
--   - pc = 0
--   - halted = false
--   - Memory contains encoded representation of x (postulated)
initWithInput : ∀ {A} → ⟦ A ⟧ → State
initWithInput {A} x = mkstate
  (writeReg (writeReg (writeReg emptyRegFile rdi (encode x)) rsp stackBase) rbp stackBase)
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

-- | Stack base value exported for other modules
stackBase : Word
stackBase = 0x7FFF0000

------------------------------------------------------------------------
-- NEW: Stateful Initial State Setup
--
-- This version properly allocates input values in memory, eliminating
-- the need for encoding postulates.
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
-- Unlike initWithInput, this version:
--   1. Actually allocates x in memory using encode-s
--   2. Uses that memory in the State
--   3. Returns the allocation address
--
-- The key property: memory ACTUALLY contains the encoded value,
-- so encoding theorems can be applied without postulates.
initWithInputStateful : ∀ {A} → ⟦ A ⟧ → InitResult A
initWithInputStateful {A} x = record
  { state = mkstate
      (writeReg (writeReg (writeReg emptyRegFile rdi x-addr) rsp stackBase) rbp stackBase)
      (alloc-mem x-alloc)  -- Use the memory with allocated x!
      initFlags
      0
      false
  ; alloc = x-alloc
  ; input-addr = x-addr
  ; rdi-eq = refl
  }
  where
    -- Start with heap at a good location (after stack area)
    init-heap : AllocState
    init-heap = alloc-state emptyMemory 0x80000000  -- Heap starts after 2GB

    -- Encode x, allocating it in memory
    encode-result : Word × AllocState
    encode-result = encode-s {A} x init-heap

    x-addr : Word
    x-addr = proj₁ encode-result

    x-alloc : AllocState
    x-alloc = proj₂ encode-result

-- | The stateful input is placed in rdi
initWithInputStateful-rdi : ∀ {A} (x : ⟦ A ⟧) →
  readReg (regs (state (initWithInputStateful x))) rdi ≡ input-addr (initWithInputStateful x)
initWithInputStateful-rdi x = rdi-eq (initWithInputStateful x)

-- | Stateful initial state is not halted
initWithInputStateful-halted : ∀ {A} (x : ⟦ A ⟧) →
  halted (state (initWithInputStateful x)) ≡ false
initWithInputStateful-halted x = refl

-- | Stateful initial state has pc = 0
initWithInputStateful-pc : ∀ {A} (x : ⟦ A ⟧) →
  pc (state (initWithInputStateful x)) ≡ 0
initWithInputStateful-pc x = refl

------------------------------------------------------------------------
-- Stateful Validity Predicates
--
-- These are like PairAt/InlAt/InrAt but use explicit addresses instead
-- of the abstract `encode`. This allows proving validity from
-- stateful encoding theorems without circular reference to postulates.
------------------------------------------------------------------------

open import Data.Maybe using (just)
open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)

-- | Pair validity with explicit component addresses
-- Memory at addr-pair contains [addr-a, addr-b]
record PairAtS (addr-a addr-b addr-pair : Word) (m : Memory) : Set where
  constructor pair-at-s
  field
    fst-valid : readMem m addr-pair ≡ just addr-a
    snd-valid : readMem m (addr-pair +ℕ 8) ≡ just addr-b

-- | Left sum validity with explicit value address
-- Memory at addr-sum contains [0, addr-val]
record InlAtS (addr-val addr-sum : Word) (m : Memory) : Set where
  constructor inl-at-s
  field
    tag-valid : readMem m addr-sum ≡ just 0
    val-valid : readMem m (addr-sum +ℕ 8) ≡ just addr-val

-- | Right sum validity with explicit value address
-- Memory at addr-sum contains [1, addr-val]
record InrAtS (addr-val addr-sum : Word) (m : Memory) : Set where
  constructor inr-at-s
  field
    tag-valid : readMem m addr-sum ≡ just 1
    val-valid : readMem m (addr-sum +ℕ 8) ≡ just addr-val

------------------------------------------------------------------------
-- Input Validity Lemmas
--
-- These lemmas prove that when initWithInputStateful allocates a
-- compound value, the memory satisfies the stateful validity predicate.
-- PROVEN from StatefulEncoding theorems - no postulates!
------------------------------------------------------------------------

-- | For pair inputs, the initial memory satisfies PairAtS
initWithInputStateful-pair-valid : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) →
  let init-heap = alloc-state emptyMemory 0x80000000
      (addr-a , st₁) = encode-s {A} a init-heap
      (addr-b , st₂) = encode-s {B} b st₁
      result = initWithInputStateful {A * B} (a , b)
      m = memory (state result)
      addr-pair = input-addr result
  in PairAtS addr-a addr-b addr-pair m
initWithInputStateful-pair-valid {A} {B} a b = pair-at-s fst-valid snd-valid
  where
    init-heap : AllocState
    init-heap = alloc-state emptyMemory 0x80000000

    -- PROVEN from StatefulEncoding theorems
    fst-valid = encode-pair-fst-thm {A} {B} a b init-heap
    snd-valid = encode-pair-snd-thm {A} {B} a b init-heap

-- | For left sum inputs, the initial memory satisfies InlAtS
initWithInputStateful-inl-valid : ∀ {A B} (a : ⟦ A ⟧) →
  let init-heap = alloc-state emptyMemory 0x80000000
      (addr-a , st₁) = encode-s {A} a init-heap
      result = initWithInputStateful {A + B} (inj₁ a)
      m = memory (state result)
      addr-sum = input-addr result
  in InlAtS addr-a addr-sum m
initWithInputStateful-inl-valid {A} {B} a = inl-at-s tag-valid val-valid
  where
    init-heap : AllocState
    init-heap = alloc-state emptyMemory 0x80000000

    -- PROVEN from StatefulEncoding theorems
    tag-valid = encode-inl-tag-thm {A} {B} a init-heap
    val-valid = encode-inl-val-thm {A} {B} a init-heap

-- | For right sum inputs, the initial memory satisfies InrAtS
initWithInputStateful-inr-valid : ∀ {A B} (b : ⟦ B ⟧) →
  let init-heap = alloc-state emptyMemory 0x80000000
      (addr-b , st₁) = encode-s {B} b init-heap
      result = initWithInputStateful {A + B} (inj₂ b)
      m = memory (state result)
      addr-sum = input-addr result
  in InrAtS addr-b addr-sum m
initWithInputStateful-inr-valid {A} {B} b = inr-at-s tag-valid val-valid
  where
    init-heap : AllocState
    init-heap = alloc-state emptyMemory 0x80000000

    -- PROVEN from StatefulEncoding theorems
    tag-valid = encode-inr-tag-thm {A} {B} b init-heap
    val-valid = encode-inr-val-thm {A} {B} b init-heap
