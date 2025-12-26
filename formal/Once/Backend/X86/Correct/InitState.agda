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
open import Once.StatefulEncoding using (encode-s)
open import Once.Memory
  using (AllocState; alloc-state; heap-ptr; init-alloc-state)
  renaming (mem to alloc-mem)
import Once.Memory as Mem

-- Keep old encode for backwards compatibility during transition
open import Once.Postulates
  using (encode)

open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
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
