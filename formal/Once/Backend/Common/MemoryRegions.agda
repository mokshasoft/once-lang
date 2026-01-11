------------------------------------------------------------------------
-- Once.Backend.Common.MemoryRegions
--
-- Abstract memory regions model for compiler correctness proofs.
--
-- KEY INSIGHT (from D041):
-- Instead of using concrete addresses and bounds like `rsp > 16`,
-- we model memory as three disjoint regions: Stack, Heap, Code.
-- This single abstraction replaces multiple specific postulates
-- (heap-stack-disjoint, code-stack-disjoint, etc.).
--
-- PROPERTIES:
-- 1. Regions are disjoint (single postulate)
-- 2. Stack has tight allocation (delta = size, no waste)
-- 3. Stack has LIFO structure (dealloc inverse of alloc)
-- 4. Each address belongs to exactly one region
--
-- USAGE:
-- - Stack addresses come from stack operations (push, alloc frame)
-- - Heap addresses come from encode (values allocated on heap)
-- - Code addresses are program counter values (< length prog)
-- - Proving disjointness: show addresses are in different regions
------------------------------------------------------------------------

module Once.Backend.Common.MemoryRegions where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _*_; _<_; _≤_; _>_; _≥_)
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)

-- Import Memory type from Common.Memory
open import Once.Backend.Common.Memory using (Memory; Word; readMem; writeMem)

------------------------------------------------------------------------
-- Memory Regions
------------------------------------------------------------------------

-- | The three memory regions
-- Stack: grows via push/alloc, used for local variables and return addresses
-- Heap: grows via allocation, used for data structures (pairs, closures)
-- Code: static, contains program instructions
data Region : Set where
  stack : Region
  heap  : Region
  code  : Region

-- | Address type (abstract - no concrete values exposed)
Addr : Set
Addr = ℕ

-- | Each address belongs to a region
-- This is the fundamental abstraction - we track region membership
-- rather than concrete address values
postulate
  region-of : Addr → Region

------------------------------------------------------------------------
-- Region Disjointness (THE KEY POSTULATE)
------------------------------------------------------------------------

-- | Addresses in different regions are distinct
-- This single postulate replaces:
--   - heap-stack-disjoint
--   - code-stack-disjoint
--   - heap-code-disjoint
--
-- JUSTIFICATION:
-- The runtime initializes memory with non-overlapping regions.
-- This is a fundamental invariant maintained by the memory allocator
-- and program loader.
postulate
  regions-disjoint : ∀ {r₁ r₂} → r₁ ≢ r₂ →
    ∀ a₁ a₂ → region-of a₁ ≡ r₁ → region-of a₂ ≡ r₂ → a₁ ≢ a₂

-- | Convenience: stack ≢ heap
stack≢heap : stack ≢ heap
stack≢heap ()

-- | Convenience: stack ≢ code
stack≢code : stack ≢ code
stack≢code ()

-- | Convenience: heap ≢ code
heap≢code : heap ≢ code
heap≢code ()

-- | Derived: stack and heap addresses are disjoint
stack-heap-disjoint : ∀ a₁ a₂ →
  region-of a₁ ≡ stack → region-of a₂ ≡ heap → a₁ ≢ a₂
stack-heap-disjoint = regions-disjoint stack≢heap

-- | Derived: stack and code addresses are disjoint
stack-code-disjoint : ∀ a₁ a₂ →
  region-of a₁ ≡ stack → region-of a₂ ≡ code → a₁ ≢ a₂
stack-code-disjoint = regions-disjoint stack≢code

-- | Derived: heap and code addresses are disjoint
heap-code-disjoint : ∀ a₁ a₂ →
  region-of a₁ ≡ heap → region-of a₂ ≡ code → a₁ ≢ a₂
heap-code-disjoint = regions-disjoint heap≢code

------------------------------------------------------------------------
-- Special Address Properties
------------------------------------------------------------------------

-- | Address 0 is not in the stack region (null page protection)
-- The null page is never mapped to any allocatable region.
-- This is a fundamental memory layout invariant.
postulate
  zero-not-in-stack : region-of 0 ≢ stack

-- | Stack region is contiguous downward from any stack address.
-- Subtracting from a stack address stays in the stack region
-- (as long as we don't underflow).
-- This is a fundamental memory layout invariant: the runtime
-- initializes the stack as a contiguous region from stackBase downward.
postulate
  stack-sub-preserves-region : ∀ (a k : ℕ) →
    region-of a ≡ stack →
    k ≤ a →
    region-of (a ∸ k) ≡ stack

-- | Derived: stack addresses are never 0
stack-addr-nonzero : ∀ a → region-of a ≡ stack → a ≢ 0
stack-addr-nonzero a a-in-stack a≡0 =
  zero-not-in-stack (subst (λ x → region-of x ≡ stack) a≡0 a-in-stack)

------------------------------------------------------------------------
-- Abstract Stack Pointer
------------------------------------------------------------------------

-- | Abstract stack pointer type
-- We don't expose concrete values - only operations and properties
record StackPointer : Set where
  field
    -- The underlying address (abstract)
    addr : Addr
    -- Stack pointers point to stack region
    in-stack : region-of addr ≡ stack

open StackPointer public

-- | Stack capacity: how many more slots can be allocated
-- This replaces concrete bounds like `rsp > 16`
record HasCapacity (sp : StackPointer) (n : ℕ) : Set where
  field
    -- Can allocate n slots without underflow
    capacity-proof : ∀ k → k ≤ n → ∃[ sp' ] (addr sp' ≡ addr sp ∸ (k * 8))

open HasCapacity public

------------------------------------------------------------------------
-- Stack Operations with Tight Allocation
------------------------------------------------------------------------

-- | Allocate n bytes on stack (returns new SP and slot addresses)
-- TIGHT ALLOCATION: The new SP is exactly n bytes below old SP
postulate
  stack-alloc : (sp : StackPointer) (n : ℕ) → HasCapacity sp n →
    ∃[ sp' ] (addr sp' ≡ addr sp ∸ (n * 8)
            × region-of (addr sp') ≡ stack)

-- | Deallocate n bytes from stack
-- LIFO PROPERTY: dealloc (alloc sp n) n ≡ sp
postulate
  stack-dealloc : (sp : StackPointer) (n : ℕ) →
    ∃[ sp' ] (addr sp' ≡ addr sp + (n * 8)
            × region-of (addr sp') ≡ stack)

-- | LIFO inverse property
-- If we allocate then deallocate the same amount, we get back to start
postulate
  alloc-dealloc-inverse : (sp : StackPointer) (n : ℕ) (cap : HasCapacity sp n) →
    let (sp' , _) = stack-alloc sp n cap
        (sp'' , _) = stack-dealloc sp' n
    in addr sp'' ≡ addr sp

------------------------------------------------------------------------
-- Stack Slot Addressing
------------------------------------------------------------------------

-- | Address of a slot at offset k from stack pointer
-- slot-addr sp 0 = address at sp (top of stack)
-- slot-addr sp 1 = address at sp + 8 (next slot)
postulate
  slot-addr : StackPointer → ℕ → Addr

  -- Slot addresses are in stack region
  slot-in-stack : ∀ sp k → region-of (slot-addr sp k) ≡ stack

  -- Different SPs give different slots (freshness)
  sp-distinct : ∀ sp₁ sp₂ k → addr sp₁ ≢ addr sp₂ → slot-addr sp₁ k ≢ slot-addr sp₂ k

  -- Different offsets give different slots
  offset-distinct : ∀ sp k₁ k₂ → k₁ ≢ k₂ → slot-addr sp k₁ ≢ slot-addr sp k₂

  -- Slot addresses are at or above the base address
  -- slot-addr sp k = addr sp + k * 8 ≥ addr sp
  -- D041: This is the key property for proving caller frame preservation
  slot-addr-≥-base : ∀ sp k → slot-addr sp k ≥ addr sp

  -- D041: Caller slots are above thunk's frame pointer
  -- When caller-sp.addr = rsp + 8 (call convention) and thunk-rbp = rsp - 16,
  -- all caller slots are above thunk-rbp.
  -- Arithmetic: slot-addr sp k = (rsp + 8) + k*8 ≥ rsp + 8 > rsp - 16 = thunk-rbp
  slot-addr-above-thunk-rbp : ∀ sp k rsp thunk-rbp →
    addr sp ≡ rsp + 8 →
    thunk-rbp ≡ rsp ∸ 16 →
    rsp > 16 →
    slot-addr sp k > thunk-rbp

------------------------------------------------------------------------
-- Heap Region Properties
------------------------------------------------------------------------

-- | Heap addresses come from encoding values
-- This connects to the existing encode function
postulate
  encode-in-heap : ∀ {A : Set} (encode : A → Addr) (x : A) →
    region-of (encode x) ≡ heap

  -- Heap addresses with offsets are still in heap
  heap-offset : ∀ a n → region-of a ≡ heap → region-of (a + n) ≡ heap

------------------------------------------------------------------------
-- Code Region Properties
------------------------------------------------------------------------

-- | Code addresses are within program bounds
postulate
  code-addr-bound : ∀ a (prog-len : ℕ) →
    region-of a ≡ code → a < prog-len

  -- PC values are in code region
  pc-in-code : ∀ (pc : Addr) (prog-len : ℕ) → pc < prog-len →
    region-of pc ≡ code

------------------------------------------------------------------------
-- Key Theorem: Stack writes don't affect heap/code
------------------------------------------------------------------------

-- | Memory at heap addresses is preserved by stack operations
-- This is the key property for proving memory preservation
stack-preserves-heap : ∀ (stack-addr heap-addr : Addr) →
  region-of stack-addr ≡ stack →
  region-of heap-addr ≡ heap →
  stack-addr ≢ heap-addr
stack-preserves-heap = stack-heap-disjoint

-- | Memory at code addresses is preserved by stack operations
stack-preserves-code : ∀ (stack-addr code-addr : Addr) →
  region-of stack-addr ≡ stack →
  region-of code-addr ≡ code →
  stack-addr ≢ code-addr
stack-preserves-code = stack-code-disjoint

------------------------------------------------------------------------
-- Abstract Frame Operations
------------------------------------------------------------------------

-- | Read slot k of a stack frame
-- k is an abstract SLOT INDEX (0, 1, 2, ...), NOT an address!
-- - Slot 0 = top of frame (e.g., saved r15)
-- - Slot 1 = next slot (e.g., saved rbp)
-- - Slot 2+ = local variables, struct fields, etc.
--
-- Fully abstract - no implementation exposed, no arithmetic leaks!
postulate
  frameSlot : Memory → StackPointer → ℕ → Maybe Word

  -- | Write to slot k of a stack frame
  frameWriteSlot : Memory → StackPointer → ℕ → Word → Memory

  -- | Reading after writing to same slot returns written value
  frameSlot-write-same : ∀ mem sp k val →
    frameSlot (frameWriteSlot mem sp k val) sp k ≡ just val

  -- | Different frames don't interfere
  -- If two StackPointers identify different frames, writing to one
  -- doesn't affect reading from the other.
  frameSlot-distinct-frames : ∀ mem sp₁ sp₂ k₁ k₂ val →
    addr sp₁ ≢ addr sp₂ →
    frameSlot (frameWriteSlot mem sp₁ k₁ val) sp₂ k₂ ≡ frameSlot mem sp₂ k₂

  -- | Different slots in same frame don't interfere
  frameSlot-distinct-slots : ∀ mem sp k₁ k₂ val →
    k₁ ≢ k₂ →
    frameSlot (frameWriteSlot mem sp k₁ val) sp k₂ ≡ frameSlot mem sp k₂

------------------------------------------------------------------------
-- Abstract Memory Preservation Properties
------------------------------------------------------------------------
-- These state what frame operations preserve, with NO arithmetic.
-- The instantiation layer proves these using concrete reasoning.

postulate
  -- | Frame writes preserve address 0 (null page protection)
  -- Stack frames are never at address 0, so writing to any frame
  -- slot preserves memory at 0.
  frameWriteSlot-preserves-zero : ∀ mem sp k val →
    readMem (frameWriteSlot mem sp k val) 0 ≡ readMem mem 0

  -- | Frame writes preserve heap addresses
  -- Stack and heap regions are disjoint.
  frameWriteSlot-preserves-heap : ∀ mem sp k val heap-addr →
    region-of heap-addr ≡ heap →
    readMem (frameWriteSlot mem sp k val) heap-addr ≡ readMem mem heap-addr

  -- | Frame writes preserve code addresses
  -- Stack and code regions are disjoint.
  frameWriteSlot-preserves-code : ∀ mem sp k val code-addr →
    region-of code-addr ≡ code →
    readMem (frameWriteSlot mem sp k val) code-addr ≡ readMem mem code-addr

------------------------------------------------------------------------
-- Raw Stack Write Preservation (for x86 execution)
------------------------------------------------------------------------
-- These lemmas are for raw writeMem operations at stack addresses.
-- Used when x86 execution writes to stack (push, mov [rsp-k], etc.)
-- The INSTANTIATION LAYER proves these; x86 proofs just use them.
--
-- KEY: These take `region-of addr ≡ stack` as input, hiding all
-- arithmetic about "why stack addresses ≠ 0/heap/code".

postulate
  -- | Writing to a stack address preserves address 0
  -- If addr is in stack region, then addr ≠ 0 (since 0 is not in stack)
  stackAddr-write-preserves-zero : ∀ mem addr val →
    region-of addr ≡ stack →
    readMem (writeMem mem addr val) 0 ≡ readMem mem 0

  -- | Writing to a stack address preserves heap addresses
  stackAddr-write-preserves-heap : ∀ mem addr val heap-addr →
    region-of addr ≡ stack →
    region-of heap-addr ≡ heap →
    readMem (writeMem mem addr val) heap-addr ≡ readMem mem heap-addr

  -- | Writing to a stack address preserves code addresses
  stackAddr-write-preserves-code : ∀ mem addr val code-addr →
    region-of addr ≡ stack →
    region-of code-addr ≡ code →
    readMem (writeMem mem addr val) code-addr ≡ readMem mem code-addr

------------------------------------------------------------------------
-- INTERNAL: Abstraction Boundary Glue
------------------------------------------------------------------------
-- These connect abstract frameSlot to concrete readMem/writeMem.
-- ONLY import these in implementation code (e.g., MutualIR.agda).
-- Consumer code should NEVER use these directly!

module FrameSlotInternal where
  postulate
    -- | Slot 0 corresponds to reading at the SP's address
    frameSlot-0-is-top : ∀ mem sp → frameSlot mem sp 0 ≡ readMem mem (addr sp)

    -- | Writing to slot 0 corresponds to writing at the SP's address
    frameWriteSlot-0-is-writeMem : ∀ mem sp val →
      frameWriteSlot mem sp 0 val ≡ Once.Backend.Common.Memory.writeMem mem (addr sp) val

    -- | General: slot k corresponds to reading at slot-addr sp k
    -- Uses abstract slot-addr instead of arithmetic (addr sp + k * 8)
    -- This keeps the abstraction clean and architecture-independent.
    frameSlot-is-readMem : ∀ mem sp k → frameSlot mem sp k ≡ readMem mem (slot-addr sp k)
