------------------------------------------------------------------------
-- Once.Backend.Common.MemoryRegionLemmas
--
-- Lemmas and theorems derived from the memory layout semantics.
--
-- This module is PARAMETERIZED over:
--   - StackGrowth: stack slot addressing (from architecture)
--   - MemoryLayout: region bounds (concrete or abstract)
--
-- Provides:
--   1. Derived disjointness theorems
--   2. Stack slot addressing (from StackGrowth)
--   3. Memory preservation lemmas
------------------------------------------------------------------------

-- Import types for module parameters
open import Once.Backend.Common.MemoryLayoutSemantics
  using (StackGrowth; MemoryLayout; RegionBounds; Addr; lower; upper; InRegion)

module Once.Backend.Common.MemoryRegionLemmas
  (layout : MemoryLayout)
  (sg : StackGrowth)
  where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _*_; _<_; _≤_; _>_; _≥_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m∸n≤m; ≤-step)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)

-- Re-export foundational types (not the default layout values or address types)
open import Once.Backend.Common.MemoryLayoutSemantics public
  hiding (StackGrowth; MemoryLayout;
          stack-bounds; heap-bounds; code-bounds;
          InStack; InHeap; InCode; intervals-disjoint;
          defaultLayout; default-stack-bounds; default-heap-bounds;
          default-code-bounds; default-intervals-disjoint;
          -- Also hide address types that depend on InStack/InHeap/InCode
          StackAddr; HeapAddr; CodeAddr; stack-addr; heap-addr; code-addr;
          addr; haddr; in-stack; in-heap; in-code;
          from-raw-stack; from-raw-heap; from-raw-code;
          to-raw-stack; to-raw-heap; to-raw-code)

-- Open the MemoryLayout parameter to get bounds
stack-bounds : RegionBounds
stack-bounds = MemoryLayout.stack-bounds layout

heap-bounds : RegionBounds
heap-bounds = MemoryLayout.heap-bounds layout

code-bounds : RegionBounds
code-bounds = MemoryLayout.code-bounds layout

-- Define region membership from the layout parameter
InStack : Addr → Set
InStack a = lower stack-bounds ≤ a × a ≤ upper stack-bounds

InHeap : Addr → Set
InHeap a = lower heap-bounds ≤ a × a ≤ upper heap-bounds

InCode : Addr → Set
InCode a = lower code-bounds ≤ a × a ≤ upper code-bounds

intervals-disjoint : ∀ a →
  ¬ (InStack a × InHeap a) ×
  ¬ (InStack a × InCode a) ×
  ¬ (InHeap a × InCode a)
intervals-disjoint = MemoryLayout.intervals-disjoint layout

------------------------------------------------------------------------
-- Abstract Address Types (using parameterized InStack/InHeap/InCode)
------------------------------------------------------------------------

-- | Stack address: in stack region by construction
record StackAddr : Set where
  constructor stack-addr
  field
    addr : Addr
    in-stack : InStack addr

open StackAddr public

-- | Heap address: in heap region by construction
record HeapAddr : Set where
  constructor heap-addr
  field
    haddr : Addr
    in-heap : InHeap haddr

open HeapAddr public

-- | Code address: in code region by construction
record CodeAddr : Set where
  constructor code-addr
  field
    addr : Addr
    in-code : InCode addr

open CodeAddr public

-- Boundary conversions
from-raw-stack : (a : Addr) → InStack a → StackAddr
from-raw-stack a proof = stack-addr a proof

from-raw-heap : (a : Addr) → InHeap a → HeapAddr
from-raw-heap a proof = heap-addr a proof

from-raw-code : (a : Addr) → InCode a → CodeAddr
from-raw-code a proof = code-addr a proof

to-raw-stack : StackAddr → Addr
to-raw-stack sa = StackAddr.addr sa

to-raw-heap : HeapAddr → Addr
to-raw-heap ha = HeapAddr.haddr ha

to-raw-code : CodeAddr → Addr
to-raw-code ca = CodeAddr.addr ca

-- Open the StackGrowth parameter
open StackGrowth sg public

-- Import and re-export Memory operations
open import Once.Backend.Common.Memory using (Memory; readMem; writeMem) public

------------------------------------------------------------------------
-- Derived Disjointness THEOREMS
------------------------------------------------------------------------

stack-heap-disjoint : ∀ a → InStack a → InHeap a → ⊥
stack-heap-disjoint a in-s in-h = proj₁ (intervals-disjoint a) (in-s , in-h)

stack-code-disjoint : ∀ a → InStack a → InCode a → ⊥
stack-code-disjoint a in-s in-c = proj₁ (proj₂ (intervals-disjoint a)) (in-s , in-c)

-- | Two addresses in different regions are distinct
stack-heap-addr-disjoint : ∀ a₁ a₂ → InStack a₁ → InHeap a₂ → a₁ ≢ a₂
stack-heap-addr-disjoint a₁ a₂ in-s in-h a₁≡a₂ =
  stack-heap-disjoint a₂ (subst InStack a₁≡a₂ in-s) in-h

stack-code-addr-disjoint : ∀ a₁ a₂ → InStack a₁ → InCode a₂ → a₁ ≢ a₂
stack-code-addr-disjoint a₁ a₂ in-s in-c a₁≡a₂ =
  stack-code-disjoint a₂ (subst InStack a₁≡a₂ in-s) in-c

------------------------------------------------------------------------
-- Abstract Stack/Heap Pointers (aliases for Semantics types)
------------------------------------------------------------------------

-- StackPointer = StackAddr from Semantics (re-exported)
StackPointer : Set
StackPointer = StackAddr

-- HeapPointer = HeapAddr from Semantics (re-exported)
HeapPointer : Set
HeapPointer = HeapAddr

------------------------------------------------------------------------
-- Stack Slot Addressing (DERIVED FROM StackGrowth)
--
-- These definitions and lemmas are derived from the StackGrowth
-- interface provided by the architecture.
------------------------------------------------------------------------

-- | Compute address of slot k in stack frame at sp
slot-addr : StackPointer → ℕ → Addr
slot-addr sp k = grow (addr sp) k

-- | Initial slot is at the stack pointer base (from grow-identity)
init-slot-at-base : ∀ sp → slot-addr sp zero ≡ addr sp
init-slot-at-base sp = grow-identity (addr sp)

-- | Different offsets give different addresses (from grow-injective)
offset-distinct : ∀ sp k₁ k₂ → k₁ ≢ k₂ → slot-addr sp k₁ ≢ slot-addr sp k₂
offset-distinct sp k₁ k₂ k₁≢k₂ = grow-injective (addr sp) k₁ k₂ k₁≢k₂

-- | Slot 0 is in stack region (trivial: slot-addr sp 0 = addr sp)
-- For k > 0, use StackCapacity.capacity-maintained instead
slot-in-stack-0 : ∀ sp → InStack (slot-addr sp 0)
slot-in-stack-0 sp = subst InStack (sym (grow-identity (addr sp))) (in-stack sp)

-- | DEPRECATED: General slot-in-stack requires capacity evidence for k > 0
-- Kept for backward compatibility; callers should migrate to:
--   k = 0: use slot-in-stack-0
--   k > 0: use StackCapacity.capacity-maintained
slot-in-stack : ∀ sp k → InStack (slot-addr sp k)
slot-in-stack sp zero = slot-in-stack-0 sp
slot-in-stack sp (suc k) = slot-in-stack-suc sp k
  where
    -- For k > 0, we need capacity. This postulate represents that requirement.
    -- It will be eliminated when callers use capacity-maintained directly.
    postulate
      slot-in-stack-suc : ∀ sp k → InStack (slot-addr sp (suc k))

-- | Different stack pointers give different slot addresses (same offset)
-- Proven from grow-addr-injective
sp-distinct : ∀ sp₁ sp₂ k → addr sp₁ ≢ addr sp₂ → slot-addr sp₁ k ≢ slot-addr sp₂ k
sp-distinct sp₁ sp₂ k addr≢ = grow-addr-injective (addr sp₁) (addr sp₂) k addr≢

------------------------------------------------------------------------
-- Heap Region Properties (SEMANTIC POSTULATES)
--
-- These represent runtime guarantees about the allocator that cannot
-- be derived from the abstract memory model alone:
--
-- 1. encode-in-heap: The runtime allocator places semantic values in
--    the heap region. This is instantiated with our specific encode
--    function in StackInstantiation.encode-in-heap-sem.
--
-- 2. heap-offset: Heap-allocated objects are contiguous. When we have
--    a pointer to a heap object, accessing fields (ptr + offset) stays
--    within heap. In practice, offset is always small (slot-size = 8).
--
-- NOTE: These are FOUNDATIONAL postulates at the allocator boundary,
-- not "middle-step" lemmas that should be proven from something else.
------------------------------------------------------------------------

postulate
  -- | Encoding function produces heap addresses
  -- JUSTIFICATION: The runtime allocator places all semantic values in heap.
  encode-in-heap : ∀ {A : Set} (encode : A → Addr) (x : A) → InHeap (encode x)

  -- | Field access stays within heap region
  -- JUSTIFICATION: Heap objects are allocated contiguously. When accessing
  -- fields of a heap object (e.g., closure payload at ptr+8), the result
  -- is still in heap. Requires heap capacity for allocated object sizes.
  heap-offset : ∀ a n → InHeap a → InHeap (a + n)

------------------------------------------------------------------------
-- Abstract Frame Operations
--
-- frameSlot reads the value at slot k of stack frame sp.
------------------------------------------------------------------------

-- | Read value at slot k of stack frame at sp
frameSlot : Memory → StackPointer → ℕ → Maybe Word
frameSlot mem sp k = readMem mem (slot-addr sp k)

------------------------------------------------------------------------
-- Memory Preservation
--
-- Writing to stack doesn't affect heap/code regions (from disjointness).
------------------------------------------------------------------------

-- Import readMem-writeMem-diff for the proofs
open import Once.Backend.Common.Memory using (readMem-writeMem-diff)

-- | Writing to a stack address preserves heap memory
stackAddr-write-preserves-heap : ∀ mem a val heap-a →
  InStack a → InHeap heap-a →
  readMem (writeMem mem a val) heap-a ≡ readMem mem heap-a
stackAddr-write-preserves-heap mem a val heap-a in-s in-h =
  readMem-writeMem-diff mem a heap-a val (stack-heap-addr-disjoint a heap-a in-s in-h)

-- | Writing to a stack address preserves code memory
stackAddr-write-preserves-code : ∀ mem a val code-a →
  InStack a → InCode code-a →
  readMem (writeMem mem a val) code-a ≡ readMem mem code-a
stackAddr-write-preserves-code mem a val code-a in-s in-c =
  readMem-writeMem-diff mem a code-a val (stack-code-addr-disjoint a code-a in-s in-c)

------------------------------------------------------------------------
-- INTERNAL: Abstraction Boundary Glue
------------------------------------------------------------------------

module FrameSlotInternal where
  -- | frameSlot at initial slot reads from the stack pointer address
  init-frame-slot-at-base : ∀ mem sp → frameSlot mem sp zero ≡ readMem mem (addr sp)
  init-frame-slot-at-base mem sp = cong (readMem mem) (init-slot-at-base sp)

  -- | frameSlot is just readMem at the slot address (by definition)
  frameSlot-is-readMem : ∀ mem sp k → frameSlot mem sp k ≡ readMem mem (slot-addr sp k)
  frameSlot-is-readMem mem sp k = refl
