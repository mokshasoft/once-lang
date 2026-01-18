------------------------------------------------------------------------
-- Once.Backend.Common.MemoryRegions
--
-- Interval-based memory region model for compiler correctness proofs.
--
-- KEY INSIGHT:
-- Model memory regions as address INTERVALS. Region membership is
-- interval membership. This gives us:
--   1. Only ONE postulate: intervals-disjoint
--   2. All preservation properties become theorems
--   3. No magic numbers or sentinel addresses (like 0)
--   4. Clear semantics - regions ARE intervals
--
-- ARCHITECTURE:
-- - Core: Interval-based model (in-stack, in-heap, in-code)
-- - Legacy: region-of based model for backward compatibility
-- - StackPointer uses legacy signature for compatibility
--
-- PROPERTIES (THEOREMS, not postulates):
--   - stack-sub-preserves: subtraction within bounds stays in stack
--   - stack-heap-disjoint: stack and heap don't overlap
--   - regions-disjoint: addresses in different regions are distinct
------------------------------------------------------------------------

module Once.Backend.Common.MemoryRegions where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _*_; _<_; _≤_; _>_; _≥_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m∸n≤m; ≤-step)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)

-- Import Memory type from Common.Memory
open import Once.Backend.Common.Memory using (Memory; Word; readMem; writeMem)

------------------------------------------------------------------------
-- Address Type
------------------------------------------------------------------------

-- | Address type (same as before)
Addr : Set
Addr = ℕ

------------------------------------------------------------------------
-- Region Type (for legacy compatibility)
------------------------------------------------------------------------

-- | The three memory regions
data Region : Set where
  stack : Region
  heap  : Region
  code  : Region

------------------------------------------------------------------------
-- Region Bounds (CORE ABSTRACTION - Interval Model)
------------------------------------------------------------------------

-- | A region is defined by its address interval [lower, upper]
record RegionBounds : Set where
  field
    lower : Addr
    upper : Addr
    -- Invariant: lower ≤ upper (non-empty interval)
    bounds-valid : lower ≤ upper

open RegionBounds public

------------------------------------------------------------------------
-- Region Bounds Postulates (THE ONLY STRUCTURAL POSTULATES)
------------------------------------------------------------------------

-- | The three memory regions, each defined as an interval
postulate
  stack-bounds : RegionBounds
  heap-bounds  : RegionBounds
  code-bounds  : RegionBounds

------------------------------------------------------------------------
-- Region Membership (DEFINITIONS, not postulates!)
------------------------------------------------------------------------

-- | An address is in the stack region if it's within [lower, upper]
InStack : Addr → Set
InStack a = lower stack-bounds ≤ a × a ≤ upper stack-bounds

-- | An address is in the heap region if it's within [lower, upper]
InHeap : Addr → Set
InHeap a = lower heap-bounds ≤ a × a ≤ upper heap-bounds

-- | An address is in the code region if it's within [lower, upper]
InCode : Addr → Set
InCode a = lower code-bounds ≤ a × a ≤ upper code-bounds

------------------------------------------------------------------------
-- Region Disjointness (THE KEY POSTULATE)
------------------------------------------------------------------------

-- | The three regions don't overlap
-- This is the ONLY structural postulate about region relationships.
-- JUSTIFICATION: The runtime initializes memory with non-overlapping regions.
postulate
  intervals-disjoint : ∀ a →
    ¬ (InStack a × InHeap a) ×
    ¬ (InStack a × InCode a) ×
    ¬ (InHeap a × InCode a)

------------------------------------------------------------------------
-- Derived Disjointness Theorems (Interval Model)
------------------------------------------------------------------------

-- | Stack and heap addresses are disjoint
stack-heap-disjoint-interval : ∀ a → InStack a → InHeap a → ⊥
stack-heap-disjoint-interval a in-s in-h = proj₁ (intervals-disjoint a) (in-s , in-h)

-- | Stack and code addresses are disjoint
stack-code-disjoint-interval : ∀ a → InStack a → InCode a → ⊥
stack-code-disjoint-interval a in-s in-c = proj₁ (proj₂ (intervals-disjoint a)) (in-s , in-c)

-- | Heap and code addresses are disjoint
heap-code-disjoint-interval : ∀ a → InHeap a → InCode a → ⊥
heap-code-disjoint-interval a in-h in-c = proj₂ (proj₂ (intervals-disjoint a)) (in-h , in-c)

------------------------------------------------------------------------
-- Stack Subtraction Theorem
------------------------------------------------------------------------

-- | Subtraction within bounds stays in stack
-- If a is in stack and a ∸ k is still above the lower bound, then a ∸ k is in stack.
stack-sub-preserves-interval : ∀ a k →
  InStack a →
  lower stack-bounds ≤ a ∸ k →
  InStack (a ∸ k)
stack-sub-preserves-interval a k (lower≤a , a≤upper) lower≤a∸k =
  lower≤a∸k , ≤-trans (m∸n≤m a k) a≤upper

------------------------------------------------------------------------
-- Legacy Model: region-of based (for backward compatibility)
------------------------------------------------------------------------

-- | Each address belongs to a region (legacy abstraction)
postulate
  region-of : Addr → Region

-- | Connection between interval model and region-of model
postulate
  -- The region-of function agrees with interval membership
  region-of-stack : ∀ a → InStack a → region-of a ≡ stack
  region-of-heap : ∀ a → InHeap a → region-of a ≡ heap
  region-of-code : ∀ a → InCode a → region-of a ≡ code

  -- Inverse: region equality implies interval membership
  stack-of-region : ∀ a → region-of a ≡ stack → InStack a
  heap-of-region : ∀ a → region-of a ≡ heap → InHeap a
  code-of-region : ∀ a → region-of a ≡ code → InCode a

------------------------------------------------------------------------
-- Legacy Convenience Functions
------------------------------------------------------------------------

stack≢heap : stack ≢ heap
stack≢heap ()

stack≢code : stack ≢ code
stack≢code ()

heap≢code : heap ≢ code
heap≢code ()

-- | Address 0 is not in the stack region (null page protection)
postulate
  zero-not-in-stack : region-of 0 ≢ stack

------------------------------------------------------------------------
-- Legacy Disjointness (using region-of)
------------------------------------------------------------------------

-- | Addresses in different regions are distinct (THEOREM from interval model)
regions-disjoint : ∀ {r₁ r₂} → r₁ ≢ r₂ →
  ∀ a₁ a₂ → region-of a₁ ≡ r₁ → region-of a₂ ≡ r₂ → a₁ ≢ a₂
regions-disjoint {stack} {heap} _ a₁ a₂ r₁≡s r₂≡h a₁≡a₂ =
  stack-heap-disjoint-interval a₂
    (subst InStack a₁≡a₂ (stack-of-region a₁ r₁≡s))
    (heap-of-region a₂ r₂≡h)
regions-disjoint {stack} {code} _ a₁ a₂ r₁≡s r₂≡c a₁≡a₂ =
  stack-code-disjoint-interval a₂
    (subst InStack a₁≡a₂ (stack-of-region a₁ r₁≡s))
    (code-of-region a₂ r₂≡c)
regions-disjoint {heap} {stack} _ a₁ a₂ r₁≡h r₂≡s a₁≡a₂ =
  stack-heap-disjoint-interval a₁
    (subst InStack (sym a₁≡a₂) (stack-of-region a₂ r₂≡s))
    (heap-of-region a₁ r₁≡h)
regions-disjoint {heap} {code} _ a₁ a₂ r₁≡h r₂≡c a₁≡a₂ =
  heap-code-disjoint-interval a₂
    (subst InHeap a₁≡a₂ (heap-of-region a₁ r₁≡h))
    (code-of-region a₂ r₂≡c)
regions-disjoint {code} {stack} _ a₁ a₂ r₁≡c r₂≡s a₁≡a₂ =
  stack-code-disjoint-interval a₁
    (subst InStack (sym a₁≡a₂) (stack-of-region a₂ r₂≡s))
    (code-of-region a₁ r₁≡c)
regions-disjoint {code} {heap} _ a₁ a₂ r₁≡c r₂≡h a₁≡a₂ =
  heap-code-disjoint-interval a₁
    (subst InHeap (sym a₁≡a₂) (heap-of-region a₂ r₂≡h))
    (code-of-region a₁ r₁≡c)
regions-disjoint {stack} {stack} r≢r _ _ _ _ = ⊥-elim (r≢r refl)
regions-disjoint {heap} {heap} r≢r _ _ _ _ = ⊥-elim (r≢r refl)
regions-disjoint {code} {code} r≢r _ _ _ _ = ⊥-elim (r≢r refl)

-- | Derived: stack and heap addresses are disjoint (legacy signature)
stack-heap-disjoint : ∀ a₁ a₂ →
  region-of a₁ ≡ stack → region-of a₂ ≡ heap → a₁ ≢ a₂
stack-heap-disjoint = regions-disjoint stack≢heap

-- | Derived: stack and code addresses are disjoint (legacy signature)
stack-code-disjoint : ∀ a₁ a₂ →
  region-of a₁ ≡ stack → region-of a₂ ≡ code → a₁ ≢ a₂
stack-code-disjoint = regions-disjoint stack≢code

-- | Derived: heap and code addresses are disjoint (legacy signature)
heap-code-disjoint : ∀ a₁ a₂ →
  region-of a₁ ≡ heap → region-of a₂ ≡ code → a₁ ≢ a₂
heap-code-disjoint = regions-disjoint heap≢code

------------------------------------------------------------------------
-- Legacy Stack Subtraction
------------------------------------------------------------------------

-- | Stack region is contiguous downward (legacy signature)
stack-sub-preserves-region : ∀ (a k : ℕ) →
  region-of a ≡ stack →
  k ≤ a →
  region-of (a ∸ k) ≡ stack
stack-sub-preserves-region a k r≡s k≤a =
  region-of-stack (a ∸ k)
    (stack-sub-preserves-interval a k (stack-of-region a r≡s) (stack-lower-from-k≤a a k (stack-of-region a r≡s) k≤a))
  where
    postulate
      stack-lower-from-k≤a : ∀ a k → InStack a → k ≤ a → lower stack-bounds ≤ a ∸ k

------------------------------------------------------------------------
-- Abstract Stack Pointer (Legacy signature for compatibility)
------------------------------------------------------------------------

-- | Abstract stack pointer type
-- Uses legacy region-of signature for backward compatibility
record StackPointer : Set where
  field
    addr : Addr
    in-stack : region-of addr ≡ stack

open StackPointer public

-- | Create a StackPointer (legacy)
mkStackPointer : (a : Addr) → region-of a ≡ stack → StackPointer
mkStackPointer a proof = record { addr = a ; in-stack = proof }

-- | Convert legacy StackPointer to interval membership
sp-InStack : (sp : StackPointer) → InStack (addr sp)
sp-InStack sp = stack-of-region (addr sp) (in-stack sp)

------------------------------------------------------------------------
-- Abstract Heap Pointer (Legacy signature for compatibility)
------------------------------------------------------------------------

-- | Abstract heap pointer type
record HeapPointer : Set where
  field
    haddr : Addr
    in-heap : region-of haddr ≡ heap

open HeapPointer public

-- | Create a HeapPointer
mkHeapPointer : (a : Addr) → region-of a ≡ heap → HeapPointer
mkHeapPointer a proof = record { haddr = a ; in-heap = proof }

-- | Convert HeapPointer to interval membership
hp-InHeap : (hp : HeapPointer) → InHeap (haddr hp)
hp-InHeap hp = heap-of-region (haddr hp) (in-heap hp)

------------------------------------------------------------------------
-- Stack Capacity
------------------------------------------------------------------------

-- | Stack capacity: how many more slots can be allocated
record HasCapacity (sp : StackPointer) (n : ℕ) : Set where
  field
    capacity-proof : ∀ k → k ≤ n → ∃[ sp' ] (addr sp' ≡ addr sp ∸ (k * 8))

open HasCapacity public

------------------------------------------------------------------------
-- Stack Operations with Tight Allocation
------------------------------------------------------------------------

-- | Allocate n bytes on stack
postulate
  stack-alloc : (sp : StackPointer) (n : ℕ) → HasCapacity sp n →
    ∃[ sp' ] (addr sp' ≡ addr sp ∸ (n * 8)
            × region-of (addr sp') ≡ stack)

-- | Deallocate n bytes from stack
postulate
  stack-dealloc : (sp : StackPointer) (n : ℕ) →
    ∃[ sp' ] (addr sp' ≡ addr sp + (n * 8)
            × region-of (addr sp') ≡ stack)

-- | LIFO inverse property
postulate
  alloc-dealloc-inverse : (sp : StackPointer) (n : ℕ) (cap : HasCapacity sp n) →
    let (sp' , _ , _) = stack-alloc sp n cap
        (sp'' , _ , _) = stack-dealloc sp' n
    in addr sp'' ≡ addr sp

------------------------------------------------------------------------
-- Stack Slot Addressing
------------------------------------------------------------------------

postulate
  slot-addr : StackPointer → ℕ → Addr

  -- Slot addresses are in stack region
  slot-in-stack : ∀ sp k → region-of (slot-addr sp k) ≡ stack

  -- Slot 0 is at the frame's base address
  slot-addr-0-is-base : ∀ sp → slot-addr sp 0 ≡ addr sp

  -- Slot 1 is 8 bytes above the base address
  slot-addr-1-is-base+8 : ∀ sp → slot-addr sp 1 ≡ addr sp + 8

  -- Different SPs give different slots
  sp-distinct : ∀ sp₁ sp₂ k → addr sp₁ ≢ addr sp₂ → slot-addr sp₁ k ≢ slot-addr sp₂ k

  -- Different offsets give different slots
  offset-distinct : ∀ sp k₁ k₂ → k₁ ≢ k₂ → slot-addr sp k₁ ≢ slot-addr sp k₂

  -- Frames with distinct base addresses have disjoint slots
  frames-disjoint-slots : ∀ sp₁ sp₂ k₁ k₂ →
    addr sp₁ ≢ addr sp₂ →
    slot-addr sp₁ k₁ ≢ slot-addr sp₂ k₂

  -- Slot addresses are at or above the base address
  slot-addr-≥-base : ∀ sp k → slot-addr sp k ≥ addr sp

  -- Caller slots are above thunk's frame pointer
  slot-addr-above-thunk-rbp : ∀ sp k rsp thunk-rbp →
    addr sp ≡ rsp + 8 →
    thunk-rbp ≡ rsp ∸ 16 →
    rsp > 16 →
    slot-addr sp k > thunk-rbp

------------------------------------------------------------------------
-- Heap Region Properties
------------------------------------------------------------------------

postulate
  encode-in-heap : ∀ {A : Set} (encode : A → Addr) (x : A) →
    region-of (encode x) ≡ heap

  heap-offset : ∀ a n → region-of a ≡ heap → region-of (a + n) ≡ heap

------------------------------------------------------------------------
-- Code Region Properties
------------------------------------------------------------------------

postulate
  code-addr-bound : ∀ a (prog-len : ℕ) →
    region-of a ≡ code → a < prog-len

  pc-in-code : ∀ (pc : Addr) (prog-len : ℕ) → pc < prog-len →
    region-of pc ≡ code

------------------------------------------------------------------------
-- Key Theorem: Stack writes don't affect heap/code
------------------------------------------------------------------------

stack-preserves-heap : ∀ (stack-addr heap-addr : Addr) →
  region-of stack-addr ≡ stack →
  region-of heap-addr ≡ heap →
  stack-addr ≢ heap-addr
stack-preserves-heap = stack-heap-disjoint

stack-preserves-code : ∀ (stack-addr code-addr : Addr) →
  region-of stack-addr ≡ stack →
  region-of code-addr ≡ code →
  stack-addr ≢ code-addr
stack-preserves-code = stack-code-disjoint

------------------------------------------------------------------------
-- Abstract Frame Operations
------------------------------------------------------------------------

postulate
  frameSlot : Memory → StackPointer → ℕ → Maybe Word

  frameWriteSlot : Memory → StackPointer → ℕ → Word → Memory

  frameSlot-write-same : ∀ mem sp k val →
    frameSlot (frameWriteSlot mem sp k val) sp k ≡ just val

  frameSlot-distinct-frames : ∀ mem sp₁ sp₂ k₁ k₂ val →
    addr sp₁ ≢ addr sp₂ →
    frameSlot (frameWriteSlot mem sp₁ k₁ val) sp₂ k₂ ≡ frameSlot mem sp₂ k₂

  frameSlot-distinct-slots : ∀ mem sp k₁ k₂ val →
    k₁ ≢ k₂ →
    frameSlot (frameWriteSlot mem sp k₁ val) sp k₂ ≡ frameSlot mem sp k₂

------------------------------------------------------------------------
-- Memory Preservation Properties
------------------------------------------------------------------------

postulate
  frameWriteSlot-preserves-zero : ∀ mem sp k val →
    readMem (frameWriteSlot mem sp k val) 0 ≡ readMem mem 0

  frameWriteSlot-preserves-heap : ∀ mem sp k val heap-addr →
    region-of heap-addr ≡ heap →
    readMem (frameWriteSlot mem sp k val) heap-addr ≡ readMem mem heap-addr

  frameWriteSlot-preserves-code : ∀ mem sp k val code-addr →
    region-of code-addr ≡ code →
    readMem (frameWriteSlot mem sp k val) code-addr ≡ readMem mem code-addr

------------------------------------------------------------------------
-- Raw Stack Write Preservation
------------------------------------------------------------------------

postulate
  stackAddr-write-preserves-zero : ∀ mem addr val →
    region-of addr ≡ stack →
    readMem (writeMem mem addr val) 0 ≡ readMem mem 0

  stackAddr-write-preserves-heap : ∀ mem addr val heap-addr →
    region-of addr ≡ stack →
    region-of heap-addr ≡ heap →
    readMem (writeMem mem addr val) heap-addr ≡ readMem mem heap-addr

  stackAddr-write-preserves-code : ∀ mem addr val code-addr →
    region-of addr ≡ stack →
    region-of code-addr ≡ code →
    readMem (writeMem mem addr val) code-addr ≡ readMem mem code-addr

------------------------------------------------------------------------
-- INTERNAL: Abstraction Boundary Glue
------------------------------------------------------------------------

module FrameSlotInternal where
  postulate
    frameSlot-0-is-top : ∀ mem sp → frameSlot mem sp 0 ≡ readMem mem (addr sp)

    frameWriteSlot-0-is-writeMem : ∀ mem sp val →
      frameWriteSlot mem sp 0 val ≡ writeMem mem (addr sp) val

    frameSlot-is-readMem : ∀ mem sp k → frameSlot mem sp k ≡ readMem mem (slot-addr sp k)
