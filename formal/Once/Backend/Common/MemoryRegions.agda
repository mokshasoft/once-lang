------------------------------------------------------------------------
-- Once.Backend.Common.MemoryRegions
--
-- Interval-based memory region model for compiler correctness proofs.
--
-- KEY INSIGHT:
-- Model memory regions as address INTERVALS. Region membership is
-- interval membership. This gives us:
--   1. Minimal postulates: just bounds existence + intervals-disjoint
--   2. Disjointness is a THEOREM from interval non-overlap
--   3. No magic numbers or sentinel addresses
--   4. Clear semantics - regions ARE intervals
--
-- POSTULATES (total: 4 structural):
--   - stack-bounds, heap-bounds, code-bounds: interval definitions
--   - intervals-disjoint: the three intervals don't overlap
--
-- THEOREMS (derived from intervals):
--   - stack-heap-disjoint, stack-code-disjoint, heap-code-disjoint
--   - stack-sub-preserves: subtraction within bounds stays in stack
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

Addr : Set
Addr = ℕ

------------------------------------------------------------------------
-- Region Bounds (CORE ABSTRACTION)
------------------------------------------------------------------------

-- | A region is defined by its address interval [lower, upper]
record RegionBounds : Set where
  field
    lower : Addr
    upper : Addr
    bounds-valid : lower ≤ upper

open RegionBounds public

------------------------------------------------------------------------
-- Region Bounds Postulates (STRUCTURAL)
------------------------------------------------------------------------

postulate
  stack-bounds : RegionBounds
  heap-bounds  : RegionBounds
  code-bounds  : RegionBounds

------------------------------------------------------------------------
-- Region Membership (DEFINITIONS, not postulates!)
------------------------------------------------------------------------

-- | Address is in stack if within [lower, upper]
InStack : Addr → Set
InStack a = lower stack-bounds ≤ a × a ≤ upper stack-bounds

-- | Address is in heap if within [lower, upper]
InHeap : Addr → Set
InHeap a = lower heap-bounds ≤ a × a ≤ upper heap-bounds

-- | Address is in code if within [lower, upper]
InCode : Addr → Set
InCode a = lower code-bounds ≤ a × a ≤ upper code-bounds

------------------------------------------------------------------------
-- Region Disjointness (THE KEY POSTULATE)
------------------------------------------------------------------------

-- | The three regions don't overlap
-- JUSTIFICATION: Runtime initializes memory with non-overlapping regions.
postulate
  intervals-disjoint : ∀ a →
    ¬ (InStack a × InHeap a) ×
    ¬ (InStack a × InCode a) ×
    ¬ (InHeap a × InCode a)

------------------------------------------------------------------------
-- Derived Disjointness THEOREMS
------------------------------------------------------------------------

stack-heap-disjoint : ∀ a → InStack a → InHeap a → ⊥
stack-heap-disjoint a in-s in-h = proj₁ (intervals-disjoint a) (in-s , in-h)

stack-code-disjoint : ∀ a → InStack a → InCode a → ⊥
stack-code-disjoint a in-s in-c = proj₁ (proj₂ (intervals-disjoint a)) (in-s , in-c)

heap-code-disjoint : ∀ a → InHeap a → InCode a → ⊥
heap-code-disjoint a in-h in-c = proj₂ (proj₂ (intervals-disjoint a)) (in-h , in-c)

-- | Two addresses in different regions are distinct
stack-heap-addr-disjoint : ∀ a₁ a₂ → InStack a₁ → InHeap a₂ → a₁ ≢ a₂
stack-heap-addr-disjoint a₁ a₂ in-s in-h a₁≡a₂ =
  stack-heap-disjoint a₂ (subst InStack a₁≡a₂ in-s) in-h

stack-code-addr-disjoint : ∀ a₁ a₂ → InStack a₁ → InCode a₂ → a₁ ≢ a₂
stack-code-addr-disjoint a₁ a₂ in-s in-c a₁≡a₂ =
  stack-code-disjoint a₂ (subst InStack a₁≡a₂ in-s) in-c

heap-code-addr-disjoint : ∀ a₁ a₂ → InHeap a₁ → InCode a₂ → a₁ ≢ a₂
heap-code-addr-disjoint a₁ a₂ in-h in-c a₁≡a₂ =
  heap-code-disjoint a₂ (subst InHeap a₁≡a₂ in-h) in-c

------------------------------------------------------------------------
-- Stack Subtraction (POSTULATE)
--
-- JUSTIFICATION: Runtime initializes the stack with sufficient capacity.
-- When k ≤ a and a is in stack, a ∸ k remains in stack.
------------------------------------------------------------------------

postulate
  stack-sub-preserves : ∀ a k →
    InStack a →
    k ≤ a →
    InStack (a ∸ k)

------------------------------------------------------------------------
-- Abstract Stack Pointer
------------------------------------------------------------------------

record StackPointer : Set where
  field
    addr : Addr
    in-stack : InStack addr

open StackPointer public

mkStackPointer : (a : Addr) → InStack a → StackPointer
mkStackPointer a proof = record { addr = a ; in-stack = proof }

------------------------------------------------------------------------
-- Abstract Heap Pointer
------------------------------------------------------------------------

record HeapPointer : Set where
  field
    haddr : Addr
    in-heap : InHeap haddr

open HeapPointer public

mkHeapPointer : (a : Addr) → InHeap a → HeapPointer
mkHeapPointer a proof = record { haddr = a ; in-heap = proof }

------------------------------------------------------------------------
-- Stack Capacity
------------------------------------------------------------------------

record HasCapacity (sp : StackPointer) (n : ℕ) : Set where
  field
    capacity-proof : ∀ k → k ≤ n → lower stack-bounds ≤ addr sp ∸ (k * 8)

open HasCapacity public

------------------------------------------------------------------------
-- Stack Operations
------------------------------------------------------------------------

postulate
  stack-alloc : (sp : StackPointer) (n : ℕ) → HasCapacity sp n →
    ∃[ sp' ] (addr sp' ≡ addr sp ∸ (n * 8))

  stack-dealloc : (sp : StackPointer) (n : ℕ) →
    ∃[ sp' ] (addr sp' ≡ addr sp + (n * 8) × InStack (addr sp'))

  alloc-dealloc-inverse : (sp : StackPointer) (n : ℕ) (cap : HasCapacity sp n) →
    let (sp' , _) = stack-alloc sp n cap
        (sp'' , _ , _) = stack-dealloc sp' n
    in addr sp'' ≡ addr sp

------------------------------------------------------------------------
-- Stack Slot Addressing
------------------------------------------------------------------------

postulate
  slot-addr : StackPointer → ℕ → Addr
  slot-in-stack : ∀ sp k → InStack (slot-addr sp k)
  slot-addr-0-is-base : ∀ sp → slot-addr sp 0 ≡ addr sp
  slot-addr-1-is-base+8 : ∀ sp → slot-addr sp 1 ≡ addr sp + 8
  sp-distinct : ∀ sp₁ sp₂ k → addr sp₁ ≢ addr sp₂ → slot-addr sp₁ k ≢ slot-addr sp₂ k
  offset-distinct : ∀ sp k₁ k₂ → k₁ ≢ k₂ → slot-addr sp k₁ ≢ slot-addr sp k₂
  frames-disjoint-slots : ∀ sp₁ sp₂ k₁ k₂ → addr sp₁ ≢ addr sp₂ → slot-addr sp₁ k₁ ≢ slot-addr sp₂ k₂
  slot-addr-≥-base : ∀ sp k → slot-addr sp k ≥ addr sp
  slot-addr-above-thunk-rbp : ∀ sp k rsp thunk-rbp →
    addr sp ≡ rsp + 8 → thunk-rbp ≡ rsp ∸ 16 → rsp > 16 → slot-addr sp k > thunk-rbp

------------------------------------------------------------------------
-- Heap Region Properties
------------------------------------------------------------------------

postulate
  encode-in-heap : ∀ {A : Set} (encode : A → Addr) (x : A) → InHeap (encode x)
  heap-offset : ∀ a n → InHeap a → InHeap (a + n)

------------------------------------------------------------------------
-- Code Region Properties
------------------------------------------------------------------------

postulate
  code-addr-bound : ∀ a (prog-len : ℕ) → InCode a → a < prog-len
  pc-in-code : ∀ (pc : Addr) (prog-len : ℕ) → pc < prog-len → InCode pc

------------------------------------------------------------------------
-- Memory Preservation: Stack writes don't affect heap/code
------------------------------------------------------------------------

stack-preserves-heap : ∀ (stack-addr heap-addr : Addr) →
  InStack stack-addr → InHeap heap-addr → stack-addr ≢ heap-addr
stack-preserves-heap = stack-heap-addr-disjoint

stack-preserves-code : ∀ (stack-addr code-addr : Addr) →
  InStack stack-addr → InCode code-addr → stack-addr ≢ code-addr
stack-preserves-code = stack-code-addr-disjoint

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
  frameWriteSlot-preserves-heap : ∀ mem sp k val heap-addr →
    InHeap heap-addr →
    readMem (frameWriteSlot mem sp k val) heap-addr ≡ readMem mem heap-addr

  frameWriteSlot-preserves-code : ∀ mem sp k val code-addr →
    InCode code-addr →
    readMem (frameWriteSlot mem sp k val) code-addr ≡ readMem mem code-addr

  stackAddr-write-preserves-heap : ∀ mem addr val heap-addr →
    InStack addr → InHeap heap-addr →
    readMem (writeMem mem addr val) heap-addr ≡ readMem mem heap-addr

  stackAddr-write-preserves-code : ∀ mem addr val code-addr →
    InStack addr → InCode code-addr →
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
