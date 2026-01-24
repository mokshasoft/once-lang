------------------------------------------------------------------------
-- Once.Backend.Common.AllocatorSemantics
--
-- Block-based heap allocator semantics (2 axioms).
--
-- This module is PARAMETERIZED over MemoryLayout, which provides
-- the heap region definition and slot-size.
--
-- Architecture:
--   - Allocated addr n : abstract witness that n slots were allocated at addr
--   - P1 (block-in-heap): all slots of an allocated block are InHeap
--   - P2 (blocks-disjoint): distinct allocations have non-overlapping slots
--
-- Properties:
--   - Handles arbitrary block sizes (pairs=2, closures=2, custom=n)
--   - Architecture-independent (parameterized by slot-size from layout)
--   - Orthogonal to memory management (GC, refcounting, linear ownership)
--   - No value injectivity, no value recovery from addresses
--
-- See: docs/formal/guides/structural-threading-architecture.md
------------------------------------------------------------------------

open import Once.Backend.Common.MemoryLayoutSemantics
  using (MemoryLayout; Addr)

module Once.Backend.Common.AllocatorSemantics (layout : MemoryLayout) where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (+-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst; cong)

-- Import InHeap from Regions
open import Once.Backend.Common.Regions layout using (InHeap)

-- Open layout to get slot-size
open MemoryLayout layout

------------------------------------------------------------------------
-- Allocation Witness
--
-- Records that a block of n slots was allocated at addr.
-- This is an ABSTRACT type — witnesses can only be created through
-- alloc-encode (postulated below).
--
-- Generators create these at allocation time:
--   pair    → Allocated pair-addr 2
--   closure → Allocated closure-addr 2
--   inl/inr → Allocated sum-addr 2
--   custom  → Allocated dt-addr n (for n-field datatypes)
------------------------------------------------------------------------

postulate
  Allocated : Addr → ℕ → Set

------------------------------------------------------------------------
-- Allocator Axioms (2 postulates + 1 creation interface)
--
-- These represent trusted runtime guarantees about the allocator.
-- They cannot be proven from the abstract memory model.
------------------------------------------------------------------------

postulate
  -- | Creation interface: encode allocates blocks in the heap.
  --
  -- The encode function maps semantic values to heap addresses.
  -- When we encode a value and declare its block size, we get an
  -- Allocated witness that the postulates can use.
  --
  -- TRUST: The declared block size n must match the actual allocation
  -- size for the value's type (pairs=2, closures=2, etc.).
  alloc-encode : ∀ {A : Set} (encode : A → Addr) (x : A) (n : ℕ) →
    Allocated (encode x) n

  -- | P1: All slots of an allocated block are in the heap region.
  --
  -- Given an allocation of n slots at addr, every slot address
  -- (addr + i * slot-size) for i < n is within the heap region.
  --
  -- This replaces both encode-in-heap and heap-offset from the old model:
  --   - encode-in-heap: block-in-heap with i=0 (base address)
  --   - heap-offset:    block-in-heap with i=1 (next slot, bounded)
  block-in-heap : ∀ {addr n} →
    Allocated addr n →
    ∀ (i : ℕ) → i < n → InHeap (addr + i * slot-size)

  -- | P2: Distinct allocations have fully disjoint slot ranges.
  --
  -- If two blocks are allocated at different base addresses,
  -- no slot of one block overlaps any slot of the other.
  --
  -- This is the separation guarantee: allocated blocks are independent
  -- memory regions. Orthogonal to GC/refcounting/linearity — those
  -- only affect WHEN blocks stop being live, not their addresses.
  blocks-disjoint : ∀ {addr₁ n₁ addr₂ n₂} →
    Allocated addr₁ n₁ →
    Allocated addr₂ n₂ →
    addr₁ ≢ addr₂ →
    ∀ (i j : ℕ) → i < n₁ → j < n₂ →
    (addr₁ + i * slot-size) ≢ (addr₂ + j * slot-size)

------------------------------------------------------------------------
-- Transitional Postulate (bounded field access)
--
-- This will be eliminated when Allocated witnesses are threaded
-- through AtS records. For now, it provides a bounded version of
-- the old arbitrary-offset heap-offset postulate.
--
-- IMPROVEMENT over old model: only allows slot-size offset (not arbitrary n).
-- All existing usages already pass slot-size, so this is the minimal bound.
------------------------------------------------------------------------

postulate
  -- | Next slot of a heap address is also InHeap.
  -- Transitional: will be replaced by threading Allocated witnesses.
  heap-offset : ∀ a → InHeap a → InHeap (a + slot-size)

------------------------------------------------------------------------
-- Derived Helpers (backward-compatible with old API)
--
-- These are PROVEN from the postulates above, not additional axioms.
------------------------------------------------------------------------

-- | Base address of an allocated block is InHeap.
-- Replaces encode-in-heap for callers with an Allocated witness.
alloc-base-in-heap : ∀ {addr n} → Allocated addr n → 0 < n → InHeap addr
alloc-base-in-heap {addr} alloc lt =
  subst InHeap (+-identityʳ addr) (block-in-heap alloc 0 lt)

-- | Encoding function produces heap addresses.
-- Backward-compatible with old encode-in-heap signature.
-- Derived from alloc-encode + block-in-heap.
encode-in-heap : ∀ {A : Set} (encode : A → Addr) (x : A) → InHeap (encode x)
encode-in-heap enc x = alloc-base-in-heap (alloc-encode enc x 1) (s≤s z≤n)

-- | Second slot of a 2-slot block is InHeap.
-- Common case for pairs, closures, sums (all 2-slot blocks).
heap-next-slot : ∀ {addr} → Allocated addr 2 → InHeap (addr + slot-size)
heap-next-slot {addr} alloc =
  subst InHeap (cong (addr +_) (*-identityˡ slot-size))
    (block-in-heap alloc 1 (s≤s (s≤s z≤n)))
  where
    open import Data.Nat.Properties using (*-identityˡ)
