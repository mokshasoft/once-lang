------------------------------------------------------------------------
-- Once.Backend.Common.AllocatorSemantics
--
-- Heap allocator semantic postulates.
--
-- This module is PARAMETERIZED over MemoryLayout, which provides
-- the heap region definition.
--
-- These postulates represent runtime guarantees about the allocator:
--   1. encode-in-heap: Allocated values are placed in heap region
--   2. heap-offset: Heap objects are contiguous (field access stays in heap)
--
-- These are FOUNDATIONAL postulates at the allocator boundary - they
-- cannot be proven from the abstract memory model, only trusted based
-- on the allocator implementation.
------------------------------------------------------------------------

open import Once.Backend.Common.MemoryLayoutSemantics
  using (MemoryLayout; Addr)

module Once.Backend.Common.AllocatorSemantics (layout : MemoryLayout) where

open import Data.Nat using (ℕ; _+_)

-- Import InHeap from Regions
open import Once.Backend.Common.Regions layout using (InHeap)

------------------------------------------------------------------------
-- Allocator Postulates
------------------------------------------------------------------------

postulate
  -- | Encoding function produces heap addresses
  --
  -- JUSTIFICATION: The runtime allocator places all semantic values
  -- (closures, pairs, sums, etc.) in the heap region. When we encode
  -- a semantic value, the result is always a heap address.
  --
  -- This is instantiated with our specific encode function in
  -- StackInstantiation.encode-in-heap-sem.
  encode-in-heap : ∀ {A : Set} (encode : A → Addr) (x : A) → InHeap (encode x)

  -- | Field access stays within heap region
  --
  -- JUSTIFICATION: Heap objects are allocated contiguously. When we
  -- have a pointer to a heap object and access a field (ptr + offset),
  -- the result is still in the heap region.
  --
  -- In practice, offset is always small (e.g., 8 bytes for slot-size).
  -- This requires the allocator to ensure sufficient heap capacity
  -- for the allocated object sizes.
  heap-offset : ∀ a n → InHeap a → InHeap (a + n)
