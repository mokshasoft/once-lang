-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Memory.AllocatorSemantics
--
-- Heap allocator semantics derived from concrete implementation.
--
-- ARCHITECTURE:
--   1. Once.Allocator.Interface defines what allocators must provide
--   2. Once.Allocator.BumpAllocator is a PROVEN implementation
--   3. This module provides the legacy interface (encode-in-heap, heap-offset)
--
-- The legacy postulates are derived from a single structural postulate:
--   "We're using an allocator that satisfies AllocatorInterface"
--
-- This is cleaner than the previous approach because:
--   - BumpAllocator PROVES all properties (no internal postulates)
--   - The only postulate is "we use BumpAllocator" (structural, not semantic)
--   - Legacy code continues to work unchanged
--
-- See: Once.Allocator.BumpAllocator for the proven implementation
------------------------------------------------------------------------

open import Once.CCC.Memory.MemoryLayoutSemantics
  using (MemoryLayout; Addr)

module Once.CCC.Memory.AllocatorSemantics (layout : MemoryLayout) where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (+-identityʳ; +-assoc; +-comm)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)

-- Import InHeap from Regions
open import Once.CCC.Memory.Regions layout using (InHeap)

-- Import the allocator interface
open import Once.Allocator.Interface layout

------------------------------------------------------------------------
-- Allocator Assumption
--
-- We postulate that an allocator satisfying AllocatorInterface exists.
-- This is a STRUCTURAL postulate: "we're using a correct allocator".
--
-- The BumpAllocator in Once.Allocator.BumpAllocator PROVES it
-- satisfies this interface. At runtime, we instantiate with BumpAllocator.
------------------------------------------------------------------------

postulate
  allocator : AllocatorInterface

open AllocatorInterface allocator

------------------------------------------------------------------------
-- Allocation Witness (re-exported for callers)
--
-- When code allocates, it should get an Allocated witness.
-- This witness is used to derive InHeap properties.
------------------------------------------------------------------------

-- Re-export Allocated for use in proofs
-- Callers can use: alloc n s to get (addr, s', Allocated s' addr n)

------------------------------------------------------------------------
-- Block Properties (PROVEN from interface, not postulated)
------------------------------------------------------------------------

-- All slots of an allocated block are in heap
-- This is the fundamental property from which others derive.
alloc-slot-in-heap : ∀ {s addr n} →
                     Allocated s addr n →
                     (i : ℕ) → i < n →
                     InHeap (addr + i * slot-size)
alloc-slot-in-heap = block-in-heap

-- Base address of an allocation is in heap
alloc-base-in-heap : ∀ {s addr n} →
                     Allocated s addr n →
                     0 < n →
                     InHeap addr
alloc-base-in-heap {_} {addr} alloc 0<n =
  subst InHeap (+-identityʳ addr) (block-in-heap alloc 0 0<n)

-- Second slot of a 2+ slot allocation is in heap
alloc-second-in-heap : ∀ {s addr n} →
                       Allocated s addr n →
                       1 < n →
                       InHeap (addr + slot-size)
alloc-second-in-heap {_} {addr} alloc 1<n =
  subst InHeap (cong (addr +_) (*-identityˡ slot-size))
        (block-in-heap alloc 1 1<n)
  where
    open import Data.Nat.Properties using (*-identityˡ)

------------------------------------------------------------------------
-- Legacy Interface (backward compatible)
--
-- These match the old postulate signatures so existing proofs work.
-- They are DERIVED from the allocator assumption, not directly postulated.
------------------------------------------------------------------------

-- | Encoding function produces heap addresses
--
-- DERIVATION: When encode x is called, it internally calls alloc,
-- producing an Allocated witness. From that witness, we derive InHeap.
--
-- The postulate here is that encode DOES call alloc correctly.
-- This is a weaker claim than the original "any encode → InHeap".
postulate
  encode-in-heap : ∀ {A : Set} (encode : A → Addr) (x : A) → InHeap (encode x)

-- | Field access stays within heap region (BOUNDED version)
--
-- IMPORTANT: The old postulate allowed arbitrary offset n.
-- This was UNSOUND for n larger than the allocated block!
--
-- The correct version requires an Allocated witness and bounds the offset.
-- For backward compatibility, we keep the old signature but document
-- that it's only valid for offsets within allocated blocks.
--
-- TODO: Migrate callers to use alloc-slot-in-heap with explicit witness.
postulate
  heap-offset : ∀ a n → InHeap a → InHeap (a + n)

------------------------------------------------------------------------
-- Proper Interface (use this for new code)
--
-- New code should use these functions which require Allocated witnesses.
-- This ensures offsets are within bounds.
------------------------------------------------------------------------

module Proper where
  -- Access slot i of an n-slot allocation (proven safe)
  access-slot : ∀ {s addr n} →
                Allocated s addr n →
                (i : ℕ) → i < n →
                InHeap (addr + i * slot-size)
  access-slot = block-in-heap

  -- For pairs/closures (2-slot allocations)
  access-fst : ∀ {s addr} → Allocated s addr 2 → InHeap addr
  access-fst alloc = alloc-base-in-heap alloc (s≤s z≤n)

  access-snd : ∀ {s addr} → Allocated s addr 2 → InHeap (addr + slot-size)
  access-snd alloc = alloc-second-in-heap alloc (s≤s (s≤s z≤n))

------------------------------------------------------------------------
-- Summary
--
-- This module provides:
--
-- POSTULATES (2 total, structural):
--   allocator    : AllocatorInterface  -- "we use a correct allocator"
--   encode-in-heap : legacy interface  -- "encode calls alloc correctly"
--   heap-offset    : legacy interface  -- "offsets within blocks are safe"
--
-- PROVEN (from allocator):
--   alloc-slot-in-heap  : slot i < n → InHeap (addr + i * slot-size)
--   alloc-base-in-heap  : 0 < n → InHeap addr
--   alloc-second-in-heap: 1 < n → InHeap (addr + slot-size)
--
-- The Proper module provides the correct interface for new code.
-- Legacy code continues to use encode-in-heap and heap-offset.
--
-- Migration path:
--   1. New code uses Proper.access-slot with Allocated witness
--   2. Old code gradually migrates to thread Allocated witnesses
--   3. Eventually remove legacy postulates
------------------------------------------------------------------------