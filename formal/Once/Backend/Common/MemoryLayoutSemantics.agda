------------------------------------------------------------------------
-- Once.Backend.Common.MemoryLayoutSemantics
--
-- FOUNDATIONAL POSTULATES for memory layout.
--
-- This module contains ONLY the minimal postulates that represent
-- runtime guarantees about memory layout:
--   1. Region bounds exist (stack, heap, code)
--   2. Regions are disjoint
--
-- Everything else (theorems, lemmas) belongs in MemoryRegionLemmas.
------------------------------------------------------------------------

module Once.Backend.Common.MemoryLayoutSemantics where

open import Data.Nat using (ℕ; _≤_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_)

-- Import Memory type from Common.Memory
open import Once.Backend.Common.Memory using (Word) public

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
--
-- JUSTIFICATION: Runtime initializes memory with these regions.
-- These are the only structural postulates needed.
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
-- Region Disjointness (THE KEY SEMANTIC POSTULATE)
--
-- JUSTIFICATION: Runtime initializes memory with non-overlapping regions.
-- This is the only semantic postulate needed - all disjointness
-- theorems follow from this.
------------------------------------------------------------------------

postulate
  intervals-disjoint : ∀ a →
    ¬ (InStack a × InHeap a) ×
    ¬ (InStack a × InCode a) ×
    ¬ (InHeap a × InCode a)
