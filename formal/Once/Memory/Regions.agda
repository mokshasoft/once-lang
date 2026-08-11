-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Memory.Regions
--
-- Abstract memory region predicates and disjointness.
--
-- This module is PARAMETERIZED over MemoryLayout, which provides
-- concrete region bounds. It defines:
--   - InStack, InHeap, InCode predicates
--   - Disjointness theorems
--
-- IR proofs should import this module to stay region-based and abstract.
-- They should NOT import architecture-specific modules like X86.Layout.
------------------------------------------------------------------------

open import Once.Memory.MemoryLayoutSemantics
  using (MemoryLayout; RegionBounds; Addr; lower; upper; InRegion)

module Once.Memory.Regions (layout : MemoryLayout) where

open import Data.Nat using (ℕ; _≤_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥)

-- Re-export Addr for convenience
open import Once.Memory.MemoryLayoutSemantics public using (Addr)

------------------------------------------------------------------------
-- Region Bounds (from layout parameter)
------------------------------------------------------------------------

stack-bounds : RegionBounds
stack-bounds = MemoryLayout.stack-bounds layout

heap-bounds : RegionBounds
heap-bounds = MemoryLayout.heap-bounds layout

code-bounds : RegionBounds
code-bounds = MemoryLayout.code-bounds layout

------------------------------------------------------------------------
-- Region Membership Predicates
------------------------------------------------------------------------

-- | Address is in stack region
InStack : Addr → Set
InStack a = lower stack-bounds ≤ a × a ≤ upper stack-bounds

-- | Address is in heap region
InHeap : Addr → Set
InHeap a = lower heap-bounds ≤ a × a ≤ upper heap-bounds

-- | Address is in code region
InCode : Addr → Set
InCode a = lower code-bounds ≤ a × a ≤ upper code-bounds

------------------------------------------------------------------------
-- Disjointness (from layout parameter)
------------------------------------------------------------------------

intervals-disjoint : ∀ a →
  ¬ (InStack a × InHeap a) ×
  ¬ (InStack a × InCode a) ×
  ¬ (InHeap a × InCode a)
intervals-disjoint = MemoryLayout.intervals-disjoint layout

------------------------------------------------------------------------
-- Derived Disjointness Theorems
------------------------------------------------------------------------

-- | Stack and heap regions don't overlap
stack-heap-disjoint : ∀ a → InStack a → InHeap a → ⊥
stack-heap-disjoint a in-s in-h = proj₁ (intervals-disjoint a) (in-s , in-h)

-- | Stack and code regions don't overlap
stack-code-disjoint : ∀ a → InStack a → InCode a → ⊥
stack-code-disjoint a in-s in-c = proj₁ (proj₂ (intervals-disjoint a)) (in-s , in-c)

-- | Heap and code regions don't overlap
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
-- Heap Address Type (bundled with region proof)
------------------------------------------------------------------------

-- | Heap address: in heap region by construction
-- Field name 'haddr' for backward compatibility with HeapPointer usage
record HeapAddr : Set where
  constructor heap-addr
  field
    haddr : Addr
    in-heap : InHeap haddr

open HeapAddr public

-- | Alias for backward compatibility
HeapPointer : Set
HeapPointer = HeapAddr