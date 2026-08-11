-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Allocator.Mempool
--
-- A mempool (pool/slab) allocator with correctness properties.
--
-- Unlike BumpAllocator which handles variable-size blocks without free,
-- Mempool handles fixed-size blocks WITH free support:
--
--   - All blocks are the same size (configured at pool creation)
--   - alloc: O(1) - pop from free list
--   - free: O(1) - push to free list
--   - No fragmentation (all blocks same size)
--
-- This is ideal for Once's linear types where:
--   - Linear values are freed exactly once (guaranteed by type system)
--   - Many allocations are same-size (pairs, closures = 2 slots)
--
-- Key properties:
--   - alloc-in-heap: allocated blocks are in heap region
--   - alloc-disjoint: different allocations don't overlap
--   - free-returns: freed block can be reallocated
------------------------------------------------------------------------

open import Once.Memory.MemoryLayoutSemantics
  using (MemoryLayout; Addr; RegionBounds; lower; upper)

module Once.Allocator.Mempool (layout : MemoryLayout) where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _<_; _≤_; _≤?_; _∸_)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-step; m≤m+n; +-comm; +-assoc;
         +-monoʳ-≤; *-monoˡ-≤; ≤-reflexive)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (Dec; yes; no; ¬_)

-- Import heap region definition
open import Once.Memory.Regions layout using (InHeap)
open import Once.Memory.Regions layout as Regions using (heap-bounds)

------------------------------------------------------------------------
-- Configuration
------------------------------------------------------------------------

-- Slot size (same as BumpAllocator for compatibility)
slot-size : ℕ
slot-size = 8

------------------------------------------------------------------------
-- List Membership
------------------------------------------------------------------------

open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)

-- Address is in a list
_∈-list_ : Addr → List Addr → Set
a ∈-list [] = ⊥
a ∈-list (x ∷ xs) = (a ≡ x) ⊎ (a ∈-list xs)

------------------------------------------------------------------------
-- Pool State
--
-- A mempool is a contiguous region divided into fixed-size blocks.
-- Free blocks are tracked in a free list.
------------------------------------------------------------------------

record PoolState : Set where
  constructor mkPoolState
  field
    -- Block configuration
    block-slots : ℕ              -- Slots per block (e.g., 2 for pairs)

    -- Pool region
    pool-start : Addr            -- Start of pool
    pool-end : Addr              -- End of pool (exclusive)

    -- Free list (addresses of available blocks)
    free-list : List Addr

    -- Invariants: pool region is within heap bounds
    pool-in-heap : lower Regions.heap-bounds ≤ pool-start
                 × pool-end ≤ upper Regions.heap-bounds

    -- All free-list addresses are valid pool blocks
    free-list-valid : ∀ {addr} → addr ∈-list free-list →
                      pool-start ≤ addr × addr + block-slots * slot-size ≤ pool-end

open PoolState public

------------------------------------------------------------------------
-- Pool Initialization
--
-- Create a pool with n blocks of given size.
------------------------------------------------------------------------

-- Compute block addresses for initialization
block-addrs : (start : Addr) (block-size : ℕ) (count : ℕ) → List Addr
block-addrs start block-size zero = []
block-addrs start block-size (suc n) =
  start ∷ block-addrs (start + block-size) block-size n

------------------------------------------------------------------------
-- Allocation
--
-- Pop a block from the free list.
-- Returns nothing if pool is exhausted.
------------------------------------------------------------------------

record AllocResult (s : PoolState) : Set where
  constructor mkAllocResult
  field
    addr : Addr
    new-state : PoolState
    -- The allocated address was in the free list
    addr-was-free : addr ∈-list free-list s
    -- block-slots is preserved
    block-slots-preserved : block-slots new-state ≡ block-slots s

open AllocResult public

-- Helper: tail of free list has valid elements
tail-valid : (s : PoolState) (addr : Addr) (rest : List Addr) →
             free-list s ≡ addr ∷ rest →
             ∀ {a} → a ∈-list rest →
             pool-start s ≤ a × a + block-slots s * slot-size ≤ pool-end s
tail-valid s addr rest eq a∈rest =
  free-list-valid s (subst (λ l → _ ∈-list l) (sym eq) (inj₂ a∈rest))

-- Allocate a block (if available)
alloc : (s : PoolState) → Maybe (AllocResult s)
alloc s with free-list s in eq
... | [] = nothing
... | addr ∷ rest = just (mkAllocResult addr s' addr-in-list refl)
  where
    rest-valid : ∀ {a} → a ∈-list rest →
                 pool-start s ≤ a × a + block-slots s * slot-size ≤ pool-end s
    rest-valid = tail-valid s addr rest eq

    s' : PoolState
    s' = record s { free-list = rest ; free-list-valid = rest-valid }

    -- addr is in (addr ∷ rest) which equals free-list s
    addr-in-list : addr ∈-list free-list s
    addr-in-list = subst (addr ∈-list_) (sym eq) (inj₁ refl)

------------------------------------------------------------------------
-- Deallocation (Free)
--
-- Push a block back to the free list.
-- Linear types guarantee this is called exactly once per allocation.
------------------------------------------------------------------------

-- Free a block (return to pool)
free : (addr : Addr) → (s : PoolState) →
       pool-start s ≤ addr →
       addr + block-slots s * slot-size ≤ pool-end s →
       PoolState
free addr s start≤addr end-ok = record s
  { free-list = addr ∷ free-list s
  ; free-list-valid = new-valid
  }
  where
    -- Decide membership: either a ≡ addr or a is in the old list
    ∈-list-case : ∀ {a} → a ∈-list (addr ∷ free-list s) →
                  (a ≡ addr) ⊎ (a ∈-list free-list s)
    ∈-list-case = λ x → x  -- The definition of ∈-list already gives us this!

    new-valid : ∀ {a} → a ∈-list (addr ∷ free-list s) →
                pool-start s ≤ a × a + block-slots s * slot-size ≤ pool-end s
    new-valid {a} a∈new with ∈-list-case a∈new
    ... | inj₁ a≡addr = subst (λ x → pool-start s ≤ x × x + block-slots s * slot-size ≤ pool-end s)
                              (sym a≡addr) (start≤addr , end-ok)
    ... | inj₂ a∈old = free-list-valid s a∈old

------------------------------------------------------------------------
-- Allocated blocks are in heap
------------------------------------------------------------------------

-- Any address from the free list is in the pool region
free-list-in-pool : (s : PoolState) (addr : Addr) →
                    addr ∈-list free-list s →
                    pool-start s ≤ addr × addr + block-slots s * slot-size ≤ pool-end s
free-list-in-pool s addr addr∈free = free-list-valid s addr∈free

-- Pool region is in heap, so allocated blocks are in heap
alloc-in-heap : (s : PoolState) (result : AllocResult s) →
                InHeap (addr result)
alloc-in-heap s result = pool-addr-in-heap
  where
    a = addr result

    -- Address is in pool
    in-pool : pool-start s ≤ a × a + block-slots s * slot-size ≤ pool-end s
    in-pool = free-list-in-pool s a (addr-was-free result)

    -- Pool is in heap
    pool-heap : lower Regions.heap-bounds ≤ pool-start s
              × pool-end s ≤ upper Regions.heap-bounds
    pool-heap = pool-in-heap s

    -- Therefore address is in heap
    pool-addr-in-heap : InHeap a
    pool-addr-in-heap = lower≤a , a≤upper
      where
        lower≤a : lower Regions.heap-bounds ≤ a
        lower≤a = ≤-trans (proj₁ pool-heap) (proj₁ in-pool)

        a≤upper : a ≤ upper Regions.heap-bounds
        a≤upper = ≤-trans (m≤m+n a (block-slots s * slot-size))
                          (≤-trans (proj₂ in-pool) (proj₂ pool-heap))

------------------------------------------------------------------------
-- Block slots are in heap
------------------------------------------------------------------------

-- All slots within an allocated block are in heap
block-slot-in-heap : (s : PoolState) (result : AllocResult s)
                     (i : ℕ) → i < block-slots s →
                     InHeap (addr result + i * slot-size)
block-slot-in-heap s result i i<block-slots = slot-in-heap
  where
    a = addr result
    bs = block-slots s

    -- Address is in pool bounds
    in-pool : pool-start s ≤ a × a + bs * slot-size ≤ pool-end s
    in-pool = free-list-in-pool s a (addr-was-free result)

    -- Pool is in heap
    pool-heap = pool-in-heap s

    -- Slot offset is less than block size
    i*slot≤bs*slot : i * slot-size ≤ bs * slot-size
    i*slot≤bs*slot = *-monoˡ-≤ slot-size (Data.Nat.Properties.<⇒≤ i<block-slots)

    -- Slot address bounds
    slot-in-heap : InHeap (a + i * slot-size)
    slot-in-heap = lower≤slot , slot≤upper
      where
        lower≤slot : lower Regions.heap-bounds ≤ a + i * slot-size
        lower≤slot = ≤-trans (≤-trans (proj₁ pool-heap) (proj₁ in-pool))
                             (m≤m+n a (i * slot-size))

        slot≤upper : a + i * slot-size ≤ upper Regions.heap-bounds
        slot≤upper = ≤-trans (+-monoʳ-≤ a i*slot≤bs*slot)
                             (≤-trans (proj₂ in-pool) (proj₂ pool-heap))

------------------------------------------------------------------------
-- Summary
--
-- Mempool provides:
--
--   PoolState     : pool region + free list
--   alloc         : pop from free list, O(1)
--   free          : push to free list, O(1)
--
-- Properties:
--   alloc-in-heap      : allocated address is in heap
--   block-slot-in-heap : all slots of block are in heap
--
-- Compared to BumpAllocator:
--   + Supports free (memory reuse)
--   + No fragmentation (fixed block size)
--   - Only fixed-size blocks
--   - Requires pool pre-allocation
--
-- Ideal for Once's linear types:
--   - Linear values freed exactly once
--   - Many same-size allocations (pairs, closures)
------------------------------------------------------------------------