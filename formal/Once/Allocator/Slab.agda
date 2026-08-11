-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Allocator.Slab
--
-- A slab allocator with multiple size classes.
--
-- This wraps multiple Mempools, one per size class:
--   - Size class 1: 1 slot (8 bytes) - primitives
--   - Size class 2: 2 slots (16 bytes) - pairs, closures
--   - Size class 3: 3 slots (24 bytes) - tagged pairs (sums)
--   - Size class 4: 4 slots (32 bytes) - larger structures
--
-- Operations:
--   - alloc n: O(1) - find size class ≥ n, pop from its free list
--   - free n addr: O(1) - push to size class n's free list
--
-- Key properties:
--   - alloc-in-heap: allocated blocks are in heap region
--   - size-class-correct: allocated block has at least n slots
------------------------------------------------------------------------

open import Once.Memory.MemoryLayoutSemantics
  using (MemoryLayout; Addr; RegionBounds; lower; upper)

module Once.Allocator.Slab (layout : MemoryLayout) where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _<_; _≤_; _≤?_; _∸_)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-step; m≤m+n; +-comm; +-assoc;
         +-monoʳ-≤; *-monoˡ-≤; ≤-reflexive; <-trans; ≤-<-trans)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Fin.Properties using (_≟_)
open import Data.Vec using (Vec; []; _∷_; lookup; updateAt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (Dec; yes; no; ¬_)

-- Import heap region definition
open import Once.Memory.Regions layout using (InHeap)
open import Once.Memory.Regions layout as Regions using (heap-bounds)

-- Import Mempool
open import Once.Allocator.Mempool layout as Mempool
  using (PoolState; mkPoolState; pool-start; pool-end; block-slots;
         free-list; pool-in-heap; free-list-valid)
  renaming (slot-size to mempool-slot-size)

------------------------------------------------------------------------
-- Vector updateAt lemmas
------------------------------------------------------------------------

-- lookup at updated index returns the updated value
lookup-updateAt-same : ∀ {A : Set} {n : ℕ} (xs : Vec A n) (i : Fin n) (f : A → A) →
                       lookup (updateAt xs i f) i ≡ f (lookup xs i)
lookup-updateAt-same (x ∷ xs) zero f = refl
lookup-updateAt-same (x ∷ xs) (suc i) f = lookup-updateAt-same xs i f

-- lookup at different index is unchanged
lookup-updateAt-diff : ∀ {A : Set} {n : ℕ} (xs : Vec A n) (i j : Fin n) (f : A → A) →
                       i ≢ j →
                       lookup (updateAt xs j f) i ≡ lookup xs i
lookup-updateAt-diff (x ∷ xs) zero zero f i≢j = ⊥-elim (i≢j refl)
  where open import Data.Empty using (⊥-elim)
lookup-updateAt-diff (x ∷ xs) zero (suc j) f i≢j = refl
lookup-updateAt-diff (x ∷ xs) (suc i) zero f i≢j = refl
lookup-updateAt-diff (x ∷ xs) (suc i) (suc j) f i≢j =
  lookup-updateAt-diff xs i j f (λ eq → i≢j (cong suc eq))

------------------------------------------------------------------------
-- Configuration
------------------------------------------------------------------------

-- Slot size (same as other allocators)
slot-size : ℕ
slot-size = 8

-- Number of size classes
-- We support 1, 2, 3, 4 slot allocations
num-size-classes : ℕ
num-size-classes = 4

-- Size class index
SizeClass : Set
SizeClass = Fin num-size-classes

-- Get block size (in slots) for a size class
-- Index 0 → 1 slot, Index 1 → 2 slots, etc.
class-slots : SizeClass → ℕ
class-slots i = suc (toℕ i)

------------------------------------------------------------------------
-- Slab State
--
-- A slab allocator is a vector of mempools, one per size class.
------------------------------------------------------------------------

record SlabState : Set where
  constructor mkSlabState
  field
    -- One pool per size class
    pools : Vec PoolState num-size-classes

    -- All pools have correct block sizes
    pools-sized : ∀ (i : SizeClass) →
                  block-slots (lookup pools i) ≡ class-slots i

open SlabState public

------------------------------------------------------------------------
-- Size Class Selection
--
-- Find the smallest size class that can hold n slots.
------------------------------------------------------------------------

-- Find size class for n slots (returns nothing if n > 4)
find-class : (n : ℕ) → Maybe SizeClass
find-class zero = just zero                           -- 0 slots → class 0 (1 slot)
find-class (suc zero) = just zero                     -- 1 slot → class 0
find-class (suc (suc zero)) = just (suc zero)         -- 2 slots → class 1
find-class (suc (suc (suc zero))) = just (suc (suc zero))  -- 3 slots → class 2
find-class (suc (suc (suc (suc zero)))) = just (suc (suc (suc zero)))  -- 4 slots → class 3
find-class _ = nothing                                -- > 4 slots → not supported

-- The selected class has enough slots
class-has-slots : ∀ n (c : SizeClass) →
                  find-class n ≡ just c →
                  n ≤ class-slots c
class-has-slots zero zero refl = Data.Nat.z≤n
class-has-slots (suc zero) zero refl = ≤-refl
class-has-slots (suc (suc zero)) (suc zero) refl = ≤-refl
class-has-slots (suc (suc (suc zero))) (suc (suc zero)) refl = ≤-refl
class-has-slots (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) refl = ≤-refl

------------------------------------------------------------------------
-- Allocation
------------------------------------------------------------------------

record SlabAllocResult (s : SlabState) (n : ℕ) : Set where
  constructor mkSlabAllocResult
  field
    addr : Addr
    new-state : SlabState
    size-class : SizeClass

    -- We got at least n slots
    enough-slots : n ≤ class-slots size-class

    -- All slots of the block are in heap
    slots-in-heap : ∀ i → i < class-slots size-class → InHeap (addr + i * slot-size)

open SlabAllocResult public

-- Allocate n slots from the slab
alloc : (n : ℕ) (s : SlabState) →
        {c : SizeClass} →
        find-class n ≡ just c →
        Maybe (SlabAllocResult s n)
alloc n s {c} fc≡c with Mempool.alloc (lookup (pools s) c)
... | nothing = nothing  -- Pool exhausted
... | just result = just (mkSlabAllocResult
    (Mempool.AllocResult.addr result)
    s'
    c
    (class-has-slots n c fc≡c)
    slots-in-heap-proof)
  where
    old-pool = lookup (pools s) c
    new-pool = Mempool.AllocResult.new-state result

    -- Update the pool in the vector
    new-pools : Vec PoolState num-size-classes
    new-pools = updateAt (pools s) c (λ _ → new-pool)

    -- Mempool.alloc preserves block-slots
    new-pool-block-slots : block-slots new-pool ≡ block-slots old-pool
    new-pool-block-slots = Mempool.AllocResult.block-slots-preserved result

    -- All pools still have correct sizes
    new-pools-sized : ∀ (i : SizeClass) → block-slots (lookup new-pools i) ≡ class-slots i
    new-pools-sized i with i ≟ c
    ... | yes refl = trans (cong block-slots (lookup-updateAt-same (pools s) c (λ _ → new-pool)))
                           (trans new-pool-block-slots (pools-sized s c))
    ... | no i≢c = trans (cong block-slots (lookup-updateAt-diff (pools s) i c (λ _ → new-pool) i≢c))
                         (pools-sized s i)

    s' : SlabState
    s' = mkSlabState new-pools new-pools-sized

    -- block-slots of old-pool equals class-slots c
    pool-sized : block-slots old-pool ≡ class-slots c
    pool-sized = pools-sized s c

    -- Convert i < class-slots c to i < block-slots old-pool
    class-to-pool : ∀ i → i < class-slots c → i < block-slots old-pool
    class-to-pool i i<class = subst (i <_) (sym pool-sized) i<class

    -- All slots are in heap (from Mempool proof)
    slots-in-heap-proof : ∀ i → i < class-slots c → InHeap (Mempool.AllocResult.addr result + i * slot-size)
    slots-in-heap-proof i i<class = Mempool.block-slot-in-heap old-pool result i (class-to-pool i i<class)

------------------------------------------------------------------------
-- Deallocation (Free)
--
-- Return a block to its size class pool.
-- Linear types guarantee this is called exactly once per allocation.
------------------------------------------------------------------------

-- Free a block back to its size class
free : (c : SizeClass) (addr : Addr) (s : SlabState) →
       (start-ok : pool-start (lookup (pools s) c) ≤ addr) →
       (end-ok : addr + class-slots c * slot-size ≤ pool-end (lookup (pools s) c)) →
       SlabState
free c addr s start-ok end-ok = mkSlabState new-pools new-pools-sized
  where
    pool = lookup (pools s) c

    -- Need to convert end-ok to use block-slots instead of class-slots
    end-ok' : addr + block-slots pool * slot-size ≤ pool-end pool
    end-ok' = subst (λ bs → addr + bs * slot-size ≤ pool-end pool)
                    (sym (pools-sized s c))
                    end-ok

    freed-pool : PoolState
    freed-pool = Mempool.free addr pool start-ok end-ok'

    -- Mempool.free preserves block-slots
    freed-pool-block-slots : block-slots freed-pool ≡ block-slots pool
    freed-pool-block-slots = refl

    new-pools : Vec PoolState num-size-classes
    new-pools = updateAt (pools s) c (λ _ → freed-pool)

    -- All pools still have correct sizes
    new-pools-sized : ∀ (i : SizeClass) → block-slots (lookup new-pools i) ≡ class-slots i
    new-pools-sized i with i ≟ c
    ... | yes refl = trans (cong block-slots (lookup-updateAt-same (pools s) c (λ _ → freed-pool)))
                           (trans freed-pool-block-slots (pools-sized s c))
    ... | no i≢c = trans (cong block-slots (lookup-updateAt-diff (pools s) i c (λ _ → freed-pool) i≢c))
                         (pools-sized s i)

------------------------------------------------------------------------
-- Block slots are in heap
------------------------------------------------------------------------

-- All slots of an allocated block are in heap
-- (This is now trivial since SlabAllocResult stores the proof directly)
block-slot-in-heap : (s : SlabState) (n : ℕ) (c : SizeClass)
                     (fc≡c : find-class n ≡ just c)
                     (result : SlabAllocResult s n)
                     (i : ℕ) → i < class-slots (size-class result) →
                     InHeap (addr result + i * slot-size)
block-slot-in-heap s n c fc≡c result i i<class = slots-in-heap result i i<class

------------------------------------------------------------------------
-- Malloc Interface Implementation
--
-- For Once's linear types, the compiler knows allocation sizes from types.
-- So malloc-free can take size as parameter (compiler generates it).
------------------------------------------------------------------------

open import Once.Allocator.Malloc layout as M using (Malloc)

-- class-slots is always ≥ 1 (needed for InHeap proof)
class-slots-pos : ∀ c → 0 < class-slots c
class-slots-pos zero = Data.Nat.s≤s Data.Nat.z≤n
class-slots-pos (suc zero) = Data.Nat.s≤s Data.Nat.z≤n
class-slots-pos (suc (suc zero)) = Data.Nat.s≤s Data.Nat.z≤n
class-slots-pos (suc (suc (suc zero))) = Data.Nat.s≤s Data.Nat.z≤n

-- Malloc-compatible alloc: find size class, allocate from it
-- Defined by explicit case analysis on find-class
malloc-alloc : ℕ → SlabState → Maybe (Addr × SlabState)
malloc-alloc zero s with alloc zero s {zero} refl
... | nothing = nothing
... | just result = just (addr result , new-state result)
malloc-alloc (suc zero) s with alloc 1 s {zero} refl
... | nothing = nothing
... | just result = just (addr result , new-state result)
malloc-alloc (suc (suc zero)) s with alloc 2 s {suc zero} refl
... | nothing = nothing
... | just result = just (addr result , new-state result)
malloc-alloc (suc (suc (suc zero))) s with alloc 3 s {suc (suc zero)} refl
... | nothing = nothing
... | just result = just (addr result , new-state result)
malloc-alloc (suc (suc (suc (suc zero)))) s with alloc 4 s {suc (suc (suc zero))} refl
... | nothing = nothing
... | just result = just (addr result , new-state result)
malloc-alloc (suc (suc (suc (suc (suc _))))) s = nothing  -- > 4 slots not supported

-- Malloc-compatible free: no-op without size info
malloc-free : Addr → SlabState → SlabState
malloc-free addr s = s

-- For proper free, we provide a sized version
malloc-free-sized : ℕ → Addr → SlabState → SlabState
malloc-free-sized n addr s with find-class n
... | nothing = s
... | just c with pool-start (lookup (pools s) c) ≤? addr
...   | no _ = s
...   | yes start-ok with addr + class-slots c * slot-size ≤? pool-end (lookup (pools s) c)
...     | no _ = s
...     | yes end-ok = free c addr s start-ok end-ok

-- Helper: InHeap for base address of an allocation result
result-in-heap : ∀ {n} {s : SlabState} (result : SlabAllocResult s n) → InHeap (addr result)
result-in-heap result =
  subst InHeap (Data.Nat.Properties.+-identityʳ (addr result))
        (slots-in-heap result 0 (class-slots-pos (size-class result)))

-- Proof: malloc-alloc returns InHeap addresses (case by case)
malloc-alloc-in-heap : ∀ {n s addr s'} →
                       malloc-alloc n s ≡ just (addr , s') →
                       InHeap addr
malloc-alloc-in-heap {zero} {s} ma-eq with alloc zero s {zero} refl
malloc-alloc-in-heap {zero} {s} () | nothing
malloc-alloc-in-heap {zero} {s} refl | just result = result-in-heap {zero} {s} result
malloc-alloc-in-heap {suc zero} {s} ma-eq with alloc 1 s {zero} refl
malloc-alloc-in-heap {suc zero} {s} () | nothing
malloc-alloc-in-heap {suc zero} {s} refl | just result = result-in-heap {suc zero} {s} result
malloc-alloc-in-heap {suc (suc zero)} {s} ma-eq with alloc 2 s {suc zero} refl
malloc-alloc-in-heap {suc (suc zero)} {s} () | nothing
malloc-alloc-in-heap {suc (suc zero)} {s} refl | just result = result-in-heap {suc (suc zero)} {s} result
malloc-alloc-in-heap {suc (suc (suc zero))} {s} ma-eq with alloc 3 s {suc (suc zero)} refl
malloc-alloc-in-heap {suc (suc (suc zero))} {s} () | nothing
malloc-alloc-in-heap {suc (suc (suc zero))} {s} refl | just result = result-in-heap {suc (suc (suc zero))} {s} result
malloc-alloc-in-heap {suc (suc (suc (suc zero)))} {s} ma-eq with alloc 4 s {suc (suc (suc zero))} refl
malloc-alloc-in-heap {suc (suc (suc (suc zero)))} {s} () | nothing
malloc-alloc-in-heap {suc (suc (suc (suc zero)))} {s} refl | just result = result-in-heap {suc (suc (suc (suc zero)))} {s} result
malloc-alloc-in-heap {suc (suc (suc (suc (suc _))))} {s} ()

-- Initial slab state: empty pools (no blocks available until filled)
-- This is a minimal implementation; architecture-specific code should
-- fill the pools with actual block addresses.

-- Helper: create an empty pool for a given block size
empty-pool : (bs : ℕ) → PoolState
empty-pool bs = mkPoolState
  bs                                  -- block-slots
  (lower Regions.heap-bounds)         -- pool-start
  (lower Regions.heap-bounds)         -- pool-end (same as start = no blocks)
  []                                  -- free-list (empty)
  (≤-refl , heap-bounds-ok)           -- pool-in-heap
  (λ {addr} → empty-valid {addr})     -- free-list-valid (vacuously true)
  where
    heap-bounds-ok : lower Regions.heap-bounds ≤ upper Regions.heap-bounds
    heap-bounds-ok = RegionBounds.bounds-valid Regions.heap-bounds

    -- ⊥-elim from Data.Empty
    open import Data.Empty using (⊥-elim)

    -- Membership in empty list is ⊥, so any property follows
    empty-valid : ∀ {addr} → addr Mempool.∈-list [] →
                  lower Regions.heap-bounds ≤ addr ×
                  addr + bs * slot-size ≤ lower Regions.heap-bounds
    empty-valid ()

-- Initial pools vector: one empty pool per size class
init-pools : Vec PoolState num-size-classes
init-pools =
  empty-pool 1 ∷       -- class 0: 1 slot
  empty-pool 2 ∷       -- class 1: 2 slots
  empty-pool 3 ∷       -- class 2: 3 slots
  empty-pool 4 ∷       -- class 3: 4 slots
  []

-- Proof that init-pools has correct sizes
init-pools-sized : ∀ (i : SizeClass) → block-slots (lookup init-pools i) ≡ class-slots i
init-pools-sized zero = refl
init-pools-sized (suc zero) = refl
init-pools-sized (suc (suc zero)) = refl
init-pools-sized (suc (suc (suc zero))) = refl

-- The initial slab state
init-slab : SlabState
init-slab = mkSlabState init-pools init-pools-sized

-- Package as Malloc interface
asMalloc : Malloc
asMalloc = record
  { State = SlabState
  ; init = init-slab
  ; alloc = malloc-alloc
  ; free = malloc-free
  ; alloc-in-heap = λ {n} {s} {addr} {s'} eq → malloc-alloc-in-heap {n} {s} {addr} {s'} eq
  }

------------------------------------------------------------------------
-- Summary
--
-- Slab provides:
--
--   SlabState     : vector of mempools, one per size class
--   alloc n       : find class ≥ n, pop from its free list, O(1)
--   free c addr   : push to class c's free list, O(1)
--
-- Malloc interface:
--   asMalloc      : Malloc (free is no-op without size)
--   malloc-free-sized : proper free with size parameter
--
-- Size classes:
--   0 → 1 slot (8 bytes)  - primitives, tagged pointers
--   1 → 2 slots (16 bytes) - pairs, closures
--   2 → 3 slots (24 bytes) - tagged pairs (sum types)
--   3 → 4 slots (32 bytes) - larger structures
--
-- Properties:
--   alloc returns InHeap address
--   class-has-slots ensures enough space
--
-- For larger allocations (> 4 slots), fall back to BumpAllocator
-- or implement additional size classes.
------------------------------------------------------------------------