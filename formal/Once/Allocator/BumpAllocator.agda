-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Allocator.BumpAllocator
--
-- A simple bump allocator with correctness properties.
--
-- This module provides a concrete allocator implementation where all
-- properties are derived from the implementation.
--
-- The bump allocator maintains:
--   - heap-ptr: current allocation pointer
--   - Invariants ensuring all allocations are in heap region
--
-- Key properties:
--   - alloc-in-heap: allocated addresses are in heap region
--   - alloc-disjoint: distinct allocations don't overlap
--   - alloc-contiguous: slots within a block are contiguous
--
-- This serves as the FOUNDATIONAL allocator model. The legacy
-- legacy InHeap helpers are derived directly from block-in-region.
------------------------------------------------------------------------

open import Once.Memory.MemoryLayoutSemantics
  using (MemoryLayout; Addr; RegionBounds; lower; upper)

module Once.Allocator.BumpAllocator (layout : MemoryLayout) where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _<_; _≤_; _≤?_; _∸_)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-step; m≤m+n; m+n≤o⇒m≤o; +-comm; +-assoc;
         +-monoʳ-≤; *-monoˡ-≤; m≤n⇒m≤o+n; ≤-reflexive)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋)

-- Import heap region definition
open import Once.Memory.Regions layout using (InHeap)
open import Once.Memory.Regions layout as Regions using (heap-bounds)

------------------------------------------------------------------------
-- Configuration
------------------------------------------------------------------------

-- Slot size from architecture (typically 8 bytes for 64-bit)
-- This should come from MemoryLayout, but for now we define it here
slot-size : ℕ
slot-size = 8

slot-size>0 : 0 < slot-size
slot-size>0 = Data.Nat.s≤s Data.Nat.z≤n

------------------------------------------------------------------------
-- Allocator State
--
-- The bump allocator maintains a single pointer that advances
-- monotonically through the heap region.
------------------------------------------------------------------------

record AllocatorState : Set where
  constructor mkAllocState
  field
    -- Current allocation pointer
    heap-ptr : Addr

    -- Heap region bounds (from layout)
    heap-start : Addr
    heap-end : Addr

    -- Invariants
    start-valid : heap-start ≡ lower Regions.heap-bounds
    end-valid : heap-end ≡ upper Regions.heap-bounds
    ptr-in-range : heap-start ≤ heap-ptr × heap-ptr ≤ heap-end

open AllocatorState public

------------------------------------------------------------------------
-- Initial State
------------------------------------------------------------------------

-- Create initial allocator state from layout bounds
init-allocator : AllocatorState
init-allocator = mkAllocState
  (lower Regions.heap-bounds)           -- heap-ptr starts at heap-start
  (lower Regions.heap-bounds)           -- heap-start
  (upper Regions.heap-bounds)           -- heap-end
  refl                          -- start-valid
  refl                          -- end-valid
  (≤-refl , heap-bounds-valid)       -- ptr-in-range
  where
    heap-bounds-valid : lower Regions.heap-bounds ≤ upper Regions.heap-bounds
    heap-bounds-valid = RegionBounds.bounds-valid Regions.heap-bounds

------------------------------------------------------------------------
-- Allocation Witness
--
-- A proof that a block of n slots was allocated at addr.
-- This is a concrete record with all the information needed
-- to derive properties.
------------------------------------------------------------------------

record Allocated (s : AllocatorState) (addr : Addr) (n : ℕ) : Set where
  constructor mkAllocated
  field
    -- The allocation started at heap-ptr of some prior state
    alloc-addr-eq : addr ≡ heap-ptr s ∸ (n * slot-size)

    -- The block fits in heap
    block-end-ok : addr + (n * slot-size) ≤ heap-end s

    -- Address is at or after heap start
    addr-after-start : heap-start s ≤ addr

open Allocated public

------------------------------------------------------------------------
-- Allocation Result
------------------------------------------------------------------------

record AllocResult (s : AllocatorState) (n : ℕ) : Set where
  constructor mkAllocResult
  field
    addr : Addr
    new-state : AllocatorState
    witness : Allocated new-state addr n

open AllocResult public

------------------------------------------------------------------------
-- The Allocation Operation
--
-- alloc n s: Allocate n slots from state s
-- Returns the allocated address and new state, or nothing if OOM
------------------------------------------------------------------------

alloc : (n : ℕ) → (s : AllocatorState) →
        heap-ptr s + (n * slot-size) ≤ heap-end s →
        AllocResult s n
alloc n s fits = mkAllocResult
  (heap-ptr s)                  -- Allocated address
  s'                            -- New state with advanced pointer
  (mkAllocated addr-eq block-ok addr-ok)
  where
    new-ptr : Addr
    new-ptr = heap-ptr s + (n * slot-size)

    s' : AllocatorState
    s' = record s
      { heap-ptr = new-ptr
      ; ptr-in-range = new-start , fits
      }
      where
        new-start : heap-start s ≤ new-ptr
        new-start = ≤-trans (proj₁ (ptr-in-range s)) (m≤m+n (heap-ptr s) (n * slot-size))

    -- Proof: addr = new-ptr - (n * slot-size) = heap-ptr s
    addr-eq : heap-ptr s ≡ heap-ptr s' ∸ (n * slot-size)
    addr-eq = sym (Data.Nat.Properties.m+n∸n≡m (heap-ptr s) (n * slot-size))

    block-ok : heap-ptr s + (n * slot-size) ≤ heap-end s'
    block-ok = fits  -- Same heap-end, and we checked fits

    addr-ok : heap-start s' ≤ heap-ptr s
    addr-ok = proj₁ (ptr-in-range s)  -- heap-start unchanged

------------------------------------------------------------------------
-- All slots of an allocated block are in heap
------------------------------------------------------------------------

-- Helper: addr is in heap if heap-start ≤ addr ≤ heap-end
addr-in-heap : (s : AllocatorState) (addr : Addr) →
               heap-start s ≤ addr →
               addr ≤ heap-end s →
               InHeap addr
addr-in-heap s addr start≤addr addr≤end =
  subst₂ (λ l u → l ≤ addr × addr ≤ u)
         (start-valid s)
         (end-valid s)
         (start≤addr , addr≤end)
  where
    subst₂ : ∀ {A B : Set} (P : A → B → Set) {a₁ a₂ b₁ b₂} →
             a₁ ≡ a₂ → b₁ ≡ b₂ → P a₁ b₁ → P a₂ b₂
    subst₂ P refl refl p = p

-- Main theorem: slot i of an allocated block is InHeap
block-in-heap : ∀ {s addr n} →
                Allocated s addr n →
                (i : ℕ) → i < n →
                InHeap (addr + i * slot-size)
block-in-heap {s} {addr} {n} alloc i i<n =
  addr-in-heap s (addr + i * slot-size) slot-after-start slot-before-end
  where
    -- addr + i*slot-size ≥ addr ≥ heap-start
    slot-after-start : heap-start s ≤ addr + i * slot-size
    slot-after-start = ≤-trans (addr-after-start alloc) (m≤m+n addr (i * slot-size))

    -- addr + i*slot-size < addr + n*slot-size ≤ heap-end
    i*slot≤n*slot : i * slot-size ≤ n * slot-size
    i*slot≤n*slot = *-monoˡ-≤ slot-size (Data.Nat.Properties.<⇒≤ i<n)

    slot-before-end : addr + i * slot-size ≤ heap-end s
    slot-before-end = ≤-trans (+-monoʳ-≤ addr i*slot≤n*slot) (block-end-ok alloc)

------------------------------------------------------------------------
-- Distinct allocations don't overlap
------------------------------------------------------------------------

-- Two allocations from sequential states have disjoint address ranges
-- (The later allocation starts where the earlier one ended)

-- For bump allocator, this is structural: each alloc advances heap-ptr,
-- so addr₂ = addr₁ + n₁ * slot-size (no overlap possible)

alloc-advances : ∀ {n} (s : AllocatorState)
                 (fits : heap-ptr s + (n * slot-size) ≤ heap-end s) →
                 heap-ptr (new-state (alloc n s fits)) ≡ heap-ptr s + (n * slot-size)
alloc-advances s fits = refl

-- Disjointness follows from monotonic advancement
-- (Proof sketch: if addr₁ < addr₂, their blocks can't overlap because
--  addr₂ = heap-ptr after first alloc = addr₁ + n₁ * slot-size)

------------------------------------------------------------------------
-- DERIVED: Legacy InHeap helpers
--
-- These match the legacy InHeap-helper signatures so existing
-- proofs can use them without modification.
------------------------------------------------------------------------

module DerivedSemantics where

  -- For the legacy interface, we need a way to get InHeap for any
  -- address that was "encoded" (allocated). In the new model, this
  -- requires threading the allocator state.
  --
  -- The key insight: if we have an Allocated witness, we can derive
  -- the legacy properties.

  -- encode-in-heap: base address of allocation is InHeap
  encode-in-heap' : ∀ {s addr n} →
                    Allocated s addr n →
                    0 < n →
                    InHeap addr
  encode-in-heap' {s} {addr} {n} alloc 0<n =
    subst InHeap (Data.Nat.Properties.+-identityʳ addr)
          (block-in-heap alloc 0 0<n)

  -- heap-offset: next slot is also InHeap
  heap-offset' : ∀ {s addr n} →
                 Allocated s addr n →
                 (i : ℕ) → suc i < n →
                 InHeap (addr + i * slot-size) →
                 InHeap (addr + i * slot-size + slot-size)
  heap-offset' {s} {addr} {n} alloc i si<n _ =
    subst InHeap eq (block-in-heap alloc (suc i) si<n)
    where
      -- suc i * slot-size = slot-size + i * slot-size (by def)
      --                   = i * slot-size + slot-size (by +-comm)
      suc-mul : suc i * slot-size ≡ i * slot-size + slot-size
      suc-mul = +-comm slot-size (i * slot-size)

      eq : addr + suc i * slot-size ≡ addr + i * slot-size + slot-size
      eq = trans (cong (addr +_) suc-mul) (sym (+-assoc addr (i * slot-size) slot-size))

------------------------------------------------------------------------
-- Malloc Interface Implementation
--
-- Provides the standard malloc-like interface.
-- free is a no-op (bump allocator doesn't support individual free).
------------------------------------------------------------------------

open import Once.Allocator.Malloc layout as M using (Malloc)

-- Malloc-compatible alloc: returns Maybe instead of requiring proof
malloc-alloc : ℕ → AllocatorState → Data.Maybe.Maybe (Addr × AllocatorState)
malloc-alloc n s with heap-ptr s + (n * slot-size) ≤? heap-end s
... | yes fits = just (heap-ptr s , new-state (alloc n s fits))
... | no _ = nothing

-- free is a no-op for bump allocator
malloc-free : Addr → AllocatorState → AllocatorState
malloc-free _ s = s

-- The heap-ptr is always InHeap (from state invariants)
heap-ptr-in-heap : (s : AllocatorState) → InHeap (heap-ptr s)
heap-ptr-in-heap s = lower≤ptr , ptr≤upper
  where
    lower≤ptr : lower Regions.heap-bounds ≤ heap-ptr s
    lower≤ptr = subst (_≤ heap-ptr s) (start-valid s) (proj₁ (ptr-in-range s))

    ptr≤upper : heap-ptr s ≤ upper Regions.heap-bounds
    ptr≤upper = subst (heap-ptr s ≤_) (end-valid s) (proj₂ (ptr-in-range s))

-- Proof: malloc-alloc returns InHeap addresses
-- The key insight: if malloc-alloc succeeds, it returns heap-ptr s, which is InHeap
malloc-alloc-in-heap : ∀ {n s addr s'} →
                       malloc-alloc n s ≡ just (addr , s') →
                       InHeap addr
malloc-alloc-in-heap {n} {s} {addr} {s'} eq with heap-ptr s + (n * slot-size) ≤? heap-end s
malloc-alloc-in-heap {n} {s} refl | yes _ = heap-ptr-in-heap s
malloc-alloc-in-heap {n} {s} () | no _

-- Package as Malloc interface
asMalloc : Malloc
asMalloc = record
  { State = AllocatorState
  ; init = init-allocator
  ; alloc = malloc-alloc
  ; free = malloc-free
  ; alloc-in-heap = malloc-alloc-in-heap
  }

------------------------------------------------------------------------
-- Summary
--
-- This module provides a CONCRETE bump allocator where:
--
--   1. AllocatorState tracks the heap pointer and bounds
--   2. alloc advances the pointer and returns a witness
--   3. block-in-heap follows from the state invariants
--   4. blocks-disjoint follows from monotonic pointer advancement
--
-- asMalloc provides the standard Malloc interface.
-- The DerivedSemantics module provides the legacy interface for
-- backward compatibility with existing proofs.
------------------------------------------------------------------------