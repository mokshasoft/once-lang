-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Allocator.Interface
--
-- Abstract malloc-like allocator interface, parameterized over the
-- address type and the slot-stepping operation.
--
-- This module defines what a malloc-like allocator must provide.
-- Concrete implementations (BumpAllocator at the Addr level, SMCore's
-- heap counter at the HeapLocation level) satisfy this interface.
--
-- Plan 0.14: parameterized over the address type so that the same
-- malloc-like interface is consumed at both the abstract trace layer
-- (HeapLocation) and the concrete codegen layer (Addr). One interface,
-- two instances, single source of truth for disjointness. The
-- codegen-level instance comes from BumpAllocator + Target/X86
-- simulation; the abstract-level instance comes from SMCore's
-- `next-heap-ref` counter.
--
-- The interface is:
--   1. Stateful allocation: alloc n → (addr, new-state, witness)
--   2. Block membership: all slots of an allocation are InRegion
--   3. Block disjointness: distinct allocations don't overlap
------------------------------------------------------------------------

module Once.Allocator.Interface where

open import Data.Nat using (ℕ; _<_)
open import Data.Product using (∃; ∃-syntax; proj₁)
open import Relation.Binary.PropositionalEquality using (_≢_)

------------------------------------------------------------------------
-- Allocator Interface
--
-- An allocator provides stateful block allocation with properties.
--
-- Parameters:
--   Address  : the type of allocation addresses (Addr, HeapLocation, ...)
--   slot-at  : compute the i-th slot of a block starting at addr
--   InRegion : predicate stating that an address is in the allocator's
--              region (for the abstract level this can be ⊤; for the
--              concrete level it's InHeap on the heap region).
------------------------------------------------------------------------

record AllocatorInterface
  (Address  : Set)
  (slot-at  : Address → ℕ → Address)
  (InRegion : Address → Set)
  : Set₁ where
  field
    -- Allocator state type
    State : Set

    -- Initial state
    init : State

    -- Allocation witness (proof that addr was allocated with size n)
    Allocated : State → Address → ℕ → Set

    -- Allocation operation
    alloc : (n : ℕ) → (s : State) →
            ∃[ addr ] ∃[ s' ] Allocated s' addr n

    -- Deallocation operation: return a block to the allocator.
    -- (malloc-like interface; Place emits `free` at last-consumer points —
    -- Plan 0.35.) A reusing allocator (Mempool/Slab) makes the block
    -- available again; the trivial bump allocator's `free` is a no-op.
    free : Address → State → State

    -- Property 1: All slots of an allocated block are InRegion.
    block-in-region :
      ∀ {s addr n} →
      Allocated s addr n →
      (i : ℕ) → i < n →
      InRegion (slot-at addr i)

    -- Property 2: Distinct allocations have disjoint address ranges.
    -- NOTE: this is already reuse-sound — it constrains only DISTINCT
    -- addresses, so a freed-then-reallocated block (same address) makes the
    -- `addr₁ ≢ addr₂` hypothesis false and the claim vacuous, exactly right.
    -- Two SIMULTANEOUSLY-live blocks always have distinct addresses (by
    -- `alloc-fresh` below), hence disjoint.
    blocks-disjoint :
      ∀ {s₁ s₂ addr₁ addr₂ n₁ n₂} →
      Allocated s₁ addr₁ n₁ →
      Allocated s₂ addr₂ n₂ →
      addr₁ ≢ addr₂ →
      ∀ (i j : ℕ) → i < n₁ → j < n₂ →
      slot-at addr₁ i ≢ slot-at addr₂ j

    -- Property 3 (liveness-aware freshness): a freshly allocated address
    -- differs from every block live in the PRE-state. Combined with
    -- `blocks-disjoint` this gives "the new block is disjoint from every
    -- currently-live block" — the fact the conservation/simulation layer
    -- (Plan 0.35 M6/M7) consumes. For a monotone allocator the fresh ref
    -- exceeds all prior refs; for a reusing allocator the popped slot is, by
    -- construction, not currently live. Each instance proves it.
    alloc-fresh :
      ∀ {n s addr' n'} →
      Allocated s addr' n' →
      proj₁ (alloc n s) ≢ addr'

------------------------------------------------------------------------
-- Summary
--
-- This interface captures what a malloc-like allocator provides. Two
-- instantiations:
--
--   * Concrete (codegen):   Address = Addr, slot-at addr i = addr + i*slot-size,
--                           InRegion = InHeap. Satisfied by BumpAllocator.
--   * Abstract (SMCore):    Address = HeapLocation, slot-at = offsetHL,
--                           InRegion = ⊤. Satisfied by SMCore's next-heap-ref
--                           counter (see Once.Allocator.AbstractInstance).
--
-- The correspondence between the two instances is established at the
-- simulation layer (Once.Allocator.Target.X86), not by re-proving
-- disjointness — disjointness flows from the abstract layer through
-- simulation faithfulness.
------------------------------------------------------------------------
