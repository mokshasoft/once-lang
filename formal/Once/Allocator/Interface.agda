------------------------------------------------------------------------
-- Once.Allocator.Interface
--
-- Abstract allocator interface (malloc-like).
--
-- This module defines what an allocator must provide. Concrete
-- implementations (like BumpAllocator) satisfy this interface.
--
-- The interface is:
--   1. Stateful allocation: alloc n → (addr, new-state)
--   2. Block membership: all slots of an allocation are InHeap
--   3. Block disjointness: distinct allocations don't overlap
--
-- The legacy CCC.AllocatorSemantics (encode-in-heap, heap-offset) can
-- be derived from this interface.
------------------------------------------------------------------------

open import Once.CCC.MemoryLayoutSemantics
  using (MemoryLayout; Addr)

module Once.Allocator.Interface (layout : MemoryLayout) where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _<_; _≤_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

-- Import heap region definition
open import Once.CCC.Regions layout using (InHeap)

------------------------------------------------------------------------
-- Allocator Interface
--
-- An allocator provides stateful block allocation with properties.
------------------------------------------------------------------------

record AllocatorInterface : Set₁ where
  field
    -- Allocator state type
    State : Set

    -- Slot size (architecture-dependent)
    slot-size : ℕ
    slot-size>0 : 0 < slot-size

    -- Initial state
    init : State

    -- Allocation witness (proof that addr was allocated with size n)
    Allocated : State → Addr → ℕ → Set

    -- Allocation operation
    alloc : (n : ℕ) → (s : State) →
            ∃[ addr ] ∃[ s' ] Allocated s' addr n

    -- Property 1: All slots of an allocated block are InHeap
    block-in-heap : ∀ {s addr n} →
                    Allocated s addr n →
                    (i : ℕ) → i < n →
                    InHeap (addr + i * slot-size)

    -- Property 2: Distinct allocations have disjoint address ranges
    blocks-disjoint : ∀ {s₁ s₂ addr₁ addr₂ n₁ n₂} →
                      Allocated s₁ addr₁ n₁ →
                      Allocated s₂ addr₂ n₂ →
                      addr₁ ≢ addr₂ →
                      ∀ (i j : ℕ) → i < n₁ → j < n₂ →
                      (addr₁ + i * slot-size) ≢ (addr₂ + j * slot-size)

------------------------------------------------------------------------
-- Derived Properties
--
-- These are the properties needed by the legacy AllocatorSemantics.
-- They are PROVEN from the interface, not postulated.
------------------------------------------------------------------------

module Derived (AI : AllocatorInterface) where
  open AllocatorInterface AI

  open import Data.Nat.Properties using (+-identityʳ; +-assoc; +-comm)
  open import Relation.Binary.PropositionalEquality using (subst; cong; trans; sym)

  -- Base address of an allocation is InHeap
  alloc-base-in-heap : ∀ {s addr n} →
                       Allocated s addr n →
                       0 < n →
                       InHeap addr
  alloc-base-in-heap {_} {addr} alloc 0<n =
    subst InHeap (+-identityʳ addr) (block-in-heap alloc 0 0<n)

  -- Next slot after a valid slot is also InHeap (if within block)
  alloc-next-in-heap : ∀ {s addr n} →
                       Allocated s addr n →
                       (i : ℕ) → suc i < n →
                       InHeap (addr + i * slot-size + slot-size)
  alloc-next-in-heap {_} {addr} alloc i si<n =
    subst InHeap eq (block-in-heap alloc (suc i) si<n)
    where
      suc-mul : suc i * slot-size ≡ i * slot-size + slot-size
      suc-mul = +-comm slot-size (i * slot-size)

      eq : addr + suc i * slot-size ≡ addr + i * slot-size + slot-size
      eq = trans (cong (addr +_) suc-mul) (sym (+-assoc addr (i * slot-size) slot-size))

------------------------------------------------------------------------
-- Summary
--
-- This interface captures what a malloc-like allocator provides:
--
--   State          : Allocator state (e.g., bump pointer + bounds)
--   Allocated s a n: Witness that n slots were allocated at a
--   alloc          : Allocate n slots, get address + witness
--   block-in-heap  : All slots of an allocation are in heap
--   blocks-disjoint: Different allocations don't overlap
--
-- Concrete implementations (BumpAllocator) satisfy this interface.
-- Legacy code can use the Derived module for encode-in-heap style.
------------------------------------------------------------------------
