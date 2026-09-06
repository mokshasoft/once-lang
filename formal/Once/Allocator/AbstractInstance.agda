-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Allocator.AbstractInstance
--
-- The abstract-trace instantiation of `Once.Allocator.Interface` at the
-- SMCore layer: Address = HeapLocation, slot-at = offsetHL,
-- InRegion = ⊤ (every HeapLocation is heap by construction).
--
-- The State is the `next-heap-ref` counter from SMCore's AllocState
-- — the trivial bump-counter model. This is the malloc-like interface
-- IR-level proofs (PairWF, future run-inl-heap, run-inr-heap)
-- consume for disjointness facts.
--
-- The concrete codegen instance (Once.Allocator.BumpAllocator at Addr
-- level) corresponds to this abstract instance via simulation
-- (Once.Allocator.Target.X86), not by re-deriving disjointness.
------------------------------------------------------------------------

module Once.Allocator.AbstractInstance where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; <-irrefl)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; sym)

open import Once.Memory.HeapAddress
  using (HeapLocation; HeapRef; heap-loc; mkHeapRef; ref-id; heap-ref;
         heap-offset; offsetHL)

open import Once.Allocator.Interface

------------------------------------------------------------------------
-- Address arithmetic for the abstract heap.
------------------------------------------------------------------------

-- slot-at on HeapLocation: walk i offsets from the base.
hl-slot-at : HeapLocation → ℕ → HeapLocation
hl-slot-at hl i = offsetHL hl i

------------------------------------------------------------------------
-- The abstract allocator's state type and witness.
------------------------------------------------------------------------

-- State: just the next ref-id counter.
State : Set
State = ℕ

-- Initial state: no allocations yet.
initial : State
initial = 0

-- Allocated witness: addr is the base of a block whose ref was bumped
-- to (or below) the current state. n is opaque at the abstract level
-- (offsets walked via hl-slot-at).
record Allocated (s : State) (addr : HeapLocation) (n : ℕ) : Set where
  constructor mkAllocated
  field
    ref         : ℕ
    addr-eq     : addr ≡ heap-loc (mkHeapRef ref) 0
    ref<state   : ref < s

open Allocated public

------------------------------------------------------------------------
-- The allocation operation: bump the counter, return heap-loc.
------------------------------------------------------------------------

alloc-impl : (n : ℕ) → (s : State) → ∃[ addr ] ∃[ s' ] Allocated s' addr n
alloc-impl n s = heap-loc (mkHeapRef s) 0 , suc s ,
  mkAllocated s refl (s≤s ≤-refl)

------------------------------------------------------------------------
-- Property proofs.
------------------------------------------------------------------------

-- All slots of an allocated block are "in region" — trivially, since
-- InRegion ≡ ⊤ at the abstract layer.
block-in-region-impl :
  ∀ {s addr n} → Allocated s addr n → (i : ℕ) → i < n →
  ⊤
block-in-region-impl _ _ _ = tt

-- Distinct allocations have distinct heap-refs and therefore distinct
-- slot addresses regardless of offsets.
blocks-disjoint-impl :
  ∀ {s₁ s₂ addr₁ addr₂ n₁ n₂} →
  Allocated s₁ addr₁ n₁ →
  Allocated s₂ addr₂ n₂ →
  addr₁ ≢ addr₂ →
  ∀ (i j : ℕ) → i < n₁ → j < n₂ →
  hl-slot-at addr₁ i ≢ hl-slot-at addr₂ j
blocks-disjoint-impl {addr₁ = .(heap-loc (mkHeapRef _) 0)} {addr₂ = .(heap-loc (mkHeapRef _) 0)}
  (mkAllocated r₁ refl _) (mkAllocated r₂ refl _) addr-≢ i j _ _ slot-≡ =
  -- slot-≡ : offsetHL (heap-loc (mkHeapRef r₁) 0) i ≡ offsetHL (heap-loc (mkHeapRef r₂) 0) j
  -- both sides = heap-loc (mkHeapRef rₖ) (i + 0) and ... (j + 0)
  -- heap-ref of both must agree → mkHeapRef r₁ ≡ mkHeapRef r₂ → r₁ ≡ r₂.
  -- Then addr₁ ≡ addr₂ — contradiction with addr-≢.
  addr-≢ (cong (λ r → heap-loc r 0) (cong heap-ref slot-≡))

------------------------------------------------------------------------
-- Deallocation (Plan 0.35 M1).
--
-- The bump counter cannot reclaim, so `free` is a no-op — the abstract
-- heap leaks. This honestly satisfies the interface today; Plan 0.35 M7
-- upgrades it to a reusing free-list once net-zero conservation is proved
-- (that change reshapes `State` from a counter and is intentionally NOT
-- done here, as it cascades into SMCore's AllocState).
------------------------------------------------------------------------

free-impl : HeapLocation → State → State
free-impl _ s = s

------------------------------------------------------------------------
-- Liveness-aware freshness (Plan 0.35 M1).
--
-- The address `alloc-impl` hands out at state s — `heap-loc (mkHeapRef s) 0`
-- — differs from every block live in the pre-state (its ref-id < s). Since
-- the counter never reuses, "live" = "allocated" and the fresh ref = s
-- exceeds all prior refs. Discharges the interface's `alloc-fresh`; no
-- postulate.
------------------------------------------------------------------------

alloc-fresh-impl :
  ∀ {n s addr' n'} →
  Allocated s addr' n' →
  proj₁ (alloc-impl n s) ≢ addr'
alloc-fresh-impl (mkAllocated ref' refl ref'<s) eq =
  <-irrefl (sym (cong (λ h → ref-id (heap-ref h)) eq)) ref'<s

------------------------------------------------------------------------
-- Package as an AllocatorInterface instance.
------------------------------------------------------------------------

abstract-allocator :
  AllocatorInterface HeapLocation hl-slot-at (λ _ → ⊤)
abstract-allocator = record
  { State           = State
  ; init            = initial
  ; Allocated       = Allocated
  ; alloc           = alloc-impl
  ; free            = free-impl
  ; block-in-region = block-in-region-impl
  ; blocks-disjoint = blocks-disjoint-impl
  ; alloc-fresh     = λ {n} {s} {addr'} {n'} → alloc-fresh-impl {n} {s} {addr'} {n'}
  }

------------------------------------------------------------------------
-- Derived corollaries consumed by IR-level proofs.
--
-- The interface's `blocks-disjoint` is the load-bearing fact. The
-- following corollaries are convenience forms in the granularity IR
-- producers actually consume (individual locations, not block witnesses).
------------------------------------------------------------------------

-- The fresh allocation at state `s` (i.e. the address `alloc-impl _ s`
-- hands out — `heap-loc (mkHeapRef s) 0`) is distinct from any heap
-- location whose ref-id is strictly less than `s`, regardless of its
-- offset. This follows directly from the bump invariant: `<-irrefl`
-- on ref-ids.
fresh-loc-disjoint :
  ∀ (s : State) (hl : HeapLocation) →
  ref-id (heap-ref hl) < s →
  hl ≢ heap-loc (mkHeapRef s) 0
fresh-loc-disjoint s hl r<s eq =
  let r-eq : ref-id (heap-ref hl) ≡ s
      r-eq = cong (λ h → ref-id (heap-ref h)) eq
  in <-irrefl r-eq r<s

-- The i-th cell of the fresh allocation (any offset) is distinct from
-- any heap location whose ref-id is strictly less than `s`. The fresh
-- ref appears in every cell of the fresh block; the old ref does not.
fresh-cell-disjoint :
  ∀ (s : State) (hl : HeapLocation) (i : ℕ) →
  ref-id (heap-ref hl) < s →
  hl ≢ hl-slot-at (heap-loc (mkHeapRef s) 0) i
fresh-cell-disjoint s hl i r<s eq =
  let r-eq : ref-id (heap-ref hl) ≡ s
      r-eq = cong (λ h → ref-id (heap-ref h)) eq
  in <-irrefl r-eq r<s
