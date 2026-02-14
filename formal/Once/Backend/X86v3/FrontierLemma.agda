------------------------------------------------------------------------
-- Once.Backend.X86v3.FrontierLemma
--
-- BeforeFrontier proof patterns for allocation at frontier.
-- Extracted from Dispatcher.agda for faster compilation.
------------------------------------------------------------------------

module Once.Backend.X86v3.FrontierLemma where

open import Data.Nat using (ℕ; zero; suc; _<_; _+_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; m<m+n; <-trans; n<1+n)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst)

open import Once.Backend.Common.FrameSemantics using (FrameSemantics)
open import Once.Backend.Common.SlotMachine

------------------------------------------------------------------------
-- Frontier lemmas parameterized by frame semantics
------------------------------------------------------------------------

module FrontierLemmas {FS : FrameSemantics} where
  open FrameSemantics FS
  open import Once.Backend.X86v3.Allocation

  open FrontierInvariant {FS}

  ------------------------------------------------------------------------
  -- Location at slot n is before frontier after allocating k > 0 slots
  --
  -- Pattern: when we allocate k slots starting at next-slot alloc,
  -- the first allocated slot (at index next-slot alloc) is still
  -- "before frontier" in the new allocator where next-slot = old + k.
  --
  -- Used in: pair-before, closure-before, pair-input-before
  ------------------------------------------------------------------------

  -- n < n + suc k (for any k, k ≥ 0)
  private
    n<n+suc-k : ∀ (n k : ℕ) → n < n + suc k
    n<n+suc-k n k = m<m+n n (s≤s z≤n)

  -- The location OnStack cf (next-slot alloc) is BeforeFrontier
  -- after allocating k slots (where k > 0)
  at-frontier-becomes-before : ∀ (alloc : AllocState {FS}) (k : ℕ) →
    (k>0 : 0 < k) →
    ∀ (slots-avail : next-slot alloc + k ≤ frame-capacity alloc) →
    let alloc' = record alloc { next-slot = next-slot alloc + k ; slots-available = slots-avail }
    in BeforeFrontier alloc' (OnStack (current-frame alloc) (next-slot alloc))
  at-frontier-becomes-before alloc (suc k) (s≤s z≤n) slots-avail =
    stack-before refl (n<n+suc-k (next-slot alloc) k)

  -- Specialized versions for common allocation sizes

  -- pair-slots = 2
  at-frontier-before-pair : ∀ (alloc : AllocState {FS}) →
    ∀ (slots-avail : next-slot alloc + 2 ≤ frame-capacity alloc) →
    let alloc' = record alloc { next-slot = next-slot alloc + 2 ; slots-available = slots-avail }
    in BeforeFrontier alloc' (OnStack (current-frame alloc) (next-slot alloc))
  at-frontier-before-pair alloc slots-avail =
    at-frontier-becomes-before alloc 2 (s≤s z≤n) slots-avail

  -- closure-slots = 2
  at-frontier-before-closure : ∀ (alloc : AllocState {FS}) →
    ∀ (slots-avail : next-slot alloc + 2 ≤ frame-capacity alloc) →
    let alloc' = record alloc { next-slot = next-slot alloc + 2 ; slots-available = slots-avail }
    in BeforeFrontier alloc' (OnStack (current-frame alloc) (next-slot alloc))
  at-frontier-before-closure = at-frontier-before-pair

  ------------------------------------------------------------------------
  -- frontier-same-heap: BeforeFrontier transfer between equivalent allocs
  --
  -- When two AllocState records have the same current-frame, next-slot,
  -- and next-heap-ref, BeforeFrontier transfers between them.
  --
  -- In practice, next-heap-ref is always the same because all our operations
  -- only modify stack slots, not heap references.
  ------------------------------------------------------------------------
  frontier-same-heap : ∀ a1 a2 →
    current-frame a1 ≡ current-frame a2 →
    next-slot a1 ≡ next-slot a2 →
    next-heap-ref a1 ≡ next-heap-ref a2 →
    ∀ loc → BeforeFrontier a1 loc → BeforeFrontier a2 loc
  frontier-same-heap a1 a2 frame-eq slot-eq heap-eq (OnStack f k) (stack-before f-eq k<slot) =
    stack-before (trans f-eq frame-eq) (subst (k <_) slot-eq k<slot)
  frontier-same-heap a1 a2 frame-eq slot-eq heap-eq (OnStack f k) (stack-other-frame f≢cf) =
    stack-other-frame (λ f≡cf2 → f≢cf (trans f≡cf2 (sym frame-eq)))
  frontier-same-heap a1 a2 frame-eq slot-eq heap-eq (OnHeap r o) (heap-before ref<heap) =
    heap-before (subst (ref-id r <_) heap-eq ref<heap)

