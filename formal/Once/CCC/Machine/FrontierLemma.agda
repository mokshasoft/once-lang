-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Target.X86-64.FrontierLemma
--
-- BeforeFrontier proof patterns for allocation at frontier.
-- Extracted from Dispatcher.agda for faster compilation.
------------------------------------------------------------------------

module Once.CCC.Machine.FrontierLemma where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; s≤s; z≤n) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (≤-refl; m<m+n; <-trans; n<1+n)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.SMPrimitives

------------------------------------------------------------------------
-- Frontier lemmas parameterized by frame semantics
------------------------------------------------------------------------

module FrontierLemmas {FS : FrameSemantics} where
  open FrameSemantics FS
  open import Once.CCC.Machine.Allocation

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

  -- n < n +ℕ suc k (for any k, k ≥ 0)
  private
    n<n+suc-k : ∀ (n k : ℕ) → n < n +ℕ suc k
    n<n+suc-k n k = m<m+n n (s≤s z≤n)

  -- The location AtStack cf (next-slot alloc) is BeforeFrontier
  -- after allocating k slots (where k > 0)
  at-frontier-becomes-before : ∀ (alloc : AllocState {FS}) (k : ℕ) →
    (k>0 : 0 < k) →
    let alloc' = record alloc { next-slot = next-slot alloc +ℕ k }
    in BeforeFrontier alloc' (AtStack (current-frame alloc) (next-slot alloc))
  at-frontier-becomes-before alloc (suc k) (s≤s z≤n) =
    stack-before refl (n<n+suc-k (next-slot alloc) k)

  -- Specialized versions for common allocation sizes

  -- pair-slots = 2
  at-frontier-before-pair : ∀ (alloc : AllocState {FS}) →
    let alloc' = record alloc { next-slot = next-slot alloc +ℕ 2 }
    in BeforeFrontier alloc' (AtStack (current-frame alloc) (next-slot alloc))
  at-frontier-before-pair alloc =
    at-frontier-becomes-before alloc 2 (s≤s z≤n)

  -- closure-slots = 2
  at-frontier-before-closure : ∀ (alloc : AllocState {FS}) →
    let alloc' = record alloc { next-slot = next-slot alloc +ℕ 2 }
    in BeforeFrontier alloc' (AtStack (current-frame alloc) (next-slot alloc))
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
  frontier-same-heap a1 a2 frame-eq slot-eq heap-eq (AtStack f k) (stack-before f-eq k<slot) =
    stack-before (trans f-eq frame-eq) (subst (k <_) slot-eq k<slot)
  frontier-same-heap a1 a2 frame-eq slot-eq heap-eq (AtStack f k) (stack-ancestor cf≺f src) =
    stack-ancestor (subst (_≺ f) frame-eq cf≺f) src  -- Transfer ordering via frame equality, preserve provenance
  frontier-same-heap a1 a2 frame-eq slot-eq heap-eq (AtDynamic hl) (heap-before ref<heap) =
    heap-before (subst (ref-id (heap-ref hl) <_) heap-eq ref<heap)
