------------------------------------------------------------------------
-- Once.Backend.X86v3.FrontierLemma
--
-- BeforeFrontier proof patterns for allocation at frontier.
-- Extracted from Dispatcher.agda for faster compilation.
------------------------------------------------------------------------

module Once.Backend.X86v3.FrontierLemma where

open import Data.Nat using (ℕ; zero; suc; _<_; _+_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; m<m+n; <-trans; n<1+n)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

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

