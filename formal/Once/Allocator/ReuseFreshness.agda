-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Allocator.ReuseFreshness
--
-- Plan 0.35 — load-bearing POC for the "reuse is sound" claim.
--
-- The plan rests on: a freed-then-reallocated block reuses an address in
-- LOCKSTEP across the abstract and concrete allocators, and the interface's
-- `alloc-fresh` (a fresh allocation differs from every block live in the
-- pre-state) still holds across reuse — so no live-set / enc-hl-injective-
-- on-live machinery is needed.
--
-- This module discharges exactly the REUSE case of `alloc-fresh`, in
-- isolation, for a free-list allocator that hands out a previously-freed
-- ref. It needs NO numeric frontier invariant and NO no-duplicate-freed
-- invariant: `alloc-fresh` quantifies over blocks live in the PRE-state,
-- whose refs are (by definition of "live = not currently freed) absent from
-- the pre-state free-list — which still contains the ref being popped. So
-- the popped ref differs from every pre-live ref.
--
-- (The full reusing AllocatorInterface instance — with the free-list state,
-- idempotent free, and the new block's own liveness witness — is the M7
-- upgrade; its invariant design is deliberately deferred. This POC confirms
-- the central claim is provable before that work.)
------------------------------------------------------------------------

module Once.Allocator.ReuseFreshness where

open import Data.Nat using (ℕ)
open import Data.List using (List; _∷_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong)

open import Once.Memory.HeapAddress
  using (HeapLocation; heap-loc; mkHeapRef; ref-id; heap-ref)

------------------------------------------------------------------------
-- The reuse case of `alloc-fresh`.
--
-- `r`        : the ref-id popped off the free-list by this allocation.
-- `rest`     : the remaining free-list (irrelevant to the proof).
-- `addr'`    : any block live in the PRE-state.
-- `live`     : its ref is NOT in the pre-state free-list `r ∷ rest`
--              (i.e. addr' is not a freed block — it is genuinely live).
--
-- Conclusion: the reallocated address `heap-loc (mkHeapRef r) 0` differs
-- from `addr'`. Hence the new block is disjoint from every live block
-- (via the interface's `blocks-disjoint`), exactly as for a fresh bump.
------------------------------------------------------------------------

reuse-alloc-fresh :
  ∀ (r : ℕ) (rest : List ℕ) (addr' : HeapLocation) →
  ref-id (heap-ref addr') ∉ (r ∷ rest) →
  heap-loc (mkHeapRef r) 0 ≢ addr'
reuse-alloc-fresh r rest addr' ref'∉ eq = ref'∉ (here (sym r≡ref'))
  where
    -- eq : heap-loc (mkHeapRef r) 0 ≡ addr'
    -- project the ref-id through both sides: r ≡ ref-id (heap-ref addr')
    r≡ref' : r ≡ ref-id (heap-ref addr')
    r≡ref' = cong (λ h → ref-id (heap-ref h)) eq
