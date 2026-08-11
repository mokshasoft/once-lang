-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Target.RiscV64.RuntimeContract
--
-- The contract between CCC and the higher-level compiler/linker.
--
-- This module makes explicit what the runtime environment must provide
-- for the CCC proofs to hold. The higher compiler satisfies this contract.
--
-- KEY DESIGN PRINCIPLES:
--   1. State invariants, not universal quantifications
--   2. Dynamic capacity (each closure knows its own requirement)
--   3. Region membership derived from bounds + layout
------------------------------------------------------------------------

module Once.CCC.Target.RiscV64.RuntimeContract where

open import Data.Nat using (ℕ; _<_; _≤_) renaming (_+_ to _+ℕ_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Induction.WellFounded using (Acc)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.Memory.MemoryLayoutSemantics as MLS using (MemoryLayout; upper)
open import Once.CCC.Machine.SMCore using (ValueLocation; AtStack; AtDynamic; HeapLocation; HeapRef)

------------------------------------------------------------------------
-- Frame Slots In Stack: predicate that all slots are in stack region
------------------------------------------------------------------------

module FrameRegion (layout : MemoryLayout) where
  open import Once.Memory.Regions layout public
    using (InStack; InHeap; stack-heap-addr-disjoint)

  -- All slots 0..capacity-1 at frame base are in stack region
  FrameSlotsInStack : (frame-base : ℕ) (capacity : ℕ) → Set
  FrameSlotsInStack base cap = ∀ k → k < cap → InStack (base +ℕ k)

  -- Valid heap base map: all refs map to heap region
  HeapBaseValid : (HeapRef → ℕ) → Set
  HeapBaseValid hb = ∀ hr → InHeap (hb hr)

------------------------------------------------------------------------
-- RuntimeContract: What the higher compiler must provide
------------------------------------------------------------------------

record RuntimeContract (FS : FrameSemantics) : Set₁ where
  open FrameSemantics FS

  field
    -- Termination (for well-founded recursion on IR)
    program-bound : ℕ
    acc-pb : Acc _<_ program-bound

    -- Memory Layout (linker establishes region bounds and disjointness)
    layout : MemoryLayout

  -- Open region definitions with our layout
  open FrameRegion layout public

  stack-upper : ℕ
  stack-upper = upper (MLS.MemoryLayout.stack-bounds layout)

  field
    -- Frame Region Invariant (linker guarantee)
    alloc-frame-valid : (base : ℕ) (capacity : ℕ) →
      InStack base →
      base +ℕ capacity ≤ stack-upper →
      FrameSlotsInStack base capacity

    -- Heap Region Invariant (allocator guarantee)
    heap-loc-in-heap : (hb : HeapRef → ℕ) →
      HeapBaseValid hb →
      ∀ (hl : HeapLocation) (block-size : ℕ) →
      HeapLocation.heap-offset hl < block-size →
      InHeap (hb (HeapLocation.heap-ref hl) +ℕ HeapLocation.heap-offset hl)

  -- DERIVED: Cross-domain disjointness
  stack≢heap : (frame-base capacity : ℕ) (k : ℕ) →
    (hb : HeapRef → ℕ) (hl : HeapLocation) (block-size : ℕ) →
    FrameSlotsInStack frame-base capacity →
    k < capacity →
    HeapBaseValid hb →
    HeapLocation.heap-offset hl < block-size →
    (frame-base +ℕ k) ≢ (hb (HeapLocation.heap-ref hl) +ℕ HeapLocation.heap-offset hl)
  stack≢heap base cap k hb hl bsize frame-valid k<cap hb-valid off<bsize =
    stack-heap-addr-disjoint
      (base +ℕ k)
      (hb (HeapLocation.heap-ref hl) +ℕ HeapLocation.heap-offset hl)
      (frame-valid k k<cap)
      (heap-loc-in-heap hb hb-valid hl bsize off<bsize)

------------------------------------------------------------------------
-- FrameOps: Frame management operations (calling convention)
------------------------------------------------------------------------

record FrameOps (FS : FrameSemantics) : Set₁ where
  open FrameSemantics FS

  field
    get-child-frame : Frame → Frame
    child-frame-ordered : ∀ parent → get-child-frame parent ≺ parent
    child-frame-adjacent : ∀ parent f →
      get-child-frame parent ≺ f → f ≺ parent → ⊥