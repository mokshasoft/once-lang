-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Machine.SMPrimitives.Heap
--
-- Helper lemmas for proofs that reason about heap-mode IR producers
-- (the AtDynamic side of the allocator).
--
-- Scope (intentionally narrow):
--   - per-instruction shape lemmas for `instr-alloc-heap`
--   - trace-level wrappers tailored to heap-mode run-X handlers
--   - small re-exports of existing SMPrimitives lemmas that heap-mode
--     proofs care about
--
-- NOT in scope:
--   - new AbstractInstr constructors (those have to live in SMCore so
--     `exec-abstract` and all per-instr predicates stay exhaustive)
--   - changes to existing classifiers (instr-effect, etc.) — adding a
--     branch there would touch every consumer
--
-- Mirror of the IRResultBase/Stack/Heap split in CWF: keep heap-only
-- reasoning in one place so a future InReg allocator can drop alongside.
------------------------------------------------------------------------

module Once.CCC.Machine.SMPrimitives.Heap where

open import Data.Bool using (false)
open import Data.Nat using (ℕ; suc; _<_; _≤_)
open import Data.Nat.Properties using (n≤1+n; <-irrefl)
open import Data.Product using (proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Allocation hiding (AllocMode)

import Once.CCC.Machine.SMPrimitives as SMP

-- Plan 0.14: the abstract-trace instance of the malloc-like allocator
-- interface. This is where heap disjointness for the abstract trace
-- layer lives. Concrete codegen (Target/X86) corresponds to this via
-- simulation; we don't re-derive disjointness.
import Once.Allocator.AbstractInstance as AI
open import Once.Allocator.Interface using (AllocatorInterface)

------------------------------------------------------------------------
-- Heap-mode helpers
------------------------------------------------------------------------

module HeapPrimitives {FS : FrameSemantics} where
  open FrameSemantics FS
  open MemOps {FS}
  open WriteOps {FS}
  open AbstractExec {FS}
  open SMP.InstrPrimitives {FS}

  ----------------------------------------------------------------------
  -- Shape of `exec-abstract (instr-alloc-heap n)`
  ----------------------------------------------------------------------

  -- next-heap-ref bumps by exactly one (n is a codegen hint, not a
  -- semantic multiplier).
  alloc-heap-bumps-next-heap-ref : ∀ (n : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    next-heap-ref (proj₂ (exec-abstract (instr-alloc-heap n) s alloc)) ≡
    suc (next-heap-ref alloc)
  alloc-heap-bumps-next-heap-ref n s alloc = refl

  -- The fresh heap location the instruction returns.
  fresh-heap-loc : (alloc : AllocState {FS}) → ValueLocation FS
  fresh-heap-loc alloc = AtDynamic (heap-loc (mkHeapRef (next-heap-ref alloc)) 0)

  -- Output now holds a pointer to the freshly-allocated cell.
  alloc-heap-output-is-fresh : ∀ (n : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    readReg (regs (proj₁ (exec-abstract (instr-alloc-heap n) s alloc))) Output ≡
    SV-Ptr (fresh-heap-loc alloc)
  alloc-heap-output-is-fresh n s alloc =
    writeReg-same (regs s) Output (SV-Ptr (fresh-heap-loc alloc))

  -- monotone heap-ref bound: alloc.next-heap-ref ≤ alloc'.next-heap-ref.
  alloc-heap-monotone : ∀ (n : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    next-heap-ref alloc ≤ next-heap-ref (proj₂ (exec-abstract (instr-alloc-heap n) s alloc))
  alloc-heap-monotone n s alloc = n≤1+n (next-heap-ref alloc)

  ----------------------------------------------------------------------
  -- Re-exports
  --
  -- Existing SMPrimitives lemmas restated under heap-flavoured names so
  -- heap-mode proofs read top-down.
  ----------------------------------------------------------------------

  alloc-heap-preserves-frame : ∀ (n : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    current-frame (proj₂ (exec-abstract (instr-alloc-heap n) s alloc)) ≡
    current-frame alloc
  alloc-heap-preserves-frame n s alloc =
    SMP.InstrPrimitives.exec-abstract-preserves-frame {FS} (instr-alloc-heap n) s alloc

  alloc-heap-preserves-heapMem : ∀ (n : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    heapMem (proj₁ (exec-abstract (instr-alloc-heap n) s alloc)) ≡ heapMem s
  alloc-heap-preserves-heapMem n s alloc =
    SMP.InstrPrimitives.exec-abstract-preserves-heapMem {FS} (instr-alloc-heap n) s alloc
      SMP.nhw-instr-alloc-heap

  -- `instr-alloc-heap`'s InstrWF falls into the catch-all `⊤` case, so
  -- the witness is `tt`.
  alloc-heap-preserves-halted : ∀ (n : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    halted (proj₁ (exec-abstract (instr-alloc-heap n) s alloc)) ≡ false
  alloc-heap-preserves-halted n s alloc h-eq =
    SMP.TracePrimitives.exec-abstract-preserves-halted-WF {FS} (instr-alloc-heap n)
      s alloc h-eq tt

  ----------------------------------------------------------------------
  -- Disjointness, from the malloc-like allocator interface
  --
  -- The abstract-trace instance (`AI.abstract-allocator`) supplies
  -- `blocks-disjoint`. The forms re-exported here are the
  -- BeforeFrontier-friendly corollaries actually consumed by heap-mode
  -- IR producers.
  ----------------------------------------------------------------------

  -- A freshly-allocated heap location (= the one `instr-alloc-heap`
  -- returns at state `alloc`) is distinct from any heap location whose
  -- ref-id is strictly less than `next-heap-ref alloc`. Derived from
  -- the abstract-allocator interface (`AI.fresh-loc-disjoint`); no
  -- parallel inline derivation.
  fresh-heap-ref-disjoint :
    ∀ (alloc : AllocState {FS}) (hl : HeapLocation) →
    ref-id (heap-ref hl) < next-heap-ref alloc →
    AtDynamic hl ≢ fresh-heap-loc alloc
  fresh-heap-ref-disjoint alloc hl r<next eq =
    AI.fresh-loc-disjoint (next-heap-ref alloc) hl r<next
      (AtDynamic-injective eq)
    where
      AtDynamic-injective : ∀ {h₁ h₂ : HeapLocation} →
                            AtDynamic {FS} h₁ ≡ AtDynamic {FS} h₂ → h₁ ≡ h₂
      AtDynamic-injective refl = refl

  -- A freshly-allocated heap location's i-th cell is distinct from any
  -- heap location whose ref-id is strictly less than next-heap-ref alloc.
  -- Derived from `AI.fresh-cell-disjoint`.
  fresh-heap-cell-disjoint :
    ∀ (alloc : AllocState {FS}) (hl : HeapLocation) (i : ℕ) →
    ref-id (heap-ref hl) < next-heap-ref alloc →
    AtDynamic hl ≢ AtDynamic (offsetHL (heap-loc (mkHeapRef (next-heap-ref alloc)) 0) i)
  fresh-heap-cell-disjoint alloc hl i r<next eq =
    AI.fresh-cell-disjoint (next-heap-ref alloc) hl i r<next
      (AtDynamic-injective eq)
    where
      AtDynamic-injective : ∀ {h₁ h₂ : HeapLocation} →
                            AtDynamic {FS} h₁ ≡ AtDynamic {FS} h₂ → h₁ ≡ h₂
      AtDynamic-injective refl = refl
