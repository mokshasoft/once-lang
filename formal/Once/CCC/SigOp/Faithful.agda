-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.SigOp.Faithful
--
-- The value-flow obligation for SigOp implementations.
--
-- ## What this is
--
-- `RelaxedContract` (sibling module) only enforces CCC-discipline:
-- the trace doesn't mess with the stack, registers (other than
-- Output), or frame. That's a necessary property — but not a
-- sufficient one. As `Once.Arith.SigOp.RelaxedPOC` demonstrates,
-- the discipline-only contract admits a copy-trace as a valid
-- implementation of *any* SigOp, including `add` (which is not a
-- copy).
--
-- This module adds the missing piece: a value-flow obligation tying
-- `Output` (post-trace) to `semM si` of the input. With this in
-- place, a wrong codegen — one that doesn't actually compute what
-- `semM si` says — fails to typecheck.
--
-- ## Why parameterize by `Repr`
--
-- The CCC abstract machine only tracks *locations*: `ValueLocation
-- = AtStack Frame ℕ | AtDynamic HeapLoc`. Locations point to other
-- locations via `stackMem`/`heapMem`. There is no "the integer 42
-- is at this location" — the abstract machine has no values, only
-- pointer chains.
--
-- The bridge between CCC's pointer-chain world and `semM`'s
-- math-level value world (`M.⟦ A ⟧`) is per-arch. On x86-64, an
-- integer value in a register has a particular bit-pattern; on
-- riscv64, possibly different. The CCC layer cannot define this
-- bridge — but it CAN abstract over it.
--
-- We make the contract record take a `Repr` parameter:
--
--   Repr : ∀ X → ⟦X⟧ → LocState → AllocState → ValueLocation → Set
--
-- ...meaning "this location, in this state, faithfully represents
-- this math-level value". Per-arch CompileCorrect supplies its own
-- `Repr` when discharging the contract; the CCC layer just states
-- the obligation.
--
-- ## Linkage to codegen
--
-- A SigOp implementation is now a **bundle**: trace + RelaxedContract
-- proof + Faithful proof. The CCC layer's `sigop-codegen-faithful`
-- (the per-arch postulate from Plan 0.10 Phase A) is derived from
-- this bundle. If a per-name proof of `Faithful` can't be built,
-- `sigop-codegen-faithful` for that name remains undischarged → the
-- compiler-correctness theorem doesn't hold for that SigOp →
-- compilation may proceed but verification fails.
--
-- This is the structural linkage the user asked for: codegen change
-- → corresponding `Faithful` proof breaks → the per-arch
-- `sigop-codegen-faithful` derivation breaks → compile-correct
-- breaks. The bug surfaces at typecheck time.
--
-- Plan 0.10 Phase A — SigOp gap closure, value-flow obligation.
------------------------------------------------------------------------

module Once.CCC.SigOp.Faithful where

open import Data.Bool using (Bool; false)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Type using (Type)
open import Once.Semantics.Machine using (⟦_⟧)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.SigOp.Info using (SigOpInfo; semM)
open import Once.CCC.Machine.SMCore
  using (LocState; AbstractTrace;
         AbstractReg; Input1; Output;
         ValueLocation;
         halted; regs; readReg;
         module AbstractExec)
open import Once.CCC.Machine.Allocation using (AllocState)

------------------------------------------------------------------------
-- The representation predicate
------------------------------------------------------------------------

-- | A representation predicate at the abstract-machine layer.
-- `Repr X x s alloc loc` ≅ "the location `loc`, in state `(s, alloc)`,
-- represents the math-level value `x : ⟦ X ⟧`".
--
-- Per-arch CompileCorrect instantiates this with a concrete
-- definition (e.g., for x86, by tracing the location chain in
-- stackMem/heapMem to a leaf and decoding the bits there).
ReprPred : FrameSemantics → Set₁
ReprPred FS =
  ∀ (X : Type) → ⟦ X ⟧ → LocState FS → AllocState {FS} → ValueLocation FS → Set

------------------------------------------------------------------------
-- The value-flow obligation
------------------------------------------------------------------------

module FaithfulDef {FS : FrameSemantics} where
  open AbstractExec {FS} using (exec-trace)

  ----------------------------------------------------------------------
  -- The contract: post-trace Output represents `semM si` of the
  -- pre-trace Input1.
  --
  -- Crucially, this requires the implementor to *exhibit*
  -- evidence that the trace's effect, when interpreted via Repr,
  -- matches `semM si`. For a copy-trace on `add`, this requires
  -- showing `add-semM x = x` — which is unprovable for the opaque
  -- `add-semM` postulate. The proof FAILS.
  ----------------------------------------------------------------------

  record Faithful (Repr : ReprPred FS) {A B}
                  (si : SigOpInfo A B) (trace : AbstractTrace) : Set where
    field
      output-faithful : ∀ (s : LocState FS) (alloc : AllocState {FS})
                         (x : ⟦ A ⟧) →
        halted s ≡ false →
        Repr A x s alloc (readReg (regs s) Input1) →
        Repr B (semM si x)
               (proj₁ (exec-trace trace s alloc))
               (proj₂ (exec-trace trace s alloc))
               (readReg (regs (proj₁ (exec-trace trace s alloc))) Output)

  open Faithful public
