-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Machine.IR.PairWF2.Setup
--
-- Plan 0.18 — driver-glue extraction.
--
-- Bundles the four Validity-derived proofs that PairWF2.run-pair needs
-- to supply to its rec-wf f call (input-valid-wf-after-setup,
-- input-before-at-f-start, not-halted-after-setup, rdi-eq-after-setup).
--
-- The bundle's TYPE is expressed via Finalize.FinalizeImpl helpers
-- (pair-s-after-setup, pair-alloc-after-pair-slots) — pure functions
-- that reduce to the same exec-trace expressions as VImpl.Validity's
-- members. Bundle's IMPLEMENTATION instantiates V0 internally; that
-- cost stays in this file (cached after first build) instead of
-- leaking into PairWF2.agda's elaboration scope.
------------------------------------------------------------------------

module Once.CCC.Machine.IR.PairWF2.Setup where

open import Data.Nat using (ℕ; suc) renaming (_+_ to _+ℕ_)
open import Data.Bool using (false)
open import Data.Product using (proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore hiding (AllocMode; Stack; Heap)
open import Once.Semantics.Machine using (⟦_⟧)
open import Once.CCC.IR
open import Once.CCC.IR.Stack
open import Once.CCC.Machine.Allocation hiding (AllocMode)
open import Once.CCC.Machine.ClosureWellFormed

import Once.CCC.Machine.SMPrimitives as SMP
import Once.CCC.Machine.IR.PairWF2.Validity as PairValidity

module SetupImpl {FS : FrameSemantics} (program-bound : ℕ) where
  open FrameSemantics FS
  open FrontierInvariant {FS}
  open AbstractExec {FS}
  open SMP.TracePrimitives {FS}

  module VImpl = PairValidity.ValidityImpl {FS} program-bound

  open ClosureWellFormedDef {FS} program-bound using (ValidAtWF)

  -- Inline helpers — must match Finalize.FinalizeImpl.pair-* exactly
  -- (definitional equality). Duplicated to avoid importing the heavy
  -- Finalize compilation unit just for two trivial functions.
  pair-s-after-setup : (s : LocState FS) (alloc : AllocState {FS}) → LocState FS
  pair-s-after-setup s alloc = proj₁ (exec-trace
    (mov-to-output ∷ store-at-slot (next-slot alloc) ∷
     instr-alloc-stack (suc pair-slots) ∷ []) s alloc)

  pair-alloc-after-pair-slots : (alloc : AllocState {FS}) → AllocState {FS}
  pair-alloc-after-pair-slots alloc =
    record alloc { next-slot = suc (suc (suc (next-slot alloc))) }

  record PairSetupBundle
    {A B C : Type}
    (mIn : AllocMode) (f : IR A B) (g : IR A C) (x : ⟦ A ⟧)
    (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) : Set where
    field
      input-valid-wf-after-setup :
        ValidAtWF mIn (pair-alloc-after-pair-slots alloc) x input-loc
                      (pair-s-after-setup s alloc)
      input-before-at-f-start :
        BeforeFrontier (pair-alloc-after-pair-slots alloc) input-loc
      not-halted-after-setup :
        halted (pair-s-after-setup s alloc) ≡ false
      rdi-eq-after-setup :
        readReg (regs (pair-s-after-setup s alloc)) Input1 ≡ SV-Ptr input-loc

  mk-pair-setup-bundle :
    ∀ {A B C} (mIn : AllocMode) (f : IR A B) (g : IR A C) (x : ⟦ A ⟧)
      (input-loc : ValueLocation FS)
      (s : LocState FS) (alloc : AllocState {FS})
      (not-halted : halted s ≡ false)
      (rdi-eq : readReg (regs s) Input1 ≡ SV-Ptr input-loc)
      (input-valid-wf : ValidAtWF mIn alloc x input-loc s)
      (input-before : BeforeFrontier alloc input-loc) →
      PairSetupBundle mIn f g x input-loc s alloc
  mk-pair-setup-bundle mIn f g x input-loc s alloc not-halted rdi-eq
                       input-valid-wf input-before =
    record
      { input-valid-wf-after-setup = V0.input-valid-wf-after-setup
      ; input-before-at-f-start    = V0.input-before-at-f-start
      ; not-halted-after-setup     = V0.not-halted-after-setup
      ; rdi-eq-after-setup         = V0.rdi-eq-after-setup
      }
    where
      module V0 = VImpl.Validity mIn f g x input-loc s alloc not-halted rdi-eq
                                  input-valid-wf input-before
