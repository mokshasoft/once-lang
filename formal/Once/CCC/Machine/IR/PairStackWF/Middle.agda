-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Machine.IR.PairStackWF.Middle
--
-- Plan 0.18 — driver-glue extraction (companion of Setup.agda).
--
-- Bundles the four Validity.L2-derived proofs that PairStackWF.run-pair
-- needs to supply to its rec-wf g call (valid-at-s-after-middle,
-- input-before-at-reclaim-f, not-halted-after-middle,
-- rdi-eq-at-s-after-middle).
--
-- The bundle's TYPE is expressed via inlined Finalize helpers
-- (pair-s-after-setup / pair-s-after-middle / pair-alloc-after-pair-slots
-- / pair-alloc-after-f-reclaim), duplicated here to avoid the cost of
-- importing Finalize. Bundle's IMPLEMENTATION instantiates V0 + V2
-- internally; that cost is paid once in this file (cached).
------------------------------------------------------------------------

module Once.CCC.Machine.IR.PairStackWF.Middle where

open import Data.Nat using (ℕ; suc) renaming (_+_ to _+ℕ_)
open import Data.Bool using (false)
open import Data.Product using (proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore hiding (AllocMode; Stack; Heap)
open import Once.Semantics.Machine using (⟦_⟧)
open import Once.IR
open import Once.CCC.IR.Stack
open import Once.CCC.Eval using (eval)
open import Once.CCC.Machine.Allocation hiding (AllocMode)
open import Once.CCC.Machine.ClosureWellFormed

import Once.CCC.Machine.SMPrimitives as SMP
import Once.CCC.Machine.IR.PairStackWF.Validity as PairValidity

module MiddleImpl {FS : FrameSemantics} (program-bound : ℕ) where
  open FrameSemantics FS
  open FrontierInvariant {FS}
  open AbstractExec {FS}
  open SMP.TracePrimitives {FS}

  module VImpl = PairValidity.ValidityImpl {FS} program-bound

  open ClosureWellFormedDef {FS} program-bound using (ValidAtWF; IRResultAWF)

  -- Inline helpers — must match Finalize.FinalizeImpl.pair-* exactly
  -- (definitional equality).
  pair-setup-trace : (alloc : AllocState {FS}) → AbstractTrace
  pair-setup-trace alloc =
    mov-to-output ∷ store-at-slot (next-slot alloc) ∷
    instr-alloc-stack (suc pair-slots) ∷ []

  pair-s-after-setup : (s : LocState FS) (alloc : AllocState {FS}) → LocState FS
  pair-s-after-setup s alloc = proj₁ (exec-trace (pair-setup-trace alloc) s alloc)

  pair-alloc-after-setup : (s : LocState FS) (alloc : AllocState {FS}) → AllocState {FS}
  pair-alloc-after-setup s alloc = proj₂ (exec-trace (pair-setup-trace alloc) s alloc)

  pair-alloc-after-pair-slots : (alloc : AllocState {FS}) → AllocState {FS}
  pair-alloc-after-pair-slots alloc =
    record alloc { next-slot = suc (suc (suc (next-slot alloc))) }

  pair-middle-trace : (alloc : AllocState {FS}) → AbstractTrace
  pair-middle-trace alloc =
    store-at-slot (suc (next-slot alloc)) ∷
    restore-input (next-slot alloc) ∷ []

  pair-s-after-middle :
    (s : LocState FS) (alloc : AllocState {FS}) (f-trace : AbstractTrace) →
    LocState FS
  pair-s-after-middle s alloc f-trace =
    proj₁ (exec-trace (pair-middle-trace alloc)
            (proj₁ (exec-trace f-trace (pair-s-after-setup s alloc)
                                       (pair-alloc-after-setup s alloc)))
            (proj₂ (exec-trace f-trace (pair-s-after-setup s alloc)
                                       (pair-alloc-after-setup s alloc))))

  pair-alloc-after-f-reclaim :
    (alloc : AllocState {FS}) (final-alloc-f : AllocState {FS}) →
    AllocState {FS}
  pair-alloc-after-f-reclaim alloc final-alloc-f = record alloc
    { next-slot     = next-slot     final-alloc-f
    ; next-heap-ref = next-heap-ref final-alloc-f }

  record PairMiddleBundle
    {A B C : Type}
    (mIn mF : AllocMode) (f : IR A B) (g : IR A C) (x : ⟦ A ⟧)
    (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS})
    (result-f : IRResultAWF mF f x (pair-s-after-setup s alloc)
                                    (pair-alloc-after-pair-slots alloc)) : Set where
    field
      valid-at-s-after-middle :
        ValidAtWF mIn (pair-alloc-after-f-reclaim alloc
                        (IRResultAWF.final-alloc result-f))
                      x input-loc
                      (pair-s-after-middle s alloc (IRResultAWF.trace result-f))
      input-before-at-reclaim-f :
        BeforeFrontier (pair-alloc-after-f-reclaim alloc
                         (IRResultAWF.final-alloc result-f))
                       input-loc
      not-halted-after-middle :
        halted (pair-s-after-middle s alloc (IRResultAWF.trace result-f)) ≡ false
      rdi-eq-at-s-after-middle :
        readReg (regs (pair-s-after-middle s alloc (IRResultAWF.trace result-f)))
                Input1 ≡ SV-Ptr input-loc

  mk-pair-middle-bundle :
    ∀ {A B C} (mIn mF : AllocMode) (f : IR A B) (g : IR A C) (x : ⟦ A ⟧)
      (input-loc : ValueLocation FS)
      (s : LocState FS) (alloc : AllocState {FS})
      (not-halted : halted s ≡ false)
      (rdi-eq : readReg (regs s) Input1 ≡ SV-Ptr input-loc)
      (input-valid-wf : ValidAtWF mIn alloc x input-loc s)
      (input-before : BeforeFrontier alloc input-loc)
      (result-f : IRResultAWF mF f x (pair-s-after-setup s alloc)
                                      (pair-alloc-after-pair-slots alloc))
      (fst-loc : ValueLocation FS)
      (fst-rax-eq :
         readReg (regs (IRResultAWF.final-state result-f)) Output ≡
         SV-Ptr fst-loc)
      (fst-valid-from-f :
         ValidAtWF mF (IRResultAWF.final-alloc result-f) (eval f x)
                      fst-loc (IRResultAWF.final-state result-f))
      (fst-before-pre-from-f :
         BeforeFrontier (IRResultAWF.final-alloc result-f) fst-loc)
      (fst-rec-valid-from-f :
         ValidAtWF mF
           (record (pair-alloc-after-pair-slots alloc)
              { next-slot     = next-slot     (IRResultAWF.final-alloc result-f)
              ; next-heap-ref = next-heap-ref (IRResultAWF.final-alloc result-f) })
           (eval f x) fst-loc (IRResultAWF.final-state result-f))
      (fst-rec-before-from-f :
         BeforeFrontier
           (record (pair-alloc-after-pair-slots alloc)
              { next-slot     = next-slot     (IRResultAWF.final-alloc result-f)
              ; next-heap-ref = next-heap-ref (IRResultAWF.final-alloc result-f) })
           fst-loc)
      (f-tnhw : TraceNoHeapWrites (IRResultAWF.trace result-f)) →
      PairMiddleBundle mIn mF f g x input-loc s alloc result-f
  mk-pair-middle-bundle mIn mF f g x input-loc s alloc not-halted rdi-eq
                        input-valid-wf input-before result-f
                        fst-loc fst-rax-eq fst-valid-from-f
                        fst-before-pre-from-f fst-rec-valid-from-f
                        fst-rec-before-from-f f-tnhw =
    record
      { valid-at-s-after-middle   = V2.valid-at-s-after-middle
      ; input-before-at-reclaim-f = V2.input-before-at-reclaim-f
      ; not-halted-after-middle   = V2.not-halted-after-middle
      ; rdi-eq-at-s-after-middle  = V2.rdi-eq-at-s-after-middle
      }
    where
      module V0 = VImpl.Validity mIn f g x input-loc s alloc not-halted rdi-eq
                                  input-valid-wf input-before
      module V2 = V0.L2 mF result-f fst-loc fst-rax-eq fst-valid-from-f
                        fst-before-pre-from-f fst-rec-valid-from-f
                        fst-rec-before-from-f f-tnhw
