-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Machine.IR.PairWF2.Finalize
--
-- Plan 0.18 — Step 1 + Option 2 (multi-file split).
--
-- Extracts the heavy module-instantiation chain (Validity.L2.L3 +
-- Bounds.L2.L3 + Assembly.L2.L3) plus the pair-bump / pair-before /
-- mk-IRResultAWF-via-bump assembly out of PairWF2.run-pair's
-- where-block. Lives in its own compilation unit so the elaborator's
-- ambient context for typechecking this chain is just the Finalize
-- submodule parameters, not PairWF2.run-pair's accumulating where.
--
-- PairWF2.run-pair instantiates this Finalize module once and calls
-- the single `pair-finalize` export to assemble the final IRResultAWF.
------------------------------------------------------------------------

module Once.CCC.Machine.IR.PairWF2.Finalize where

open import Data.Nat using (ℕ; suc) renaming (_+_ to _+ℕ_)
open import Data.Bool using (false)
open import Data.Unit using (⊤; tt)
open import Data.Product using (proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore hiding (AllocMode; Stack; Heap)
open import Once.Semantics.Machine using (⟦_⟧; sem-pair)
pair = sem-pair
open import Once.CCC.IR
open import Once.CCC.Eval using (eval)
open import Once.CCC.IR.Size
open import Once.CCC.IR.Stack
open import Once.CCC.Machine.Allocation hiding (AllocMode)
open import Once.CCC.Machine.ClosureWellFormed

import Once.CCC.Machine.SMPrimitives as SMP

import Once.CCC.Machine.IR.PairWF2.Validity as PairValidity
import Once.CCC.Machine.IR.PairWF2.Bounds as PairBounds
import Once.CCC.Machine.IR.PairWF2.Assembly as PairAssembly

module FinalizeImpl {FS : FrameSemantics} (program-bound : ℕ) where
  open FrameSemantics FS
  open FrontierInvariant {FS}
  open MemOps {FS}
  open WriteOps {FS}
  open StackAllocation {FS}
  open AbstractExec {FS}
  open ExecLemmas {FS}

  open SMP.MemoryOps {FS}
  open SMP.InstrPrimitives {FS}
  open SMP.TracePrimitives {FS}
  open SMP.TraceComposition {FS}
  open SMP.TraceOutputDeterminism {FS}

  module VImpl = PairValidity.ValidityImpl {FS} program-bound
  module BImpl = PairBounds.BoundsImpl {FS} program-bound
  module AImpl = PairAssembly.AssemblyImpl {FS} program-bound

  open ClosureWellFormedDef {FS} program-bound
    using (ValidAtWF; IRResultAWF; at-loc; mk-IRResultAWF-via-bump;
           mem-preserved-from-tnhw)

  ----------------------------------------------------------------------
  -- Inline state-derivation helpers — top-level functions, NOT module
  -- members. These reduce definitionally to the same exec-trace
  -- expressions as VImpl.Validity.s-after-setup / .alloc-after-pair-slots
  -- etc., so result-f / result-g built via VVal at the call site unify
  -- with pair-finalize's parameter types without forcing PairWF2 to
  -- re-elaborate Validity's submodule instantiation.
  --
  -- Why this matters: a previous version of pair-finalize's signature
  -- referenced V0.s-after-setup etc. (V0 = Validity instantiation inside
  -- the Finalize submodule). Type-checking the call site forced Agda
  -- to elaborate that V0 in PairWF2's scope, defeating the file-split.
  ----------------------------------------------------------------------
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

  ----------------------------------------------------------------------
  -- Finalize submodule — parameterized over the run-pair-side base
  -- inputs. Sits at the same nesting level as Validity / Bounds /
  -- Assembly; consumers (PairWF2.run-pair) instantiate it with their
  -- own f/g/x/... and then call pair-finalize.
  ----------------------------------------------------------------------
  module Finalize
    {A B C : Type}
    (mIn : AllocMode)
    (f : IR A B) (g : IR A C)
    (x : ⟦ A ⟧)
    (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS})
    (not-halted : halted s ≡ false)
    (rdi-eq : readReg (regs s) Input1 ≡ SV-Ptr input-loc)
    (input-valid-wf : ValidAtWF mIn alloc x input-loc s)
    (input-before : BeforeFrontier alloc input-loc)
    where

    -- V0 is the local instantiation of Validity. Body-only — never
    -- mentioned in pair-finalize's signature (signature uses the
    -- pair-s-after-setup / pair-alloc-after-pair-slots helpers above,
    -- which reduce to the same exec-trace expressions definitionally).
    module V0 = VImpl.Validity mIn f g x input-loc s alloc not-halted rdi-eq
                                input-valid-wf input-before

    pair-finalize :
      (mF : AllocMode)
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
      (mG : AllocMode)
      (result-g : IRResultAWF mG g x
                   (pair-s-after-middle s alloc (IRResultAWF.trace result-f))
                   (pair-alloc-after-f-reclaim alloc (IRResultAWF.final-alloc result-f)))
      (snd-loc : ValueLocation FS)
      (snd-rax-eq :
         readReg (regs (IRResultAWF.final-state result-g)) Output ≡
         SV-Ptr snd-loc)
      (snd-rec-valid-from-g :
         ValidAtWF mG
           (record (pair-alloc-after-f-reclaim alloc (IRResultAWF.final-alloc result-f))
              { next-slot     = next-slot     (IRResultAWF.final-alloc result-g)
              ; next-heap-ref = next-heap-ref (IRResultAWF.final-alloc result-g) })
           (eval g x) snd-loc (IRResultAWF.final-state result-g))
      (snd-rec-before-from-g :
         BeforeFrontier
           (record (pair-alloc-after-f-reclaim alloc (IRResultAWF.final-alloc result-f))
              { next-slot     = next-slot     (IRResultAWF.final-alloc result-g)
              ; next-heap-ref = next-heap-ref (IRResultAWF.final-alloc result-g) })
           snd-loc) →
      (g-tnhw : TraceNoHeapWrites (IRResultAWF.trace result-g)) →
      IRResultAWF Stack (⟨ f , g ⟩ Stack) x s alloc

    pair-finalize mF result-f fst-loc fst-rax-eq fst-valid-from-f
                  fst-before-pre-from-f fst-rec-valid-from-f fst-rec-before-from-f
                  f-tnhw
                  mG result-g snd-loc snd-rax-eq snd-rec-valid-from-g
                  snd-rec-before-from-g g-tnhw =
      mk-IRResultAWF-via-bump
        A2.s-final
        A2.alloc-final
        B2.pair-trace
        pair-bump
        pair-bump-eq
        SMP.!!  -- trace-is-ir-to-trace (Pattern 1, pre-existing hole)
        refl
        A2.alloc-correct-pair
        (at-loc V0.pair-loc V3.pair-valid-wf-final pair-before A2.rax-eq
                V3.pair-valid-wf-final pair-before)
        A2.not-halted-final
        (mem-preserved-from-tnhw alloc B2.pair-trace s A2.s-final refl
              B2.pair-trace-writes-above B2.pair-trace-no-heap-writes)
        A2.pair-trace-twf
        (exec-trace-preserves-halted-WF B2.pair-trace)
        (record
          { max-slot-written = B2.pair-max-slot
          ; stack-budget = B2.req-pair
          ; bump-fits-stack-budget = SMP.!!    -- Plan 0.17.1 TODO (pre-existing)
          ; max-slot-geq-final = SMP.!!        -- Plan 0.17.1 TODO (pre-existing)
          ; max-slot-usage-bound = B2.pair-max-slot-bound
          ; frontier-slot-stable = λ _ _ _ _ _ → inj₂ (inj₂ tt)
          ; trace-writes-above = B2.pair-trace-writes-above
          ; trace-slot-reads-above = B2.pair-trace-slot-reads-above
          ; trace-writes-below = B2.pair-trace-writes-below
          ; trace-slot-reads-below = B2.pair-trace-slot-reads-below
          ; scratch-budget = B2.req-pair-scratch
          ; scratch-bounded = SMP.!!           -- Plan 0.17.1 TODO (pre-existing)
          })
        (record
          { heap-budget = IRResultAWF.heap-budget result-f +ℕ IRResultAWF.heap-budget result-g
          ; max-heap-ref-written = IRResultAWF.max-heap-ref-written result-g
          ; bump-fits-heap-budget = SMP.!!     -- Plan 0.17.1 TODO (pre-existing)
          ; max-heap-ref-geq-final = SMP.!!    -- Plan 0.17.1 TODO (pre-existing)
          ; max-heap-usage-bound = B2.pair-max-heap-usage-bound
          })
      where
        module V2 = V0.L2 mF result-f fst-loc fst-rax-eq fst-valid-from-f
                          fst-before-pre-from-f fst-rec-valid-from-f
                          fst-rec-before-from-f f-tnhw
        module B0 = BImpl.Bounds alloc
        module B1 = B0.L2 f x V0.s-after-setup mF result-f f-tnhw
        module B2 = B1.L3 g V2.s-after-middle mG result-g g-tnhw
        module A0 = AImpl.Assembly f g x s alloc not-halted
        module A1 = A0.L2 mF result-f f-tnhw
        module A2 = A1.L3 mG result-g g-tnhw V2.middle-restore-input-witness
        module V3 = V2.L3 mG result-g snd-loc snd-rax-eq snd-rec-valid-from-g
                          snd-rec-before-from-g g-tnhw A2.s-final A2.s-final-eq

        pair-bump : AllocBump
        pair-bump = mkBump
          (3 +ℕ (next-slot-delta (IRResultAWF.bump result-f)
                 +ℕ next-slot-delta (IRResultAWF.bump result-g)))
          (next-heap-ref-delta (IRResultAWF.bump result-f)
           +ℕ next-heap-ref-delta (IRResultAWF.bump result-g))

        pair-bump-eq : A2.alloc-final ≡ apply-bump pair-bump alloc
        pair-bump-eq = SMP.!!  -- pre-existing (Plan 0.17 Phase 5)

        pair-before : BeforeFrontier A2.alloc-final V0.pair-loc
        pair-before = stack-before refl B2.fst<reclaim-g
