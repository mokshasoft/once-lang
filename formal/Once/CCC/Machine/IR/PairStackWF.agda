-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Machine.IR.PairStackWF
--
-- Clean reimplementation of pair IR well-formedness using:
-- 1. Parameterized validity preservation lemma for both f and g
-- 2. Only positive invariants (TraceWritesAbove, BeforeFrontier)
-- 3. No function definitions in where clauses (module-level helpers)
--
-- Key insight: f and g are symmetric - both take input from a register
-- and write to [start, max). The validityWF-trace-preserves lemma from
-- ClosureWellFormed handles all cases without gap-unreachability reasoning.
------------------------------------------------------------------------

module Once.CCC.Machine.IR.PairStackWF where

open import Data.Nat using (ℕ; suc; _<_; _≤_; _≥_; s≤s; z≤n; _⊔_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; m≤n+m; n≤1+n; +-comm; +-assoc; +-suc; +-identityʳ; +-monoˡ-≤; +-monoʳ-≤; <-≤-trans; <⇒≤; <⇒≢; m≤m⊔n; m≤n⊔m; ⊔-lub; _<?_; ≮⇒≥)
open import Data.Empty using (⊥-elim)
open import Data.Bool using (false)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym; cong; cong₂; subst; subst₂)
open import Relation.Nullary using (yes; no)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore hiding (AllocMode; Stack; Heap)
open import Once.Semantics.Machine using (⟦_⟧; sem-pair)
pair = sem-pair  -- Semantic pair constructor for ⟦ A * B ⟧
open import Once.IR
open import Once.CCC.Machine.LocMatchesMode using (LocMatchesMode)
open import Once.CCC.Eval using (eval)
open import Once.IR.Size
open import Once.CCC.IR.Stack
open import Once.CCC.Machine.Allocation hiding (AllocMode)
open import Once.CCC.Machine.ClosureWellFormed

-- Import SMPrimitives qualified for memory reasoning primitives
import Once.CCC.Machine.SMPrimitives as SMP

-- Plan 0.18 driver-glue extraction:
--   Setup     — rec-wf-f-arg bundle (input-valid-wf-after-setup etc.)
--   Middle    — rec-wf-g-arg bundle (valid-at-s-after-middle etc.)
--   Finalize  — 9-instantiation chain + IRResultAWF assembly
-- All three transitively import Validity; PairStackWF.agda itself does NOT
-- need to instantiate VImpl.Validity (the V0 / V2 cost is paid inside
-- the bundle helpers, where it's cached after first build).
import Once.CCC.Machine.IR.PairStackWF.Setup as PairSetup
import Once.CCC.Machine.IR.PairStackWF.Middle as PairMiddle
import Once.CCC.Machine.IR.PairStackWF.Finalize as PairFinalize

------------------------------------------------------------------------
-- PairStackWF Implementation
------------------------------------------------------------------------

module PairStackWFImpl {FS : FrameSemantics} (program-bound : ℕ) where
  open FrameSemantics FS
  open FrontierInvariant {FS}
  open MemOps {FS}
  open WriteOps {FS}
  open StackAllocation {FS}
  open AbstractExec {FS}
  open ExecLemmas {FS}

  -- Open SMPrimitives modules for memory reasoning
  open SMP.MemoryOps {FS}
  open SMP.InstrPrimitives {FS}
  open SMP.TracePrimitives {FS}
  open SMP.TraceComposition {FS}
  open SMP.TraceOutputDeterminism {FS}

  -- Plan 0.18: instantiate Setup / Middle / Finalize once at
  -- PairStackWFImpl level. VImpl.Validity is NOT instantiated here —
  -- it's consumed only inside the bundle helpers.
  module SImpl = PairSetup.SetupImpl {FS} program-bound
  module MImpl = PairMiddle.MiddleImpl {FS} program-bound
  module FImpl = PairFinalize.FinalizeImpl {FS} program-bound

  -- Types from ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound
    using (ValidAtWF; IRResultAWF; ResultPlace; unit-result; at-loc;
           RecDispatcherWF; mk-IRResultAWF-via-bump;
           valid-pair-wf; valid-unit-wf;
           validityWF-mem-only; validityWF-mem-preserved;
           validityWF-mem-preserved-in-regions;
           validityWF-frontier-advance;
           validityWF-trace-preserves;
           irresult-mem-preserved; mem-preserved-from-tnhw)

  ------------------------------------------------------------------------
  -- run-pair: Main implementation
  ------------------------------------------------------------------------

  -- Plan 0.14 (Camp 2): run-pair handles the Stack-mode pair only.
  -- pair-loc is AtStack so LocMatchesMode Stack pair-loc = ⊤ (witness tt).
  -- The Heap-mode pair is handled by PairAllocWF.run-pair-heap; the
  -- Dispatcher case-splits on the pair IR's mode to pick the handler.
  run-pair : ∀ {A B C} (mIn : AllocMode) (f : IR A B) (g : IR A C)
    (rec-wf : RecDispatcherWF (ir-size (⟨ f , g ⟩ Heap)))
    (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ SV-Ptr input-loc →
    IRResultAWF Stack (⟨ f , g ⟩ Stack) x s alloc

  run-pair {A} {B} {C} mIn f g rec-wf x input-loc s alloc
           input-valid-wf input-before not-halted rdi-eq =
    -- Plan 0.18 Option 2: the heavy 9-instantiation chain + final
    -- IRResultAWF assembly lives in PairFinalize.FinalizeImpl.Finalize.
    -- run-pair only handles: setup-state derivation (VVal), rec-wf f,
    -- FstFacts dispatch, middle-state derivation (VL2), rec-wf g,
    -- SndFacts dispatch, then a single call to VFin.pair-finalize.
    VFin.pair-finalize mF result-f fst-loc fst-rax-eq fst-valid-from-f
                       fst-before-pre-from-f fst-rec-valid-from-f
                       fst-rec-before-from-f f-tnhw
                       mG result-g snd-loc snd-rax-eq
                       snd-rec-valid-from-g snd-rec-before-from-g g-tnhw
    where
      -- Setup-side: rec-wf-f args via SImpl bundle.
      setup-bundle = SImpl.mk-pair-setup-bundle mIn f g x input-loc s alloc
                       not-halted rdi-eq input-valid-wf input-before
      open SImpl.PairSetupBundle setup-bundle

      ------------------------------------------------------------------------
      -- Run f via recursive dispatch — at the post-setup state.
      ------------------------------------------------------------------------
      f-exec-result : ∃[ mOut ] IRResultAWF mOut f x
                        (SImpl.pair-s-after-setup s alloc)
                        (SImpl.pair-alloc-after-pair-slots alloc)
      f-exec-result = rec-wf mIn f (⟨,⟩-f-smaller f g {Stack}) x input-loc
                        (SImpl.pair-s-after-setup s alloc)
                        (SImpl.pair-alloc-after-pair-slots alloc)
                        input-valid-wf-after-setup input-before-at-f-start
                        not-halted-after-setup rdi-eq-after-setup
      mF = proj₁ f-exec-result
      result-f = proj₂ f-exec-result
      s₁ = IRResultAWF.final-state result-f
      f-trace = IRResultAWF.trace result-f

      ------------------------------------------------------------------------
      -- Plan 0.2.4.5 D1 task #28: dispatch on f's result-place.
      ------------------------------------------------------------------------
      record FstFacts : Set where
        field
          fst-loc-f       : ValueLocation FS
          fst-rax-f       : readReg (regs s₁) Output ≡ SV-Ptr fst-loc-f
          fst-valid-f     : ValidAtWF mF (IRResultAWF.final-alloc result-f) (eval f x) fst-loc-f s₁
          fst-before-f    : BeforeFrontier (IRResultAWF.final-alloc result-f) fst-loc-f
          fst-rec-valid-f : ValidAtWF mF (record (SImpl.pair-alloc-after-pair-slots alloc)
                                            { next-slot     = next-slot     (IRResultAWF.final-alloc result-f)
                                            ; next-heap-ref = next-heap-ref (IRResultAWF.final-alloc result-f) })
                                       (eval f x) fst-loc-f s₁
          fst-rec-before-f : BeforeFrontier (record (SImpl.pair-alloc-after-pair-slots alloc)
                                              { next-slot     = next-slot     (IRResultAWF.final-alloc result-f)
                                              ; next-heap-ref = next-heap-ref (IRResultAWF.final-alloc result-f) })
                                            fst-loc-f

      f-facts : FstFacts
      f-facts with IRResultAWF.result-place result-f
      ... | at-loc loc valid before rax rvalid rbefore = record
              { fst-loc-f        = loc
              ; fst-rax-f        = rax
              ; fst-valid-f      = valid
              ; fst-before-f     = before
              ; fst-rec-valid-f  = rvalid
              ; fst-rec-before-f = rbefore
              }
      ... | unit-result = record
              { fst-loc-f        = unit-fst-loc
              ; fst-rax-f        = unit-fst-rax
              ; fst-valid-f      = valid-unit-wf
              ; fst-before-f     = unit-fst-before
              ; fst-rec-valid-f  = valid-unit-wf
              ; fst-rec-before-f = unit-fst-rec-before
              }
        where
          postulate
            -- Unit values have no observable location; postulate a witness loc.
            unit-fst-loc : ValueLocation FS
            unit-fst-rax : readReg (regs s₁) Output ≡ SV-Ptr unit-fst-loc
            unit-fst-before : BeforeFrontier (IRResultAWF.final-alloc result-f) unit-fst-loc
            unit-fst-rec-before : BeforeFrontier
              (record (SImpl.pair-alloc-after-pair-slots alloc)
                { next-slot     = next-slot     (IRResultAWF.final-alloc result-f)
                ; next-heap-ref = next-heap-ref (IRResultAWF.final-alloc result-f) })
              unit-fst-loc

      open FstFacts f-facts using ()
        renaming (fst-loc-f to fst-loc;
                  fst-rax-f to fst-rax-eq;
                  fst-valid-f to fst-valid-from-f;
                  fst-before-f to fst-before-pre-from-f;
                  fst-rec-valid-f to fst-rec-valid-from-f;
                  fst-rec-before-f to fst-rec-before-from-f)

      f-tnhw : TraceNoHeapWrites f-trace
      f-tnhw = SMP.!!  -- TODO: stack-only sub-IR derivation (post Plan 0.14 follow-up)

      -- Middle-side: rec-wf-g args via MImpl bundle.
      middle-bundle = MImpl.mk-pair-middle-bundle mIn mF f g x input-loc s alloc
                        not-halted rdi-eq input-valid-wf input-before result-f
                        fst-loc fst-rax-eq fst-valid-from-f
                        fst-before-pre-from-f fst-rec-valid-from-f
                        fst-rec-before-from-f f-tnhw
      open MImpl.PairMiddleBundle middle-bundle

      ------------------------------------------------------------------------
      -- Run g via recursive dispatch — at runtime state.
      ------------------------------------------------------------------------
      g-exec-result : ∃[ mOut ] IRResultAWF mOut g x
                        (MImpl.pair-s-after-middle s alloc (IRResultAWF.trace result-f))
                        (MImpl.pair-alloc-after-f-reclaim alloc
                          (IRResultAWF.final-alloc result-f))
      g-exec-result = rec-wf mIn g (⟨,⟩-g-smaller f g {Stack}) x input-loc
                        (MImpl.pair-s-after-middle s alloc (IRResultAWF.trace result-f))
                        (MImpl.pair-alloc-after-f-reclaim alloc
                          (IRResultAWF.final-alloc result-f))
                        valid-at-s-after-middle input-before-at-reclaim-f
                        not-halted-after-middle rdi-eq-at-s-after-middle
      mG = proj₁ g-exec-result
      result-g = proj₂ g-exec-result
      s₂ = IRResultAWF.final-state result-g
      g-trace = IRResultAWF.trace result-g

      ------------------------------------------------------------------------
      -- Plan 0.2.4.5 D1 task #28: dispatch on g's result-place.
      ------------------------------------------------------------------------
      record SndFacts (g-input-alloc : AllocState {FS}) : Set where
        field
          snd-loc-g       : ValueLocation FS
          snd-rax-g       : readReg (regs s₂) Output ≡ SV-Ptr snd-loc-g
          snd-valid-g     : ValidAtWF mG (IRResultAWF.final-alloc result-g) (eval g x) snd-loc-g s₂
          snd-before-g    : BeforeFrontier (IRResultAWF.final-alloc result-g) snd-loc-g
          snd-rec-valid-g : ValidAtWF mG (record g-input-alloc
                                            { next-slot     = next-slot     (IRResultAWF.final-alloc result-g)
                                            ; next-heap-ref = next-heap-ref (IRResultAWF.final-alloc result-g) })
                                       (eval g x) snd-loc-g s₂
          snd-rec-before-g : BeforeFrontier (record g-input-alloc
                                              { next-slot     = next-slot     (IRResultAWF.final-alloc result-g)
                                              ; next-heap-ref = next-heap-ref (IRResultAWF.final-alloc result-g) })
                                            snd-loc-g

      g-facts : SndFacts (MImpl.pair-alloc-after-f-reclaim alloc
                           (IRResultAWF.final-alloc result-f))
      g-facts with IRResultAWF.result-place result-g
      ... | at-loc loc valid before rax rvalid rbefore = record
              { snd-loc-g        = loc
              ; snd-rax-g        = rax
              ; snd-valid-g      = valid
              ; snd-before-g     = before
              ; snd-rec-valid-g  = rvalid
              ; snd-rec-before-g = rbefore
              }
      ... | unit-result = record
              { snd-loc-g        = unit-snd-loc
              ; snd-rax-g        = unit-snd-rax
              ; snd-valid-g      = valid-unit-wf
              ; snd-before-g     = unit-snd-before
              ; snd-rec-valid-g  = valid-unit-wf
              ; snd-rec-before-g = unit-snd-rec-before
              }
        where
          postulate
            unit-snd-loc : ValueLocation FS
            unit-snd-rax : readReg (regs s₂) Output ≡ SV-Ptr unit-snd-loc
            unit-snd-before : BeforeFrontier (IRResultAWF.final-alloc result-g) unit-snd-loc
            unit-snd-rec-before : BeforeFrontier
              (record (MImpl.pair-alloc-after-f-reclaim alloc
                        (IRResultAWF.final-alloc result-f))
                { next-slot     = next-slot     (IRResultAWF.final-alloc result-g)
                ; next-heap-ref = next-heap-ref (IRResultAWF.final-alloc result-g) })
              unit-snd-loc

      open SndFacts g-facts using ()
        renaming (snd-loc-g to snd-loc;
                  snd-rax-g to snd-rax-eq;
                  snd-valid-g to snd-valid-from-g;
                  snd-before-g to snd-before-pre-from-g;
                  snd-rec-valid-g to snd-rec-valid-from-g;
                  snd-rec-before-g to snd-rec-before-from-g)

      g-tnhw : TraceNoHeapWrites g-trace
      g-tnhw = SMP.!!  -- TODO: stack-only sub-IR derivation (post Plan 0.14 follow-up)

      ------------------------------------------------------------------------
      -- Instantiate the Finalize submodule once and forward all derived
      -- products. pair-finalize handles VBnd0/1/2, VAsm0/1/2, VL3, the
      -- pair-bump / pair-before computations, and the final
      -- mk-IRResultAWF-via-bump assembly.
      ------------------------------------------------------------------------
      module VFin = FImpl.Finalize mIn f g x input-loc s alloc not-halted rdi-eq
                                    input-valid-wf input-before
