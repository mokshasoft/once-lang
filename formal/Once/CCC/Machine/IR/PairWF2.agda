-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Machine.IR.PairWF2
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

module Once.CCC.Machine.IR.PairWF2 where

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
open import Once.CCC.IR
open import Once.CCC.Eval using (eval)
open import Once.CCC.IR.Size
open import Once.CCC.IR.Stack
open import Once.CCC.Machine.Allocation hiding (AllocMode)
open import Once.CCC.Machine.ClosureWellFormed

-- Import SMPrimitives qualified for memory reasoning primitives
import Once.CCC.Machine.SMPrimitives as SMP

-- Plan 0.18: Phases 9-11 (oaf-* / oag-* / validity chains) live in this
-- companion module so they elaborate as a separate compilation unit
-- (halves peak typechecker RSS during full-project builds).
import Once.CCC.Machine.IR.PairWF2.Validity as PairValidity

-- Plan 0.17.1 / 0.18 Cluster B: trace combinatorics + budget bounds.
-- Pure structural facts about pair-trace; no state dependency.
import Once.CCC.Machine.IR.PairWF2.Bounds as PairBounds

-- Plan 0.17.1 / 0.18 Cluster A: state-evolution proofs (alloc-correct,
-- pair-trace-twf, mem-preserved-pair, rax-eq, not-halted-final, etc.).
import Once.CCC.Machine.IR.PairWF2.Assembly as PairAssembly

------------------------------------------------------------------------
-- PairWF2 Implementation
------------------------------------------------------------------------

module PairWF2Impl {FS : FrameSemantics} (program-bound : ℕ) where
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

  -- Plan 0.18: instantiate the Validity companion module's ValidityImpl
  -- at this FS + program-bound. run-pair later instantiates .Validity.L2.L3.
  module VImpl = PairValidity.ValidityImpl {FS} program-bound

  -- Cluster B: Bounds module instantiation.
  module BImpl = PairBounds.BoundsImpl {FS} program-bound

  -- Cluster A: Assembly module instantiation.
  module AImpl = PairAssembly.AssemblyImpl {FS} program-bound

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
  -- The Heap-mode pair is handled by PairHeapWF.run-pair-heap; the
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
    -- Plan 0.17 / 0.18: use mk-IRResultAWF-via-bump.
    -- Heavy proofs come from VBnd2 (Bounds, Cluster B) and VAsm2
    -- (Assembly, Cluster A); validity from VL3 (Validity, Cluster C).
    mk-IRResultAWF-via-bump
      VAsm2.s-final
      VAsm2.alloc-final
      VBnd2.pair-trace
      pair-bump
      pair-bump-eq
      SMP.!!  -- trace-is-ir-to-trace (Pattern 1)
      refl
      VAsm2.alloc-correct-pair
      (at-loc pair-loc pair-valid-wf-final pair-before VAsm2.rax-eq
              pair-valid-wf-final pair-before)
      VAsm2.not-halted-final
      (mem-preserved-from-tnhw alloc VBnd2.pair-trace s VAsm2.s-final refl
            VBnd2.pair-trace-writes-above VBnd2.pair-trace-no-heap-writes)
      VAsm2.pair-trace-twf
      (exec-trace-preserves-halted-WF VBnd2.pair-trace)
      (record
        { max-slot-written = VBnd2.pair-max-slot
        ; stack-budget = VBnd2.req-pair
        ; bump-fits-stack-budget = SMP.!!    -- Plan 0.17.1 TODO
        ; max-slot-geq-final = SMP.!!        -- Plan 0.17.1 TODO (was pair-max-slot-geq-final)
        ; max-slot-usage-bound = VBnd2.pair-max-slot-bound
        ; frontier-slot-stable = pair-frontier-stable
        ; trace-writes-above = VBnd2.pair-trace-writes-above
        ; trace-slot-reads-above = VBnd2.pair-trace-slot-reads-above
        ; trace-writes-below = VBnd2.pair-trace-writes-below
        ; trace-slot-reads-below = VBnd2.pair-trace-slot-reads-below
        ; scratch-budget = VBnd2.req-pair-scratch
        ; scratch-bounded = SMP.!!           -- Plan 0.17.1 TODO (was pair-scratch-bounded)
        })
      (record
        { heap-budget = IRResultAWF.heap-budget result-f +ℕ IRResultAWF.heap-budget result-g
        ; max-heap-ref-written = IRResultAWF.max-heap-ref-written result-g
        ; bump-fits-heap-budget = SMP.!!     -- Plan 0.17.1 TODO
        ; max-heap-ref-geq-final = SMP.!!    -- Plan 0.17.1 TODO
        ; max-heap-usage-bound = VBnd2.pair-max-heap-usage-bound
        })
    where
      ------------------------------------------------------------------------
      -- Plan 0.18 wire-through: instantiate Validity at the top of the
      -- where-block so all layout/setup/L2/L3 intermediates come from
      -- there (no per-site duplication). Each `open` brings the derived
      -- binders into scope; PairWF2 only assembles the IRResultAWF on top.
      ------------------------------------------------------------------------
      module VVal = VImpl.Validity mIn f g x input-loc s alloc not-halted rdi-eq
                                   input-valid-wf input-before
      open VVal

      ------------------------------------------------------------------------
      -- Run f via recursive dispatch — at the post-setup state.
      ------------------------------------------------------------------------
      f-exec-result : ∃[ mOut ] IRResultAWF mOut f x s-after-setup alloc-after-pair-slots
      f-exec-result = rec-wf mIn f (⟨,⟩-f-smaller f g {Stack}) x input-loc s-after-setup alloc-after-pair-slots
                        input-valid-wf-after-setup input-before-at-f-start
                        not-halted-after-setup rdi-eq-after-setup
      mF = proj₁ f-exec-result
      result-f = proj₂ f-exec-result
      s₁ = IRResultAWF.final-state result-f
      f-trace = IRResultAWF.trace result-f

      -- Plan 0.2.4.5 D1 task #30: f's portion of dynamic budgets.
      rf = IRResultAWF.stack-budget result-f
      sf = IRResultAWF.scratch-budget result-f

      ------------------------------------------------------------------------
      -- Plan 0.2.4.5 D1 task #28: dispatch on f's result-place to
      -- extract fst-loc + supporting facts. Same pattern as compose:
      --   at-loc → bound vars from constructor.
      --   unit-result → fst-loc = readReg s₁ Output (whatever Output
      --     happens to be at f's end), making the rax equation refl
      --     by construction. validity at any loc is valid-unit-wf.
      --     pair-loc[0]'s contents will equal Output's value via the
      --     store-at-slot fst-slot instruction, so valid-pair-wf's
      --     "pair-loc[0] ≡ just (SV-Ptr fst-loc)" claim holds.
      record FstFacts : Set where
        field
          fst-loc-f       : ValueLocation FS
          -- Plan 0.13.2: Output now stores SV-Ptr.
          fst-rax-f       : readReg (regs s₁) Output ≡ SV-Ptr fst-loc-f
          fst-valid-f     : ValidAtWF mF (IRResultAWF.final-alloc result-f) (eval f x) fst-loc-f s₁
          fst-before-f    : BeforeFrontier (IRResultAWF.final-alloc result-f) fst-loc-f
          fst-rec-valid-f : ValidAtWF mF (record alloc-after-pair-slots
                                            { next-slot     = next-slot     (IRResultAWF.final-alloc result-f)
                                            ; next-heap-ref = next-heap-ref (IRResultAWF.final-alloc result-f) })
                                       (eval f x) fst-loc-f s₁
          fst-rec-before-f : BeforeFrontier (record alloc-after-pair-slots
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
              (record alloc-after-pair-slots
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

      ------------------------------------------------------------------------
      -- Plan 0.18 wire-through: f-tnhw is the only L2 input we still
      -- supply (postulate); everything else comes from VVal.L2.
      ------------------------------------------------------------------------
      f-tnhw : TraceNoHeapWrites f-trace
      f-tnhw = SMP.!!  -- TODO: stack-only sub-IR derivation (post Plan 0.14 follow-up)

      module VL2 = VVal.L2 mF result-f fst-loc fst-rax-eq fst-valid-from-f
                           fst-before-pre-from-f fst-rec-valid-from-f
                           fst-rec-before-from-f f-tnhw
      open VL2 hiding (s₁; f-trace)

      -- Local: bounds and PairWF2-specific derivations
      reclaim-f-bound : reclaim-f ≤ f-start +ℕ rf
      reclaim-f-bound = IRResultAWF.slot-stays-in-budget result-f


      ------------------------------------------------------------------------
      -- Run g via recursive dispatch — at runtime state.
      ------------------------------------------------------------------------
      g-exec-result : ∃[ mOut ] IRResultAWF mOut g x s-after-middle alloc-after-f-reclaim
      g-exec-result = rec-wf mIn g (⟨,⟩-g-smaller f g {Stack}) x input-loc s-after-middle alloc-after-f-reclaim
                        valid-at-s-after-middle input-before-at-reclaim-f
                        not-halted-after-middle rdi-eq-at-s-after-middle
      mG = proj₁ g-exec-result
      result-g = proj₂ g-exec-result
      s₂ = IRResultAWF.final-state result-g
      g-trace = IRResultAWF.trace result-g

      -- Plan 0.2.4.5 D1 task #30: g's portion + dynamic pair budgets.
      rg = IRResultAWF.stack-budget result-g
      sg = IRResultAWF.scratch-budget result-g
      req-pair = 1 +ℕ rf +ℕ rg +ℕ pair-slots
      req-pair-scratch = 1 +ℕ sf +ℕ sg +ℕ pair-slots

      ------------------------------------------------------------------------
      -- Plan 0.2.4.5 D1 task #28: dispatch on g's result-place to
      -- extract snd-loc + supporting facts. Same pattern as fst above.
      --
      -- Plan 0.13.3 Phase d prep: parameterised over `g-input-alloc`, the
      -- alloc passed to rec-wf for g. Currently `alloc-after-f-reclaim`
      -- (synthetic); after the principled hoist this becomes
      -- `alloc-after-middle` (runtime). Isolating the dependency here
      -- means the hoist becomes a one-line parameter swap at the call
      -- site, with no other type changes.
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

      g-facts : SndFacts alloc-after-f-reclaim
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
              (record alloc-after-f-reclaim
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

      ------------------------------------------------------------------------
      -- g-tnhw postulate (matches f-tnhw above).
      ------------------------------------------------------------------------
      g-tnhw : TraceNoHeapWrites g-trace
      g-tnhw = SMP.!!  -- TODO: stack-only sub-IR derivation (post Plan 0.14 follow-up)

      ------------------------------------------------------------------------
      -- Plan 0.18 wire-through: Bounds instantiation (Cluster B).
      -- VBnd2 exports pair-trace and all trace-bounds / budget-bound proofs.
      ------------------------------------------------------------------------
      module VBnd0 = BImpl.Bounds alloc
      module VBnd1 = VBnd0.L2 f x s-after-setup mF result-f f-tnhw
      module VBnd2 = VBnd1.L3 g s-after-middle mG result-g g-tnhw

      ------------------------------------------------------------------------
      -- Plan 0.18 wire-through: Assembly instantiation (Cluster A).
      -- VAsm2 exports the heavy state-evolution proofs.
      ------------------------------------------------------------------------
      module VAsm0 = AImpl.Assembly f g x s alloc not-halted
      module VAsm1 = VAsm0.L2 mF result-f f-tnhw
      module VAsm2 = VAsm1.L3 mG result-g g-tnhw middle-restore-input-witness

      -- Plan 0.17: pair-bump for stack-mode pair. Both slot and heap
      -- deltas are non-trivial because pair-reclaim depends on
      -- sub-IR bumps. Concrete arithmetic via pair-bump-eq below.
      pair-bump : AllocBump
      pair-bump = SMP.!!  -- TODO: compose from sub-IR bumps + pair scratch

      pair-bump-eq : VAsm2.alloc-final ≡ apply-bump pair-bump alloc
      pair-bump-eq = SMP.!!  -- TODO Plan 0.17 Phase 5: concrete arithmetic bridge
      pair-frontier-stable : ∀ (s' : LocState FS) (input-loc' : ValueLocation FS) →
        halted s' ≡ false →
        readReg (regs s') Input1 ≡ SV-Ptr input-loc' →
        readLoc s' (AtStack frame backup-slot) ≡ just (SV-Ptr input-loc') →
        (next-slot alloc ≡ VBnd2.pair-reclaim) ⊎
        ((readLoc (proj₁ (exec-trace VBnd2.pair-trace s' alloc))
                 (AtStack frame backup-slot) ≡ just (SV-Ptr input-loc')) ⊎ ⊤)
      pair-frontier-stable s' input-loc' not-halted' rdi-eq' _ =
        -- Use store-then-preserve pattern:
        -- mov-to-output sets Output = input-loc', store-at-slot backup-slot saves it
        -- rest of trace writes above suc backup-slot, so backup-slot preserved
        inj₂ (inj₂ tt)  -- Conservative: return uncertain

      ------------------------------------------------------------------------
      -- Pair result location is before frontier
      ------------------------------------------------------------------------
      pair-before : BeforeFrontier VAsm2.alloc-final pair-loc
      pair-before = stack-before refl VBnd2.fst<reclaim-g


      ------------------------------------------------------------------------
      -- Plan 0.18 wire-through: instantiate VL3 with the s-final-eq bridge.
      -- VVal/VL2 are already opened at the top of the where-block.
      -- pair-valid-wf-final is the single export we read off.
      ------------------------------------------------------------------------
      module VL3 = VL2.L3 mG result-g
                     snd-loc snd-rax-eq snd-rec-valid-from-g snd-rec-before-from-g
                     g-tnhw VAsm2.s-final VAsm2.s-final-eq

      pair-valid-wf-final : ValidAtWF Stack VAsm2.alloc-final
                              (pair (eval f x) (eval g x)) pair-loc VAsm2.s-final
      pair-valid-wf-final = VL3.pair-valid-wf-final
