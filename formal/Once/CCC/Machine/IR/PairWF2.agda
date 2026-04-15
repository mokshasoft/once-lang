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
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; n≤1+n; +-comm; +-assoc; +-suc; +-identityʳ; +-monoˡ-≤; +-monoʳ-≤; <-≤-trans; <⇒≤; <⇒≢; m≤m⊔n; m≤n⊔m; ⊔-lub; _<?_; ≮⇒≥)
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
open import Once.Semantics.Machine using (⟦_⟧)
open import Once.CCC.IR
open import Once.CCC.Eval using (PrimSem; eval)
open import Once.CCC.IR.Size
open import Once.CCC.IR.Stack
open import Once.CCC.Machine.Allocation hiding (AllocMode)
open import Once.CCC.Machine.ClosureWellFormed

-- Import SMPrimitives qualified for memory reasoning primitives
import Once.CCC.Machine.SMPrimitives as SMP

------------------------------------------------------------------------
-- PairWF2 Implementation
------------------------------------------------------------------------

module PairWF2Impl {FS : FrameSemantics} (program-bound : ℕ) (primSem : PrimSem) where
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

  -- Types from ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound primSem
    using (ValidAtWF; IRResultAWF; RecDispatcherWF;
           valid-pair-wf;
           validityWF-mem-only; validityWF-mem-preserved;
           validityWF-mem-preserved-in-regions;
           validityWF-frontier-advance;
           validityWF-trace-preserves;
           irresult-mem-preserved)

  ------------------------------------------------------------------------
  -- run-pair: Main implementation
  ------------------------------------------------------------------------

  run-pair : ∀ {A B C} (mIn : AllocMode) (f : IR A B) (g : IR A C) (m : AllocMode)
    (rec-wf : RecDispatcherWF (ir-size (⟨ f , g ⟩ Heap)))
    (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input ≡ input-loc →
    IRResultAWF m (⟨ f , g ⟩ m) x s alloc

  run-pair {A} {B} {C} mIn f g m rec-wf x input-loc s alloc
           input-valid-wf input-before not-halted rdi-eq =
    record
      { result-loc = pair-loc
      ; final-state = s-final
      ; final-alloc = alloc-final
      ; trace = pair-trace
      ; trace-correct = refl  -- s-final DEFINED by trace
      ; result-valid-wf = pair-valid-wf-final
      ; result-before = pair-before
      ; rax-is-result = rax-eq
      ; not-halted = not-halted-final
      ; frame-preserved = refl
      ; slot-monotone = slot-monotone-pair
      ; heap-monotone = ≤-refl
      -- Phase 7: Removed reclaimable-slot, reclaim-monotone, reclaim-bounded, reclaim-size-bound
      ; reclaim-preserves-result = pair-before
      ; reclaim-preserves-validity = pair-valid-wf-final
      ; max-slot-written = pair-max-slot
      ; max-slot-geq-final = pair-max-slot-geq-final
      ; max-slot-usage-bound = pair-max-slot-bound
      ; slot-stays-in-budget = pair-slot-stays-in-budget
      ; frontier-slot-stable = pair-frontier-stable
      ; trace-writes-above = pair-trace-writes-above
      ; trace-slot-reads-above = pair-trace-slot-reads-above
      ; trace-writes-below = pair-trace-writes-below
      ; trace-slot-reads-below = pair-trace-slot-reads-below
      -- Note: trace-preserves-capacity removed in Phase 3
      ; trace-no-heap-writes = pair-trace-no-heap-writes
      ; trace-preserves-halted = pair-trace-preserves-halted
      ; scratch-bounded = pair-scratch-bounded
      }
    where
      ------------------------------------------------------------------------
      -- Slot Layout (pure arithmetic, no functions)
      --
      -- backup-slot = next-slot alloc       -- stores input pointer for g
      -- fst-slot    = suc backup-slot       -- stores f's result pointer
      -- snd-slot    = suc fst-slot          -- stores g's result pointer
      -- f-start     = suc snd-slot          -- f writes to [f-start, max-f)
      -- g-start     = reclaim-f             -- g writes to [reclaim-f, max-g)
      ------------------------------------------------------------------------
      rf = ir-stack-requirement f
      rg = ir-stack-requirement g
      req-pair = ir-stack-requirement (⟨ f , g ⟩ m)
      frame = current-frame alloc
      backup-slot = next-slot alloc
      fst-slot = suc backup-slot
      snd-slot = suc fst-slot
      f-start = suc snd-slot  -- = suc (suc (suc backup-slot))

      pair-loc : ValueLocation FS
      pair-loc = OnStack frame fst-slot

      ------------------------------------------------------------------------
      -- Allocation state after reserving pair slots
      -- f and g start from f-start = suc snd-slot
      ------------------------------------------------------------------------
      alloc-after-pair-slots : AllocState {FS}
      alloc-after-pair-slots = record alloc { next-slot = f-start }

      ------------------------------------------------------------------------
      -- Capacity derivations
      ------------------------------------------------------------------------
      -- Input validity at advanced frontier
      ------------------------------------------------------------------------
      input-before-at-f-start : BeforeFrontier alloc-after-pair-slots input-loc
      input-before-at-f-start = frontier-monotone alloc alloc-after-pair-slots refl
                                  (≤-trans (n≤1+n backup-slot) (≤-trans (n≤1+n fst-slot) (n≤1+n snd-slot)))
                                  ≤-refl input-loc input-before

      input-valid-wf-at-f-start : ValidAtWF mIn alloc-after-pair-slots x input-loc s
      input-valid-wf-at-f-start = validityWF-frontier-advance x input-loc s refl
                                    (≤-trans (n≤1+n backup-slot) (≤-trans (n≤1+n fst-slot) (n≤1+n snd-slot)))
                                    ≤-refl input-valid-wf

      bf-to-after-pair-slots : ∀ loc → BeforeFrontier alloc loc → BeforeFrontier alloc-after-pair-slots loc
      bf-to-after-pair-slots loc bf = frontier-monotone alloc alloc-after-pair-slots refl
                                        (≤-trans (n≤1+n backup-slot) (≤-trans (n≤1+n fst-slot) (n≤1+n snd-slot)))
                                        ≤-refl loc bf

      ------------------------------------------------------------------------
      -- Run f via recursive dispatch
      ------------------------------------------------------------------------
      f-exec-result : ∃[ mOut ] IRResultAWF mOut f x s alloc-after-pair-slots
      f-exec-result = rec-wf mIn f (⟨,⟩-f-smaller f g {m}) x input-loc s alloc-after-pair-slots
                        input-valid-wf-at-f-start input-before-at-f-start not-halted rdi-eq
      mF = proj₁ f-exec-result
      result-f = proj₂ f-exec-result
      s₁ = IRResultAWF.final-state result-f
      fst-loc = IRResultAWF.result-loc result-f
      f-trace = IRResultAWF.trace result-f

      ------------------------------------------------------------------------
      -- Reclaim after f (Phase 7: use next-slot final-alloc instead of reclaimable-slot)
      ------------------------------------------------------------------------
      reclaim-f = next-slot (IRResultAWF.final-alloc result-f)

      reclaim-f-bound : reclaim-f ≤ f-start +ℕ rf
      reclaim-f-bound = IRResultAWF.slot-stays-in-budget result-f

      reclaim-f-above-f-start : f-start ≤ reclaim-f
      reclaim-f-above-f-start = IRResultAWF.slot-monotone result-f

      alloc-after-f-reclaim : AllocState {FS}
      alloc-after-f-reclaim = record alloc { next-slot = reclaim-f }

      ------------------------------------------------------------------------
      -- Input validity for g (after restoring from backup-slot)
      ------------------------------------------------------------------------
      input-before-at-reclaim-f : BeforeFrontier alloc-after-f-reclaim input-loc
      input-before-at-reclaim-f = frontier-monotone alloc alloc-after-f-reclaim refl
                                    (≤-trans (n≤1+n backup-slot)
                                      (≤-trans (n≤1+n fst-slot)
                                        (≤-trans (n≤1+n snd-slot) reclaim-f-above-f-start)))
                                    ≤-refl input-loc input-before

      -- Input validity at s₁ (memory preserved through f-trace for input-loc)
      input-valid-wf-s1 : ValidAtWF mIn alloc x input-loc s₁
      input-valid-wf-s1 = validityWF-mem-preserved x input-loc s s₁ input-before
                            (λ loc bf → irresult-mem-preserved result-f loc (bf-to-after-pair-slots loc bf))
                            input-valid-wf

      input-valid-wf-at-reclaim-f : ValidAtWF mIn alloc-after-f-reclaim x input-loc s₁
      input-valid-wf-at-reclaim-f = validityWF-frontier-advance x input-loc s₁ refl
                                      (≤-trans (n≤1+n backup-slot)
                                        (≤-trans (n≤1+n fst-slot)
                                          (≤-trans (n≤1+n snd-slot) reclaim-f-above-f-start)))
                                      ≤-refl input-valid-wf-s1

      -- Restore input register for g
      s₁' = record s₁ { regs = writeReg (regs s₁) Input input-loc }
      rdi-eq₁ : readReg (regs s₁') Input ≡ input-loc
      rdi-eq₁ = writeReg-same (regs s₁) Input input-loc

      input-valid-wf₁' : ValidAtWF mIn alloc-after-f-reclaim x input-loc s₁'
      input-valid-wf₁' = validityWF-mem-only x input-loc s₁ s₁' refl refl input-valid-wf-at-reclaim-f

      ------------------------------------------------------------------------
      -- Run g via recursive dispatch
      ------------------------------------------------------------------------
      g-exec-result : ∃[ mOut ] IRResultAWF mOut g x s₁' alloc-after-f-reclaim
      g-exec-result = rec-wf mIn g (⟨,⟩-g-smaller f g {m}) x input-loc s₁' alloc-after-f-reclaim
                        input-valid-wf₁' input-before-at-reclaim-f
                        (IRResultAWF.not-halted result-f) rdi-eq₁
      mG = proj₁ g-exec-result
      result-g = proj₂ g-exec-result
      s₂ = IRResultAWF.final-state result-g
      snd-loc = IRResultAWF.result-loc result-g
      g-trace = IRResultAWF.trace result-g

      ------------------------------------------------------------------------
      -- Reclaim after g (Phase 7: use next-slot final-alloc instead of reclaimable-slot)
      ------------------------------------------------------------------------
      reclaim-g = next-slot (IRResultAWF.final-alloc result-g)

      reclaim-g-bound : reclaim-g ≤ reclaim-f +ℕ rg
      reclaim-g-bound = IRResultAWF.slot-stays-in-budget result-g

      ------------------------------------------------------------------------
      -- Final allocation
      ------------------------------------------------------------------------
      alloc-final : AllocState {FS}
      alloc-final = record alloc { next-slot = reclaim-g }

      pair-reclaim = reclaim-g

      pair-reclaim-monotone : next-slot alloc ≤ pair-reclaim
      pair-reclaim-monotone = ≤-trans (n≤1+n backup-slot)
                                (≤-trans (n≤1+n fst-slot)
                                  (≤-trans (n≤1+n snd-slot)
                                    (≤-trans reclaim-f-above-f-start (IRResultAWF.slot-monotone result-g))))

      ------------------------------------------------------------------------
      -- Trace Construction
      --
      -- pair-trace =
      --   mov-to-output ∷ store-at-slot backup-slot ∷  -- backup input
      --   f-trace ++                                    -- execute f
      --   store-at-slot fst-slot ∷ restore-input backup-slot ∷  -- save f result, restore input
      --   g-trace ++                                    -- execute g
      --   store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []  -- save g result, compute pair addr
      ------------------------------------------------------------------------
      pair-trace : AbstractTrace
      pair-trace = mov-to-output ∷ store-at-slot backup-slot ∷
                   f-trace ++
                   store-at-slot fst-slot ∷ restore-input backup-slot ∷
                   g-trace ++
                   store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []

      ------------------------------------------------------------------------
      -- s-final DEFINED by trace (makes trace-correct = refl)
      ------------------------------------------------------------------------
      s-final : LocState FS
      s-final = proj₁ (exec-trace pair-trace s alloc)

      ------------------------------------------------------------------------
      -- Trace decomposition: segments and intermediate states
      ------------------------------------------------------------------------

      -- Trace segments
      setup-trace : AbstractTrace
      setup-trace = mov-to-output ∷ store-at-slot backup-slot ∷ []

      middle-trace : AbstractTrace
      middle-trace = store-at-slot fst-slot ∷ restore-input backup-slot ∷ []

      final-trace : AbstractTrace
      final-trace = store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []

      -- Intermediate states (value bindings, not functions)
      s-after-setup : LocState FS
      s-after-setup = proj₁ (exec-trace setup-trace s alloc)

      alloc-after-setup : AllocState {FS}
      alloc-after-setup = proj₂ (exec-trace setup-trace s alloc)

      s-after-f : LocState FS
      s-after-f = proj₁ (exec-trace f-trace s-after-setup alloc-after-setup)

      alloc-after-f : AllocState {FS}
      alloc-after-f = proj₂ (exec-trace f-trace s-after-setup alloc-after-setup)

      s-after-middle : LocState FS
      s-after-middle = proj₁ (exec-trace middle-trace s-after-f alloc-after-f)

      alloc-after-middle : AllocState {FS}
      alloc-after-middle = proj₂ (exec-trace middle-trace s-after-f alloc-after-f)

      s-after-g : LocState FS
      s-after-g = proj₁ (exec-trace g-trace s-after-middle alloc-after-middle)

      alloc-after-g : AllocState {FS}
      alloc-after-g = proj₂ (exec-trace g-trace s-after-middle alloc-after-middle)

      s-after-final : LocState FS
      s-after-final = proj₁ (exec-trace final-trace s-after-g alloc-after-g)

      ------------------------------------------------------------------------
      -- Trace predicates from sub-IRs
      ------------------------------------------------------------------------
      f-twa : TraceWritesAbove f-start f-trace
      f-twa = IRResultAWF.trace-writes-above result-f

      f-twb : TraceWritesBelow (IRResultAWF.max-slot-written result-f) f-trace
      f-twb = IRResultAWF.trace-writes-below result-f

      f-tnhw : TraceNoHeapWrites f-trace
      f-tnhw = IRResultAWF.trace-no-heap-writes result-f

      -- Note: f-tpc removed in Phase 3

      f-tph : TracePreservesHaltedP f-trace
      f-tph = IRResultAWF.trace-preserves-halted result-f

      g-twa : TraceWritesAbove reclaim-f g-trace
      g-twa = IRResultAWF.trace-writes-above result-g

      g-twb : TraceWritesBelow (IRResultAWF.max-slot-written result-g) g-trace
      g-twb = IRResultAWF.trace-writes-below result-g

      g-tnhw : TraceNoHeapWrites g-trace
      g-tnhw = IRResultAWF.trace-no-heap-writes result-g

      -- Note: g-tpc removed in Phase 3

      g-tph : TracePreservesHaltedP g-trace
      g-tph = IRResultAWF.trace-preserves-halted result-g

      ------------------------------------------------------------------------
      -- Halted preservation and trace equality
      ------------------------------------------------------------------------
      setup-tph : TracePreservesHaltedP setup-trace
      setup-tph = tph-∷ iph-mov-to-output (tph-∷ iph-store-at-slot tph-[])

      not-halted-after-setup : halted s-after-setup ≡ false
      not-halted-after-setup = exec-trace-preserves-halted setup-trace s alloc not-halted setup-tph

      not-halted-after-f : halted s-after-f ≡ false
      not-halted-after-f = exec-trace-preserves-halted f-trace s-after-setup alloc-after-setup
                             not-halted-after-setup f-tph

      middle-tph : TracePreservesHaltedP middle-trace
      middle-tph = tph-∷ iph-store-at-slot (tph-∷ iph-restore-input tph-[])

      not-halted-after-middle : halted s-after-middle ≡ false
      not-halted-after-middle = exec-trace-preserves-halted middle-trace s-after-f alloc-after-f
                                  not-halted-after-f middle-tph

      not-halted-after-g : halted s-after-g ≡ false
      not-halted-after-g = exec-trace-preserves-halted g-trace s-after-middle alloc-after-middle
                             not-halted-after-middle g-tph

      final-tph : TracePreservesHaltedP final-trace
      final-tph = tph-∷ iph-store-at-slot (tph-∷ iph-lea-slot tph-[])

      -- s-final ≡ s-after-final via trace decomposition
      s-final-eq : s-final ≡ s-after-final
      s-final-eq =
        let rest-after-setup = f-trace ++ store-at-slot fst-slot ∷ restore-input backup-slot ∷
                               g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []
            rest-after-f = store-at-slot fst-slot ∷ restore-input backup-slot ∷
                           g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []
            rest-after-middle = g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []
            step1 = exec-trace-append setup-trace rest-after-setup s alloc
            step2 = exec-trace-append f-trace rest-after-f s-after-setup alloc-after-setup
            step3 = exec-trace-append middle-trace rest-after-middle s-after-f alloc-after-f
            step4 = exec-trace-append g-trace final-trace s-after-middle alloc-after-middle
        in cong proj₁ (trans step1 (trans step2 (trans step3 step4)))

      -- Frame preserved through trace
      frame-preserved-through : current-frame alloc-after-g ≡ frame
      frame-preserved-through =
        trans (exec-trace-preserves-frame g-trace s-after-middle alloc-after-middle)
        (trans (exec-trace-preserves-frame middle-trace s-after-f alloc-after-f)
        (trans (exec-trace-preserves-frame f-trace s-after-setup alloc-after-setup)
               (exec-trace-preserves-frame setup-trace s alloc)))

      ------------------------------------------------------------------------
      -- Max slot tracking
      ------------------------------------------------------------------------
      max-slot-f = IRResultAWF.max-slot-written result-f
      max-slot-g = IRResultAWF.max-slot-written result-g
      pair-max-slot = max-slot-f ⊔ max-slot-g

      pair-max-slot-geq-final : pair-reclaim ≤ pair-max-slot
      pair-max-slot-geq-final = ≤-trans (IRResultAWF.max-slot-geq-final result-g) (m≤n⊔m max-slot-f max-slot-g)

      max-slot-f≤pair : max-slot-f ≤ pair-max-slot
      max-slot-f≤pair = m≤m⊔n max-slot-f max-slot-g

      max-slot-g≤pair : max-slot-g ≤ pair-max-slot
      max-slot-g≤pair = m≤n⊔m max-slot-f max-slot-g

      ------------------------------------------------------------------------
      -- Key bounds for slot preservation
      ------------------------------------------------------------------------
      fst-slot<reclaim-f : fst-slot < reclaim-f
      fst-slot<reclaim-f = ≤-trans (n≤1+n snd-slot) reclaim-f-above-f-start

      snd-slot<reclaim-f : snd-slot < reclaim-f
      snd-slot<reclaim-f = reclaim-f-above-f-start

      fst<reclaim-g : fst-slot < reclaim-g
      fst<reclaim-g = <-≤-trans fst-slot<reclaim-f (IRResultAWF.slot-monotone result-g)

      snd<reclaim-g : snd-slot < reclaim-g
      snd<reclaim-g = <-≤-trans snd-slot<reclaim-f (IRResultAWF.slot-monotone result-g)

      ------------------------------------------------------------------------
      -- Trace bounds (write above/below)
      ------------------------------------------------------------------------
      -- Weakened: f writes above suc backup-slot
      f-twa-weak : TraceWritesAbove (suc backup-slot) f-trace
      f-twa-weak = trace-writes-above-mono (suc backup-slot) f-start f-trace
                     (≤-trans (n≤1+n fst-slot) (n≤1+n snd-slot)) f-twa

      -- g writes above reclaim-f, weaken to suc backup-slot
      g-twa-weak : TraceWritesAbove (suc backup-slot) g-trace
      g-twa-weak = trace-writes-above-mono (suc backup-slot) reclaim-f g-trace
                     (≤-trans (n≤1+n fst-slot) (≤-trans (n≤1+n snd-slot) reclaim-f-above-f-start))
                     g-twa

      -- Build pair-trace-writes-above incrementally
      backup≤fst : backup-slot ≤ fst-slot
      backup≤fst = n≤1+n backup-slot

      backup≤snd : backup-slot ≤ snd-slot
      backup≤snd = ≤-trans backup≤fst (n≤1+n fst-slot)

      backup≤reclaim-f : backup-slot ≤ reclaim-f
      backup≤reclaim-f = ≤-trans (n≤1+n backup-slot)
                           (≤-trans (n≤1+n fst-slot) (≤-trans (n≤1+n snd-slot) reclaim-f-above-f-start))

      -- Final segment: store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []
      final-seg-twa : TraceWritesAbove backup-slot (store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
      final-seg-twa = backup≤snd , tt

      -- g + final
      g-plus-final-twa : TraceWritesAbove backup-slot (g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
      g-plus-final-twa = trace-writes-above-append backup-slot g-trace (store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
                           (trace-writes-above-mono backup-slot reclaim-f g-trace backup≤reclaim-f g-twa)
                           final-seg-twa

      -- middle + g + final
      middle-plus-twa : TraceWritesAbove backup-slot
                          (store-at-slot fst-slot ∷ restore-input backup-slot ∷ g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
      middle-plus-twa = backup≤fst , g-plus-final-twa

      -- f + middle + g + final
      f-plus-twa : TraceWritesAbove backup-slot
                     (f-trace ++ store-at-slot fst-slot ∷ restore-input backup-slot ∷ g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
      f-plus-twa = trace-writes-above-append backup-slot f-trace
                     (store-at-slot fst-slot ∷ restore-input backup-slot ∷ g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
                     (trace-writes-above-mono backup-slot (suc backup-slot) f-trace (n≤1+n backup-slot) f-twa-weak)
                     middle-plus-twa

      pair-trace-writes-above : TraceWritesAbove backup-slot pair-trace
      pair-trace-writes-above = ≤-refl , f-plus-twa

      ------------------------------------------------------------------------
      -- Trace bounds (write below)
      ------------------------------------------------------------------------
      fst<bound : fst-slot < pair-max-slot
      fst<bound = <-≤-trans fst-slot<reclaim-f
                    (≤-trans (IRResultAWF.max-slot-geq-final result-f) max-slot-f≤pair)

      snd<bound : snd-slot < pair-max-slot
      snd<bound = <-≤-trans snd-slot<reclaim-f
                    (≤-trans (IRResultAWF.max-slot-geq-final result-f) max-slot-f≤pair)

      backup<bound : backup-slot < pair-max-slot
      backup<bound = <-≤-trans (s≤s backup≤fst) fst<bound

      final-seg-twb : TraceWritesBelow pair-max-slot (store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
      final-seg-twb = snd<bound , tt

      g-plus-final-twb : TraceWritesBelow pair-max-slot (g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
      g-plus-final-twb = trace-writes-below-append pair-max-slot g-trace (store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
                           (trace-writes-below-mono max-slot-g pair-max-slot g-trace max-slot-g≤pair g-twb)
                           final-seg-twb

      middle-plus-twb : TraceWritesBelow pair-max-slot
                          (store-at-slot fst-slot ∷ restore-input backup-slot ∷ g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
      middle-plus-twb = fst<bound , g-plus-final-twb

      f-plus-twb : TraceWritesBelow pair-max-slot
                     (f-trace ++ store-at-slot fst-slot ∷ restore-input backup-slot ∷ g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
      f-plus-twb = trace-writes-below-append pair-max-slot f-trace
                     (store-at-slot fst-slot ∷ restore-input backup-slot ∷ g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
                     (trace-writes-below-mono max-slot-f pair-max-slot f-trace max-slot-f≤pair f-twb)
                     middle-plus-twb

      pair-trace-writes-below : TraceWritesBelow pair-max-slot pair-trace
      pair-trace-writes-below = backup<bound , f-plus-twb

      ------------------------------------------------------------------------
      -- Trace read bounds (similar structure)
      ------------------------------------------------------------------------
      f-tsra : TraceSlotReadsAbove f-start f-trace
      f-tsra = IRResultAWF.trace-slot-reads-above result-f

      g-tsra : TraceSlotReadsAbove reclaim-f g-trace
      g-tsra = IRResultAWF.trace-slot-reads-above result-g

      f-tsrb : TraceSlotReadsBelow max-slot-f f-trace
      f-tsrb = IRResultAWF.trace-slot-reads-below result-f

      g-tsrb : TraceSlotReadsBelow max-slot-g g-trace
      g-tsrb = IRResultAWF.trace-slot-reads-below result-g

      final-seg-rsra : TraceSlotReadsAbove backup-slot (store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
      final-seg-rsra = tt

      g-plus-final-rsra : TraceSlotReadsAbove backup-slot (g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
      g-plus-final-rsra = trace-slot-reads-above-append backup-slot g-trace (store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
                            (trace-slot-reads-above-mono backup-slot reclaim-f g-trace backup≤reclaim-f g-tsra)
                            final-seg-rsra

      middle-plus-rsra : TraceSlotReadsAbove backup-slot
                           (store-at-slot fst-slot ∷ restore-input backup-slot ∷ g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
      middle-plus-rsra = ≤-refl , g-plus-final-rsra  -- restore-input reads backup-slot >= backup-slot

      f-plus-rsra : TraceSlotReadsAbove backup-slot
                      (f-trace ++ store-at-slot fst-slot ∷ restore-input backup-slot ∷ g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
      f-plus-rsra = trace-slot-reads-above-append backup-slot f-trace
                      (store-at-slot fst-slot ∷ restore-input backup-slot ∷ g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
                      (trace-slot-reads-above-mono backup-slot (suc backup-slot) f-trace (n≤1+n backup-slot)
                        (trace-slot-reads-above-mono (suc backup-slot) f-start f-trace
                          (≤-trans (n≤1+n fst-slot) (n≤1+n snd-slot)) f-tsra))
                      middle-plus-rsra

      pair-trace-slot-reads-above : TraceSlotReadsAbove backup-slot pair-trace
      pair-trace-slot-reads-above = f-plus-rsra

      final-seg-rsrb : TraceSlotReadsBelow pair-max-slot (store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
      final-seg-rsrb = tt

      g-plus-final-rsrb : TraceSlotReadsBelow pair-max-slot (g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
      g-plus-final-rsrb = trace-slot-reads-below-append pair-max-slot g-trace (store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
                            (trace-slot-reads-below-mono max-slot-g pair-max-slot g-trace max-slot-g≤pair g-tsrb)
                            final-seg-rsrb

      middle-plus-rsrb : TraceSlotReadsBelow pair-max-slot
                           (store-at-slot fst-slot ∷ restore-input backup-slot ∷ g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
      middle-plus-rsrb = backup<bound , g-plus-final-rsrb  -- restore-input reads backup-slot < pair-max-slot

      f-plus-rsrb : TraceSlotReadsBelow pair-max-slot
                      (f-trace ++ store-at-slot fst-slot ∷ restore-input backup-slot ∷ g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
      f-plus-rsrb = trace-slot-reads-below-append pair-max-slot f-trace
                      (store-at-slot fst-slot ∷ restore-input backup-slot ∷ g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
                      (trace-slot-reads-below-mono max-slot-f pair-max-slot f-trace max-slot-f≤pair f-tsrb)
                      middle-plus-rsrb

      pair-trace-slot-reads-below : TraceSlotReadsBelow pair-max-slot pair-trace
      pair-trace-slot-reads-below = f-plus-rsrb

      ------------------------------------------------------------------------
      -- Trace no heap writes
      ------------------------------------------------------------------------
      pair-trace-no-heap-writes : TraceNoHeapWrites pair-trace
      pair-trace-no-heap-writes =
        trace-no-heap-writes-append (mov-to-output ∷ store-at-slot backup-slot ∷ [])
          (f-trace ++ store-at-slot fst-slot ∷ restore-input backup-slot ∷ g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
          tt
          (trace-no-heap-writes-append f-trace
            (store-at-slot fst-slot ∷ restore-input backup-slot ∷ g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
            f-tnhw
            (trace-no-heap-writes-append g-trace (store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []) g-tnhw tt))

      -- Note: pair-trace-preserves-capacity removed in Phase 3

      ------------------------------------------------------------------------
      -- Trace preserves halted
      ------------------------------------------------------------------------
      pair-trace-preserves-halted : TracePreservesHaltedP pair-trace
      pair-trace-preserves-halted =
        tph-∷ iph-mov-to-output
        (tph-∷ iph-store-at-slot
        (tph-++ f-tph
        (tph-∷ iph-store-at-slot
        (tph-∷ iph-restore-input
        (tph-++ g-tph
        (tph-∷ iph-store-at-slot
        (tph-∷ iph-lea-slot tph-[])))))))

      ------------------------------------------------------------------------
      -- Slot monotone for pair
      ------------------------------------------------------------------------
      slot-monotone-pair : next-slot alloc ≤ next-slot alloc-final
      slot-monotone-pair = pair-reclaim-monotone

      ------------------------------------------------------------------------
      -- Pair reclaim size bound
      ------------------------------------------------------------------------
      sss-rf-rg≡req-pair : (f-start +ℕ rf) +ℕ rg ≡ backup-slot +ℕ req-pair
      sss-rf-rg≡req-pair =
        let step1 : (((1 +ℕ rf) +ℕ rg) +ℕ 2) ≡ 3 +ℕ (rf +ℕ rg)
            step1 = trans (+-assoc (1 +ℕ rf) rg 2)
                    (trans (cong ((1 +ℕ rf) +ℕ_) (+-comm rg 2))
                    (trans (sym (+-assoc (1 +ℕ rf) 2 rg))
                    (trans (cong (_+ℕ rg) (+-assoc 1 rf 2))
                    (trans (cong (λ x → (1 +ℕ x) +ℕ rg) (+-comm rf 2))
                    (trans (cong (_+ℕ rg) (sym (+-assoc 1 2 rf))) (+-assoc 3 rf rg))))))
            step2 : backup-slot +ℕ (3 +ℕ (rf +ℕ rg)) ≡ suc (suc (suc (backup-slot +ℕ (rf +ℕ rg))))
            step2 = trans (sym (+-assoc backup-slot 3 (rf +ℕ rg)))
                      (trans (cong (_+ℕ (rf +ℕ rg)) (+-comm backup-slot 3))
                        (+-assoc 3 backup-slot (rf +ℕ rg)))
            step3 : (backup-slot +ℕ rf) +ℕ rg ≡ backup-slot +ℕ (rf +ℕ rg)
            step3 = +-assoc backup-slot rf rg
        in trans (cong (λ x → suc (suc (suc x))) step3)
             (trans (sym step2) (cong (backup-slot +ℕ_) (sym step1)))

      reclaim-g≤-rf-rg : reclaim-g ≤ (f-start +ℕ rf) +ℕ rg
      reclaim-g≤-rf-rg = ≤-trans reclaim-g-bound (+-monoˡ-≤ rg reclaim-f-bound)

      pair-reclaim-size-bound : pair-reclaim ≤ backup-slot +ℕ req-pair
      pair-reclaim-size-bound = ≤-trans reclaim-g≤-rf-rg
        (subst (((f-start +ℕ rf) +ℕ rg) ≤_) sss-rf-rg≡req-pair ≤-refl)

      ------------------------------------------------------------------------
      -- Max slot bound
      ------------------------------------------------------------------------
      pair-max-slot-bound : pair-max-slot ≤ backup-slot +ℕ req-pair
      pair-max-slot-bound =
        ⊔-lub max-slot-f-bound max-slot-g-bound
        where
          max-slot-f-usage : max-slot-f ≤ f-start +ℕ rf
          max-slot-f-usage = IRResultAWF.max-slot-usage-bound result-f

          max-slot-g-usage : max-slot-g ≤ reclaim-f +ℕ rg
          max-slot-g-usage = IRResultAWF.max-slot-usage-bound result-g

          max-slot-f-bound : max-slot-f ≤ backup-slot +ℕ req-pair
          max-slot-f-bound = ≤-trans max-slot-f-usage
            (≤-trans (m≤m+n (f-start +ℕ rf) rg)
                     (subst (((f-start +ℕ rf) +ℕ rg) ≤_) sss-rf-rg≡req-pair ≤-refl))

          max-slot-g-bound : max-slot-g ≤ backup-slot +ℕ req-pair
          max-slot-g-bound = ≤-trans max-slot-g-usage
            (≤-trans (+-monoˡ-≤ rg reclaim-f-bound)
                     (subst (((f-start +ℕ rf) +ℕ rg) ≤_) sss-rf-rg≡req-pair ≤-refl))

      -- Stack discipline: pair stays within budget
      -- alloc-final has next-slot = reclaim-g = pair-reclaim
      -- pair-reclaim-size-bound proves: pair-reclaim ≤ backup-slot + req-pair
      -- backup-slot = next-slot alloc, so this is exactly slot-stays-in-budget
      pair-slot-stays-in-budget : next-slot alloc-final ≤ backup-slot +ℕ req-pair
      pair-slot-stays-in-budget = pair-reclaim-size-bound

      ------------------------------------------------------------------------
      -- Scratch bounded
      --
      -- pair-max-slot = max-slot-f ⊔ max-slot-g
      -- Need: pair-max-slot ≤ next-slot alloc-final +ℕ req-pair
      --
      -- From f's scratch-bounded: max-slot-f ≤ next-slot alloc₁ +ℕ rf
      --   where alloc₁ = IRResultAWF.final-alloc result-f
      -- From g's scratch-bounded: max-slot-g ≤ next-slot alloc-g +ℕ rg
      --   where alloc-g = IRResultAWF.final-alloc result-g
      --
      -- alloc-final has next-slot = reclaim-g = pair-reclaim
      -- Since alloc-final ≥ alloc (slot monotone) and req-pair covers rf + rg + overhead,
      -- we can bound both max-slot-f and max-slot-g.
      ------------------------------------------------------------------------
      pair-scratch-bounded : pair-max-slot ≤ next-slot alloc-final +ℕ req-pair
      pair-scratch-bounded =
        ⊔-lub f-scratch-bound g-scratch-bound
        where
          -- f's scratch-bounded: max-slot-f ≤ next-slot alloc₁ +ℕ rf
          -- where alloc₁ is f's final alloc (starting from f-start)
          -- Since next-slot alloc-final = reclaim-g ≥ f-start (transitively through reclaim-f),
          -- we have: max-slot-f ≤ (f-start +ℕ rf) ≤ backup-slot +ℕ req-pair ≤ reclaim-g +ℕ req-pair
          f-scratch-bound : max-slot-f ≤ next-slot alloc-final +ℕ req-pair
          f-scratch-bound =
            let max-f-bound : max-slot-f ≤ backup-slot +ℕ req-pair
                max-f-bound = ≤-trans (IRResultAWF.max-slot-usage-bound result-f)
                                (≤-trans (m≤m+n (f-start +ℕ rf) rg)
                                  (subst (((f-start +ℕ rf) +ℕ rg) ≤_) sss-rf-rg≡req-pair ≤-refl))
            in ≤-trans max-f-bound (+-monoˡ-≤ req-pair pair-reclaim-monotone)

          -- g's scratch-bounded: max-slot-g ≤ next-slot alloc-g +ℕ rg
          -- where alloc-g = IRResultAWF.final-alloc result-g
          -- next-slot alloc-g = next-slot alloc-final since alloc-final = alloc-g (with reclaim)
          -- Actually, alloc-final has next-slot = reclaim-g, and g ran on alloc-after-f-reclaim
          g-scratch-bound : max-slot-g ≤ next-slot alloc-final +ℕ req-pair
          g-scratch-bound =
            let max-g-bound : max-slot-g ≤ backup-slot +ℕ req-pair
                max-g-bound = ≤-trans (IRResultAWF.max-slot-usage-bound result-g)
                                (≤-trans (+-monoˡ-≤ rg reclaim-f-bound)
                                  (subst (((f-start +ℕ rf) +ℕ rg) ≤_) sss-rf-rg≡req-pair ≤-refl))
            in ≤-trans max-g-bound (+-monoˡ-≤ req-pair pair-reclaim-monotone)

      ------------------------------------------------------------------------
      -- Memory preservation (using positive write bounds)
      ------------------------------------------------------------------------
      mem-preserved-pair : ∀ loc → BeforeFrontier alloc loc → readLoc s-final loc ≡ readLoc s loc
      mem-preserved-pair (OnStack f' k) (stack-before f'≡cf k<next) =
        -- k < next-slot alloc = backup-slot, so slot k is below write region
        subst (λ f → readLoc s-final (OnStack f k) ≡ readLoc s (OnStack f k))
              (sym f'≡cf)
              (exec-trace-preserves-slot-below pair-trace s alloc backup-slot k
                 pair-trace-writes-above pair-trace-no-heap-writes k<next)
      mem-preserved-pair (OnStack f' k) (stack-ancestor cf≺f' _) =
        -- f' is an ancestor frame
        exec-trace-preserves-ancestor pair-trace s alloc f' k cf≺f' pair-trace-no-heap-writes
      mem-preserved-pair (OnHeap h) (heap-before _) =
        -- Heap location
        exec-trace-preserves-heap-loc pair-trace s alloc h pair-trace-no-heap-writes

      ------------------------------------------------------------------------
      -- Frontier slot stability
      ------------------------------------------------------------------------
      pair-frontier-stable : ∀ (s' : LocState FS) (input-loc' : ValueLocation FS) →
        halted s' ≡ false →
        readReg (regs s') Input ≡ input-loc' →
        readLoc s' (OnStack frame backup-slot) ≡ just input-loc' →
        (next-slot alloc ≡ pair-reclaim) ⊎
        ((readLoc (proj₁ (exec-trace pair-trace s' alloc))
                 (OnStack frame backup-slot) ≡ just input-loc') ⊎ ⊤)
      pair-frontier-stable s' input-loc' not-halted' rdi-eq' _ =
        -- Use store-then-preserve pattern:
        -- mov-to-output sets Output = input-loc', store-at-slot backup-slot saves it
        -- rest of trace writes above suc backup-slot, so backup-slot preserved
        inj₂ (inj₂ tt)  -- Conservative: return uncertain

      ------------------------------------------------------------------------
      -- Pair result location is before frontier
      ------------------------------------------------------------------------
      pair-before : BeforeFrontier alloc-final pair-loc
      pair-before = stack-before refl fst<reclaim-g

      ------------------------------------------------------------------------
      -- RAX contains result
      --
      -- final-trace = store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []
      -- The last instruction lea-slot fst-slot sets Output = OnStack frame fst-slot
      ------------------------------------------------------------------------
      -- Decompose final-trace execution
      s-after-snd-store : LocState FS
      s-after-snd-store = proj₁ (exec-abstract (store-at-slot snd-slot) s-after-g alloc-after-g)

      alloc-after-snd-store : AllocState {FS}
      alloc-after-snd-store = proj₂ (exec-abstract (store-at-slot snd-slot) s-after-g alloc-after-g)

      not-halted-after-snd-store : halted s-after-snd-store ≡ false
      not-halted-after-snd-store = trans (store-at-slot-halted snd-slot s-after-g alloc-after-g) not-halted-after-g

      frame-after-snd-store : current-frame alloc-after-snd-store ≡ frame
      frame-after-snd-store = trans (exec-abstract-preserves-frame (store-at-slot snd-slot) s-after-g alloc-after-g)
                                    frame-preserved-through

      -- final-trace decomposes as store then lea
      final-trace-decomp : exec-trace final-trace s-after-g alloc-after-g ≡
                           exec-trace (lea-slot fst-slot ∷ []) s-after-snd-store alloc-after-snd-store
      final-trace-decomp = exec-trace-cons (store-at-slot snd-slot) (lea-slot fst-slot ∷ [])
                             s-after-g alloc-after-g not-halted-after-g

      -- lea-slot as single instruction
      lea-single : exec-trace (lea-slot fst-slot ∷ []) s-after-snd-store alloc-after-snd-store ≡
                   exec-abstract (lea-slot fst-slot) s-after-snd-store alloc-after-snd-store
      lea-single = exec-trace-single (lea-slot fst-slot) s-after-snd-store alloc-after-snd-store not-halted-after-snd-store

      -- s-after-final = exec lea-slot ...
      s-after-final-eq : s-after-final ≡ proj₁ (exec-abstract (lea-slot fst-slot) s-after-snd-store alloc-after-snd-store)
      s-after-final-eq = cong proj₁ (trans final-trace-decomp lea-single)

      rax-eq : readReg (regs s-final) Output ≡ pair-loc
      rax-eq =
        let eq1 = cong (λ st → readReg (regs st) Output) s-final-eq
            eq2 = cong (λ st → readReg (regs st) Output) s-after-final-eq
            eq3 = lea-slot-result fst-slot s-after-snd-store alloc-after-snd-store
            eq4 = cong (λ f → OnStack f fst-slot) frame-after-snd-store
        in trans eq1 (trans eq2 (trans eq3 eq4))

      ------------------------------------------------------------------------
      -- Not halted after trace
      ------------------------------------------------------------------------
      not-halted-final : halted s-final ≡ false
      not-halted-final = exec-trace-preserves-halted pair-trace s alloc not-halted pair-trace-preserves-halted

      ------------------------------------------------------------------------
      -- fst-ptr and snd-ptr (memory holds correct values)
      --
      -- fst-ptr: store-at-slot fst-slot (in middle-trace) writes f's output
      -- snd-ptr: store-at-slot snd-slot (in final-trace) writes g's output
      ------------------------------------------------------------------------

      -- Output at s-after-f contains fst-loc
      -- Use exec-trace-output-deterministic: two executions of f-trace from states
      -- that agree on Input and memory in [f-start, max-slot-f) give same Output.
      --
      -- Execution 1: f-trace from s-after-setup with alloc-after-setup → s-after-f
      -- Execution 2: f-trace from s with alloc-after-pair-slots → s₁ (via trace-correct)
      -- IRResultAWF.rax-is-result gives Output at s��� = fst-loc

      -- Prerequisites for exec-trace-output-deterministic
      -- Frame equality: both allocators have same frame
      oaf-frame-eq : current-frame alloc-after-setup ≡ current-frame alloc-after-pair-slots
      oaf-frame-eq = trans (exec-trace-preserves-frame setup-trace s alloc) refl

      -- Input preservation through setup-trace (mov-to-output and store-at-slot don't modify Input)
      oaf-input-preserved : readReg (regs s-after-setup) Input ≡ readReg (regs s) Input
      oaf-input-preserved =
        let s₁' = proj₁ (exec-abstract mov-to-output s alloc)
            alloc₁' = proj₂ (exec-abstract mov-to-output s alloc)
            mov-preserves-input : readReg (regs s₁') Input ≡ readReg (regs s) Input
            mov-preserves-input = writeReg-preserves (regs s) Output Input (readReg (regs s) Input) (λ ())
            not-halted₁' = exec-abstract-preserves-halted mov-to-output s alloc not-halted iph-mov-to-output
            s₂' = proj₁ (exec-abstract (store-at-slot backup-slot) s₁' alloc₁')
            store-preserves-input : readReg (regs s₂') Input ≡ readReg (regs s₁') Input
            store-preserves-input = exec-abstract-store-at-slot-preserves-input backup-slot s₁' alloc₁'
            setup-decomp : exec-trace setup-trace s alloc ≡ exec-trace (store-at-slot backup-slot ∷ []) s₁' alloc₁'
            setup-decomp = exec-trace-cons mov-to-output (store-at-slot backup-slot ∷ []) s alloc not-halted
            store-single : exec-trace (store-at-slot backup-slot ∷ []) s₁' alloc₁' ≡ exec-abstract (store-at-slot backup-slot) s₁' alloc₁'
            store-single = exec-trace-single (store-at-slot backup-slot) s₁' alloc₁' not-halted₁'
            s-setup-eq : s-after-setup ≡ s₂'
            s-setup-eq = cong proj₁ (trans setup-decomp store-single)
        in trans (cong (λ st → readReg (regs st) Input) s-setup-eq)
                 (trans store-preserves-input mov-preserves-input)

      -- Memory agreement at [f-start, max-slot-f): setup writes only at backup-slot < f-start
      -- Both frames are equal to `frame`:
      -- - current-frame alloc-after-setup ≡ frame (via exec-trace-preserves-frame)
      -- - current-frame alloc-after-pair-slots ≡ frame (by definition, only next-slot changed)
      oaf-frame-setup : current-frame alloc-after-setup ≡ frame
      oaf-frame-setup = exec-trace-preserves-frame setup-trace s alloc

      oaf-frame-pair-slots : current-frame alloc-after-pair-slots ≡ frame
      oaf-frame-pair-slots = refl

      oaf-mem-agree : ∀ slot → f-start ≤ slot → slot < max-slot-f →
        readLoc s-after-setup (OnStack (current-frame alloc-after-setup) slot) ≡
        readLoc s (OnStack (current-frame alloc-after-pair-slots) slot)
      oaf-mem-agree slot f-start≤slot slot<max =
        -- setup-trace writes only to backup-slot, and f-start > backup-slot
        -- So memory at slot ≥ f-start is unchanged
        -- Use frame equalities to convert to `frame`, prove equality, then convert back
        subst₂ (λ f1 f2 → readLoc s-after-setup (OnStack f1 slot) ≡ readLoc s (OnStack f2 slot))
               (sym oaf-frame-setup) (sym oaf-frame-pair-slots)
               oaf-mem-at-frame
        where
          -- backup-slot < f-start (since f-start = suc (suc (suc backup-slot)))
          -- and f-start ≤ slot, so backup-slot < slot
          backup<f-start : backup-slot < f-start
          backup<f-start = ≤-trans (n≤1+n fst-slot) (n≤1+n snd-slot)
          backup<slot : backup-slot < slot
          backup<slot = <-≤-trans backup<f-start f-start≤slot

          -- Core proof: s-after-setup agrees with s at (OnStack frame slot)
          oaf-mem-at-frame : readLoc s-after-setup (OnStack frame slot) ≡ readLoc s (OnStack frame slot)
          oaf-mem-at-frame =
            let -- setup-trace = mov-to-output ∷ store-at-slot backup-slot ∷ []
                -- mov-to-output preserves memory
                s₁' = proj₁ (exec-abstract mov-to-output s alloc)
                alloc₁' = proj₂ (exec-abstract mov-to-output s alloc)
                mov-preserves-mem : readLoc s₁' (OnStack frame slot) ≡ readLoc s (OnStack frame slot)
                mov-preserves-mem = readLoc-stackMem-eq s₁' s (OnStack frame slot) refl refl
                -- store-at-slot backup-slot preserves slot (since backup-slot < slot)
                s₂' = proj₁ (exec-abstract (store-at-slot backup-slot) s₁' alloc₁')
                not-halted₁' = exec-abstract-preserves-halted mov-to-output s alloc not-halted iph-mov-to-output
                frame₁' : current-frame alloc₁' ≡ frame
                frame₁' = exec-abstract-preserves-frame mov-to-output s alloc
                store-preserves-slot : readLoc s₂' (OnStack frame slot) ≡ readLoc s₁' (OnStack frame slot)
                store-preserves-slot = subst (λ f → readLoc s₂' (OnStack f slot) ≡ readLoc s₁' (OnStack f slot))
                                             frame₁'
                                             (store-at-slot-preserves-other backup-slot slot s₁' alloc₁' (inj₁ backup<slot))
                -- Connect s-after-setup to s₂'
                setup-decomp : exec-trace setup-trace s alloc ≡ exec-trace (store-at-slot backup-slot ∷ []) s₁' alloc₁'
                setup-decomp = exec-trace-cons mov-to-output (store-at-slot backup-slot ∷ []) s alloc not-halted
                store-single : exec-trace (store-at-slot backup-slot ∷ []) s₁' alloc₁' ≡ exec-abstract (store-at-slot backup-slot) s₁' alloc₁'
                store-single = exec-trace-single (store-at-slot backup-slot) s₁' alloc₁' not-halted₁'
                s-setup-eq : s-after-setup ≡ s₂'
                s-setup-eq = cong proj₁ (trans setup-decomp store-single)
            in trans (cong (λ st → readLoc st (OnStack frame slot)) s-setup-eq)
                     (trans store-preserves-slot mov-preserves-mem)

      -- s₁ output from trace-correct and rax-is-result
      oaf-s1-output : readReg (regs (proj₁ (exec-trace f-trace s alloc-after-pair-slots))) Output ≡ fst-loc
      oaf-s1-output = subst (λ st → readReg (regs st) Output ≡ fst-loc)
                            (sym (IRResultAWF.trace-correct result-f))
                            (IRResultAWF.rax-is-result result-f)

      output-after-f : readReg (regs s-after-f) Output ≡ fst-loc
      output-after-f =
        trans (exec-trace-output-deterministic f-trace
                s-after-setup s alloc-after-setup alloc-after-pair-slots f-start max-slot-f
                not-halted-after-setup not-halted oaf-frame-eq oaf-input-preserved
                f-tsra (IRResultAWF.trace-slot-reads-below result-f)
                f-twa f-tnhw oaf-mem-agree)
              oaf-s1-output

      -- Output at s-after-g contains snd-loc
      -- Use exec-trace-output-deterministic: two executions of g-trace from states
      -- that agree on Input and memory in [reclaim-f, max-slot-g) give same Output.
      --
      -- Execution 1: g-trace from s-after-middle with alloc-after-middle → s-after-g
      -- Execution 2: g-trace from s₁' with alloc-after-f-reclaim → (via trace-correct)
      -- IRResultAWF.rax-is-result gives Output = snd-loc

      -- Prerequisites for exec-trace-output-deterministic
      -- Frame equality
      oag-frame-eq : current-frame alloc-after-middle ≡ current-frame alloc-after-f-reclaim
      oag-frame-eq = trans (exec-trace-preserves-frame middle-trace s-after-f alloc-after-f)
                     (trans (exec-trace-preserves-frame f-trace s-after-setup alloc-after-setup)
                     (trans (exec-trace-preserves-frame setup-trace s alloc) refl))

      -- Input equality: both have input-loc (s₁' has it from writeReg, s-after-middle from restore-input)
      oag-input-s1' : readReg (regs s₁') Input ≡ input-loc
      oag-input-s1' = writeReg-same (regs s₁) Input input-loc

      -- Decompose middle-trace: store-at-slot fst-slot ∷ restore-input backup-slot ∷ []
      -- (moved before oag-input-after-middle which needs these)
      oag-s-after-fst-store : LocState FS
      oag-s-after-fst-store = proj₁ (exec-abstract (store-at-slot fst-slot) s-after-f alloc-after-f)

      oag-alloc-after-fst-store : AllocState {FS}
      oag-alloc-after-fst-store = proj₂ (exec-abstract (store-at-slot fst-slot) s-after-f alloc-after-f)

      oag-not-halted-fst-store : halted oag-s-after-fst-store ≡ false
      oag-not-halted-fst-store = trans (store-at-slot-halted fst-slot s-after-f alloc-after-f) not-halted-after-f

      oag-frame-fst-store-eq : current-frame oag-alloc-after-fst-store ≡ frame
      oag-frame-fst-store-eq = trans (exec-abstract-preserves-frame (store-at-slot fst-slot) s-after-f alloc-after-f)
                                     (trans (exec-trace-preserves-frame f-trace s-after-setup alloc-after-setup)
                                            (exec-trace-preserves-frame setup-trace s alloc))

      -- Input after middle-trace: restore-input backup-slot sets Input to backup-slot's value
      -- Chain: setup writes input-loc to backup → f preserves → store fst preserves → restore reads
      -- Key steps: (1) setup writes input-loc to backup-slot, (2) f-trace preserves backup (writes above f-start),
      -- (3) store-at-slot fst-slot preserves backup (fst > backup), (4) restore-input reads backup and sets Input
      oag-input-after-middle : readReg (regs s-after-middle) Input ≡ input-loc
      oag-input-after-middle =
        let -- Step 1: After setup-trace, backup-slot has input-loc
            -- setup-trace = mov-to-output ∷ store-at-slot backup-slot ∷ []
            -- Use rec-scheme-stores-input which proves exactly this
            setup-stores : readLoc s-after-setup (OnStack (current-frame alloc) backup-slot) ≡ just (readReg (regs s) Input)
            setup-stores = SMP.RecSchemeSemantics.rec-scheme-stores-input backup-slot s alloc not-halted
            setup-has-input : readLoc s-after-setup (OnStack frame backup-slot) ≡ just input-loc
            setup-has-input = trans setup-stores (cong just rdi-eq)

            -- Step 2: f-trace preserves backup-slot (writes above f-start, backup-slot < f-start)
            -- backup-slot < f-start (backup-slot < suc (suc (suc backup-slot)))
            backup<f-start : backup-slot < f-start
            backup<f-start = ≤-trans (n≤1+n fst-slot) (n≤1+n snd-slot)
            -- f-trace writes above f-start
            -- Use exec-trace-preserves-slot-below
            frame-setup-eq : current-frame alloc-after-setup ≡ frame
            frame-setup-eq = exec-trace-preserves-frame setup-trace s alloc
            f-preserves-backup : readLoc s-after-f (OnStack (current-frame alloc-after-setup) backup-slot) ≡
                                 readLoc s-after-setup (OnStack (current-frame alloc-after-setup) backup-slot)
            f-preserves-backup = exec-trace-preserves-slot-below f-trace s-after-setup alloc-after-setup f-start backup-slot
                                   f-twa f-tnhw backup<f-start
            -- Transport to frame
            f-has-input : readLoc s-after-f (OnStack frame backup-slot) ≡ just input-loc
            f-has-input = trans (subst (λ f → readLoc s-after-f (OnStack f backup-slot) ≡ readLoc s-after-setup (OnStack f backup-slot))
                                       frame-setup-eq f-preserves-backup)
                                setup-has-input

            -- Step 3: store-at-slot fst-slot preserves backup-slot (backup-slot < fst-slot)
            -- fst-slot = suc backup-slot, so backup-slot < fst-slot is suc backup-slot ≤ suc backup-slot = ≤-refl
            backup<fst : backup-slot < fst-slot
            backup<fst = ≤-refl
            frame-f-eq : current-frame alloc-after-f ≡ frame
            frame-f-eq = trans (exec-trace-preserves-frame f-trace s-after-setup alloc-after-setup)
                               (exec-trace-preserves-frame setup-trace s alloc)
            store-fst-preserves-backup : readLoc oag-s-after-fst-store (OnStack frame backup-slot) ≡ readLoc s-after-f (OnStack frame backup-slot)
            store-fst-preserves-backup = subst (λ f → readLoc oag-s-after-fst-store (OnStack f backup-slot) ≡ readLoc s-after-f (OnStack f backup-slot))
                                               frame-f-eq
                                               (store-at-slot-preserves-other fst-slot backup-slot s-after-f alloc-after-f (inj₂ backup<fst))
            fst-store-has-input : readLoc oag-s-after-fst-store (OnStack frame backup-slot) ≡ just input-loc
            fst-store-has-input = trans store-fst-preserves-backup f-has-input

            -- Step 4: restore-input backup-slot sets Input to value at backup-slot
            fst-store-backup-slot-eq : readLoc oag-s-after-fst-store (OnStack (current-frame oag-alloc-after-fst-store) backup-slot) ≡ just input-loc
            fst-store-backup-slot-eq = subst (λ f → readLoc oag-s-after-fst-store (OnStack f backup-slot) ≡ just input-loc)
                                             (sym oag-frame-fst-store-eq)
                                             fst-store-has-input
            restore-sets-input : readReg (regs (proj₁ (exec-abstract (restore-input backup-slot) oag-s-after-fst-store oag-alloc-after-fst-store))) Input ≡ input-loc
            restore-sets-input = SMP.RecSchemeSemantics.exec-abstract-restore-input-sets-input backup-slot oag-s-after-fst-store oag-alloc-after-fst-store input-loc fst-store-backup-slot-eq

            -- Connect s-after-middle to the restore result
            -- s-after-middle = proj₁ (exec-trace middle-trace s-after-f alloc-after-f)
            -- middle-trace = store-at-slot fst-slot ∷ restore-input backup-slot ∷ []
            middle-decomp : exec-trace middle-trace s-after-f alloc-after-f ≡
                            exec-trace (restore-input backup-slot ∷ []) oag-s-after-fst-store oag-alloc-after-fst-store
            middle-decomp = exec-trace-cons (store-at-slot fst-slot) (restore-input backup-slot ∷ []) s-after-f alloc-after-f not-halted-after-f
            restore-single : exec-trace (restore-input backup-slot ∷ []) oag-s-after-fst-store oag-alloc-after-fst-store ≡
                             exec-abstract (restore-input backup-slot) oag-s-after-fst-store oag-alloc-after-fst-store
            restore-single = exec-trace-single (restore-input backup-slot) oag-s-after-fst-store oag-alloc-after-fst-store oag-not-halted-fst-store
            s-middle-eq : s-after-middle ≡ proj₁ (exec-abstract (restore-input backup-slot) oag-s-after-fst-store oag-alloc-after-fst-store)
            s-middle-eq = cong proj₁ (trans middle-decomp restore-single)

        in trans (cong (λ st → readReg (regs st) Input) s-middle-eq) restore-sets-input

      oag-input-eq : readReg (regs s-after-middle) Input ≡ readReg (regs s₁') Input
      oag-input-eq = trans oag-input-after-middle (sym oag-input-s1')

      -- Memory agreement at [reclaim-f, max-slot-g)
      -- middle-trace writes to fst-slot (< reclaim-f), so slots ≥ reclaim-f unchanged from s-after-f
      -- s-after-f vs s₁': need trace determinism on f-trace results for memory
      -- This is complex because s-after-f and s₁ may differ in memory outside [f-start, max-slot-f)
      -- For now, use the fact that both agree on slots in [reclaim-f, max-slot-g) because:
      -- - slots ≥ reclaim-f are uninitialized before g runs
      -- - the memory values at these slots don't affect g's output
      oag-frame-middle : current-frame alloc-after-middle ≡ frame
      oag-frame-middle = trans (exec-trace-preserves-frame middle-trace s-after-f alloc-after-f)
                         (trans (exec-trace-preserves-frame f-trace s-after-setup alloc-after-setup)
                                (exec-trace-preserves-frame setup-trace s alloc))

      oag-frame-reclaim : current-frame alloc-after-f-reclaim ≡ frame
      oag-frame-reclaim = refl

      oag-mem-agree : ∀ slot → reclaim-f ≤ slot → slot < max-slot-g →
        readLoc s-after-middle (OnStack (current-frame alloc-after-middle) slot) ≡
        readLoc s₁' (OnStack (current-frame alloc-after-f-reclaim) slot)
      oag-mem-agree slot rf≤slot slot<max with slot <? max-slot-f
      ... | yes slot<max-f =
        -- Case 1: slot ∈ [reclaim-f, max-slot-f) - in f's write range, use determinism
        let -- Frame equalities
            frame-f-eq : current-frame alloc-after-f ≡ frame
            frame-f-eq = trans (exec-trace-preserves-frame f-trace s-after-setup alloc-after-setup)
                               (exec-trace-preserves-frame setup-trace s alloc)

            -- middle-trace preserves slot ≥ reclaim-f (writes at fst-slot < reclaim-f)
            middle-twb : TraceWritesBelow reclaim-f middle-trace
            middle-twb = fst-slot<reclaim-f , tt
            middle-pres = SMP.TracePrimitives.exec-trace-preserves-slot-above middle-trace
                            s-after-f alloc-after-f reclaim-f slot middle-twb tt rf≤slot
            middle-pres-frame = subst (λ fr → readLoc s-after-middle (OnStack fr slot) ≡
                                              readLoc s-after-f (OnStack fr slot))
                                      frame-f-eq middle-pres

            -- slot ≥ reclaim-f ≥ f-start
            slot≥f-start : f-start ≤ slot
            slot≥f-start = ≤-trans reclaim-f-above-f-start rf≤slot

            -- Use determinism lemma for [f-start, max-slot-f)
            mem-det = SMP.TraceOutputDeterminism.exec-trace-mem-deterministic f-trace
                        s-after-setup s alloc-after-setup alloc-after-pair-slots f-start max-slot-f
                        not-halted-after-setup not-halted
                        oaf-frame-eq oaf-input-preserved
                        f-tsra f-tsrb f-twa f-twb f-tnhw oaf-mem-agree
                        slot slot≥f-start slot<max-f

            -- Convert frames
            mem-det-frame : readLoc s-after-f (OnStack frame slot) ≡
                            readLoc (proj₁ (exec-trace f-trace s alloc-after-pair-slots)) (OnStack frame slot)
            mem-det-frame = subst₂ (λ f1 f2 → readLoc s-after-f (OnStack f1 slot) ≡
                                              readLoc (proj₁ (exec-trace f-trace s alloc-after-pair-slots)) (OnStack f2 slot))
                                   oaf-frame-setup oaf-frame-pair-slots mem-det

            -- Convert to s₁ using trace-correct
            s₁-eq : readLoc (proj₁ (exec-trace f-trace s alloc-after-pair-slots)) (OnStack frame slot) ≡
                    readLoc s₁ (OnStack frame slot)
            s₁-eq = cong (λ st → readLoc st (OnStack frame slot)) (IRResultAWF.trace-correct result-f)

            -- s₁' has same stack as s₁
            s₁'-eq : readLoc s₁' (OnStack frame slot) ≡ readLoc s₁ (OnStack frame slot)
            s₁'-eq = refl

            f-eq : readLoc s-after-f (OnStack frame slot) ≡ readLoc s₁ (OnStack frame slot)
            f-eq = trans mem-det-frame s₁-eq

        in subst₂ (λ f1 f2 → readLoc s-after-middle (OnStack f1 slot) ≡ readLoc s₁' (OnStack f2 slot))
                  (sym oag-frame-middle) (sym oag-frame-reclaim)
                  (trans middle-pres-frame (trans f-eq (sym s₁'-eq)))
      ... | no slot≮max-f =
        -- Case 2: slot ≥ max-slot-f - f doesn't write there, both preserve from s
        let slot≥max-f : max-slot-f ≤ slot
            slot≥max-f = ≮⇒≥ slot≮max-f

            -- Frame equalities
            frame-f-eq : current-frame alloc-after-f ≡ frame
            frame-f-eq = trans (exec-trace-preserves-frame f-trace s-after-setup alloc-after-setup)
                               (exec-trace-preserves-frame setup-trace s alloc)

            -- middle-trace preserves slot ≥ reclaim-f (writes at fst-slot < reclaim-f)
            middle-twb : TraceWritesBelow reclaim-f middle-trace
            middle-twb = fst-slot<reclaim-f , tt
            middle-pres = SMP.TracePrimitives.exec-trace-preserves-slot-above middle-trace
                            s-after-f alloc-after-f reclaim-f slot middle-twb tt rf≤slot
            middle-pres-frame = subst (λ fr → readLoc s-after-middle (OnStack fr slot) ≡
                                              readLoc s-after-f (OnStack fr slot))
                                      frame-f-eq middle-pres

            -- f-trace preserves slot ≥ max-slot-f (writes below max-slot-f)
            f-pres = SMP.TracePrimitives.exec-trace-preserves-slot-above f-trace
                       s-after-setup alloc-after-setup max-slot-f slot f-twb f-tnhw slot≥max-f
            f-pres-frame = subst (λ fr → readLoc s-after-f (OnStack fr slot) ≡
                                         readLoc s-after-setup (OnStack fr slot))
                                 oaf-frame-setup f-pres

            -- setup-trace preserves slot ≥ max-slot-f (writes at backup-slot < max-slot-f)
            -- backup-slot < fst-slot = ≤-refl (since suc backup-slot = fst-slot)
            -- fst-slot < snd-slot = ≤-refl
            -- snd-slot < f-start = ≤-refl
            -- f-start ≤ reclaim-f (reclaim-f-above-f-start)
            -- reclaim-f ≤ max-slot-f (max-slot-geq-final)
            backup<fst-slot : backup-slot < fst-slot
            backup<fst-slot = ≤-refl
            fst<snd-slot : fst-slot < snd-slot
            fst<snd-slot = ≤-refl
            snd<f-start' : snd-slot < f-start
            snd<f-start' = ≤-refl
            backup<f-start' : backup-slot < f-start
            backup<f-start' = ≤-trans (≤-trans backup<fst-slot (n≤1+n fst-slot)) (n≤1+n snd-slot)
            backup<max-slot-f : backup-slot < max-slot-f
            backup<max-slot-f = <-≤-trans backup<f-start'
                                  (≤-trans reclaim-f-above-f-start (IRResultAWF.max-slot-geq-final result-f))
            setup-twb : TraceWritesBelow max-slot-f setup-trace
            setup-twb = backup<max-slot-f , tt
            setup-pres = SMP.TracePrimitives.exec-trace-preserves-slot-above setup-trace
                           s alloc max-slot-f slot setup-twb tt slot≥max-f

            -- Combine: s-after-f preserves from s
            s-after-f-pres = trans f-pres-frame setup-pres

            -- s₁ also preserves from s (f writes below max-slot-f)
            s₁-f-pres = SMP.TracePrimitives.exec-trace-preserves-slot-above f-trace
                          s alloc-after-pair-slots max-slot-f slot f-twb f-tnhw slot≥max-f
            s₁-pres = subst (λ st → readLoc st (OnStack frame slot) ≡ readLoc s (OnStack frame slot))
                            (IRResultAWF.trace-correct result-f) s₁-f-pres

            -- s₁' = s₁ (only regs changed)
            s₁'-eq : readLoc s₁' (OnStack frame slot) ≡ readLoc s₁ (OnStack frame slot)
            s₁'-eq = refl

            -- Both preserve from s, so they're equal
            f-eq : readLoc s-after-f (OnStack frame slot) ≡ readLoc s₁ (OnStack frame slot)
            f-eq = trans s-after-f-pres (sym s₁-pres)

        in subst₂ (λ f1 f2 → readLoc s-after-middle (OnStack f1 slot) ≡ readLoc s₁' (OnStack f2 slot))
                  (sym oag-frame-middle) (sym oag-frame-reclaim)
                  (trans middle-pres-frame (trans f-eq (sym s₁'-eq)))

      -- s₂ output from trace-correct and rax-is-result
      oag-s2-output : readReg (regs (proj₁ (exec-trace g-trace s₁' alloc-after-f-reclaim))) Output ≡ snd-loc
      oag-s2-output = subst (λ st → readReg (regs st) Output ≡ snd-loc)
                            (sym (IRResultAWF.trace-correct result-g))
                            (IRResultAWF.rax-is-result result-g)

      output-after-g : readReg (regs s-after-g) Output ≡ snd-loc
      output-after-g =
        trans (exec-trace-output-deterministic g-trace
                s-after-middle s₁' alloc-after-middle alloc-after-f-reclaim reclaim-f max-slot-g
                not-halted-after-middle (IRResultAWF.not-halted result-f) oag-frame-eq oag-input-eq
                g-tsra (IRResultAWF.trace-slot-reads-below result-g)
                g-twa g-tnhw oag-mem-agree)
              oag-s2-output

      -- Decompose middle-trace: store-at-slot fst-slot ∷ restore-input backup-slot ∷ []
      s-after-fst-store : LocState FS
      s-after-fst-store = proj₁ (exec-abstract (store-at-slot fst-slot) s-after-f alloc-after-f)

      alloc-after-fst-store : AllocState {FS}
      alloc-after-fst-store = proj₂ (exec-abstract (store-at-slot fst-slot) s-after-f alloc-after-f)

      not-halted-after-fst-store : halted s-after-fst-store ≡ false
      not-halted-after-fst-store = trans (store-at-slot-halted fst-slot s-after-f alloc-after-f) not-halted-after-f

      -- fst-slot gets fst-loc after store-at-slot fst-slot
      fst-written-in-store : readLoc s-after-fst-store (OnStack (current-frame alloc-after-f) fst-slot) ≡ just fst-loc
      fst-written-in-store = trans (store-at-slot-result fst-slot s-after-f alloc-after-f)
                                   (cong just output-after-f)

      -- Frame equality for fst-slot location
      frame-after-f-eq : current-frame alloc-after-f ≡ frame
      frame-after-f-eq = trans (exec-trace-preserves-frame f-trace s-after-setup alloc-after-setup)
                               (exec-trace-preserves-frame setup-trace s alloc)

      -- frame after fst-store is same as frame-after-f
      frame-after-fst-store-eq : current-frame alloc-after-fst-store ≡ frame
      frame-after-fst-store-eq = trans (exec-abstract-preserves-frame (store-at-slot fst-slot) s-after-f alloc-after-f)
                                       frame-after-f-eq

      -- restore-input preserves all memory locations (it only modifies Input register)
      restore-preserves-fst : readLoc (proj₁ (exec-abstract (restore-input backup-slot) s-after-fst-store alloc-after-fst-store))
                                      (OnStack frame fst-slot) ≡ readLoc s-after-fst-store (OnStack frame fst-slot)
      restore-preserves-fst =
        readLoc-stackMem-eq
          (proj₁ (exec-abstract (restore-input backup-slot) s-after-fst-store alloc-after-fst-store))
          s-after-fst-store
          (OnStack frame fst-slot)
          (SMP.RecSchemeSemantics.exec-abstract-restore-input-preserves-stackMem backup-slot s-after-fst-store alloc-after-fst-store)
          (SMP.RecSchemeSemantics.exec-abstract-restore-input-preserves-heapMem backup-slot s-after-fst-store alloc-after-fst-store)

      -- Combine: s-after-middle has fst-loc at fst-slot
      -- middle-trace = store-at-slot fst-slot ∷ restore-input backup-slot ∷ []
      -- restore-input only modifies register, not memory, so fst-slot is preserved
      fst-at-s-after-middle : readLoc s-after-middle (OnStack frame fst-slot) ≡ just fst-loc
      fst-at-s-after-middle =
        -- Use exec-trace-preserves-slot-below on the restore-input part
        -- First, restore-input doesn't write to any stack slot (TraceWritesAbove anything)
        -- So we can use the slot-below preservation lemma
        let rest-trace : AbstractTrace
            rest-trace = restore-input backup-slot ∷ []
            -- rest-trace writes nowhere (TraceWritesAbove any bound)
            rest-twa : TraceWritesAbove fst-slot rest-trace
            rest-twa = tt
            rest-tnhw : TraceNoHeapWrites rest-trace
            rest-tnhw = tt
            -- After fst-store, fst-slot < fst-slot is false, so use different reasoning
            -- Actually, restore-input doesn't write to stack at all
            -- Let's use readLoc-stackMem-eq on the trace execution
            s-after-rest : LocState FS
            s-after-rest = proj₁ (exec-trace rest-trace s-after-fst-store alloc-after-fst-store)
            alloc-after-rest : AllocState {FS}
            alloc-after-rest = proj₂ (exec-trace rest-trace s-after-fst-store alloc-after-fst-store)
            -- s-after-middle is definitionally equal to executing middle-trace from s-after-f
            -- and middle-trace = store-at-slot fst-slot ∷ rest-trace
            -- So s-after-middle = s-after-rest when computed through the decomposition
            -- Use the cons lemma
            middle-decomp : exec-trace middle-trace s-after-f alloc-after-f ≡
                           exec-trace rest-trace s-after-fst-store alloc-after-fst-store
            middle-decomp = exec-trace-cons (store-at-slot fst-slot) rest-trace s-after-f alloc-after-f not-halted-after-f
            s-middle-eq : s-after-middle ≡ s-after-rest
            s-middle-eq = cong proj₁ middle-decomp
            -- restore-input preserves stack memory
            rest-preserves-stackMem : stackMem s-after-rest ≡ stackMem s-after-fst-store
            rest-preserves-stackMem = SMP.RecSchemeSemantics.restore-trace-preserves-stackMem backup-slot s-after-fst-store alloc-after-fst-store
                                        not-halted-after-fst-store
            rest-preserves-heapMem : heapMem s-after-rest ≡ heapMem s-after-fst-store
            rest-preserves-heapMem = SMP.RecSchemeSemantics.restore-trace-preserves-heapMem backup-slot s-after-fst-store alloc-after-fst-store
                                       not-halted-after-fst-store
            rest-preserves-fst' : readLoc s-after-rest (OnStack frame fst-slot) ≡
                                  readLoc s-after-fst-store (OnStack frame fst-slot)
            rest-preserves-fst' = readLoc-stackMem-eq s-after-rest s-after-fst-store (OnStack frame fst-slot)
                                    rest-preserves-stackMem rest-preserves-heapMem
            fst-at-fst-store : readLoc s-after-fst-store (OnStack frame fst-slot) ≡ just fst-loc
            fst-at-fst-store = subst (λ f → readLoc s-after-fst-store (OnStack f fst-slot) ≡ just fst-loc)
                                 frame-after-f-eq fst-written-in-store
        in trans (cong (λ st → readLoc st (OnStack frame fst-slot)) s-middle-eq)
                 (trans rest-preserves-fst' fst-at-fst-store)

      -- fst-slot preserved through rest of middle-trace (restore-input doesn't write)
      -- then through g-trace (writes above reclaim-f > fst-slot)
      -- then through final-trace (writes to snd-slot ≠ fst-slot, lea doesn't write)

      -- g-trace preserves fst-slot (writes above reclaim-f, fst-slot < reclaim-f)
      g-preserves-fst : readLoc s-after-g (OnStack frame fst-slot) ≡ readLoc s-after-middle (OnStack frame fst-slot)
      g-preserves-fst =
        let preserved = exec-trace-preserves-slot-below g-trace s-after-middle alloc-after-middle
                          reclaim-f fst-slot g-twa g-tnhw fst-slot<reclaim-f
            frame-eq = exec-trace-preserves-frame middle-trace s-after-f alloc-after-f
        in subst (λ f → readLoc s-after-g (OnStack f fst-slot) ≡ readLoc s-after-middle (OnStack f fst-slot))
                 (trans frame-eq frame-after-f-eq) preserved

      -- store-at-slot snd-slot preserves fst-slot (different slots)
      -- snd-slot = suc fst-slot, so fst-slot < snd-slot means suc fst-slot ≤ suc fst-slot = ≤-refl
      snd-store-preserves-fst : readLoc s-after-snd-store (OnStack frame fst-slot) ≡ readLoc s-after-g (OnStack frame fst-slot)
      snd-store-preserves-fst =
        subst (λ f → readLoc s-after-snd-store (OnStack f fst-slot) ≡ readLoc s-after-g (OnStack f fst-slot))
              frame-preserved-through
              (store-at-slot-preserves-other snd-slot fst-slot s-after-g alloc-after-g (inj₂ ≤-refl))

      -- lea-slot preserves all memory
      lea-preserves-fst : readLoc (proj₁ (exec-abstract (lea-slot fst-slot) s-after-snd-store alloc-after-snd-store))
                                  (OnStack frame fst-slot) ≡ readLoc s-after-snd-store (OnStack frame fst-slot)
      lea-preserves-fst = lea-slot-preserves-mem fst-slot s-after-snd-store alloc-after-snd-store (OnStack frame fst-slot)

      fst-ptr : readLoc s-final (OnStack frame fst-slot) ≡ just fst-loc
      fst-ptr =
        -- Chain: s-final -> s-after-final -> lea preserves -> store snd preserves -> g preserves -> s-after-middle
        let eq1 = cong (λ st → readLoc st (OnStack frame fst-slot)) s-final-eq
            eq2 = cong (λ st → readLoc st (OnStack frame fst-slot)) s-after-final-eq
        in trans eq1 (trans eq2 (trans lea-preserves-fst
                                (trans snd-store-preserves-fst
                                (trans g-preserves-fst fst-at-s-after-middle))))

      -- snd-slot gets snd-loc from final-trace
      snd-written : readLoc s-after-snd-store (OnStack frame snd-slot) ≡ just snd-loc
      snd-written = subst (λ f → readLoc s-after-snd-store (OnStack f snd-slot) ≡ just snd-loc)
                          frame-preserved-through
                          (trans (store-at-slot-result snd-slot s-after-g alloc-after-g)
                                 (cong just output-after-g))

      -- lea-slot preserves snd-slot
      lea-preserves-snd : readLoc (proj₁ (exec-abstract (lea-slot fst-slot) s-after-snd-store alloc-after-snd-store))
                                  (OnStack frame snd-slot) ≡ readLoc s-after-snd-store (OnStack frame snd-slot)
      lea-preserves-snd = lea-slot-preserves-mem fst-slot s-after-snd-store alloc-after-snd-store (OnStack frame snd-slot)

      snd-ptr : readLoc s-final (OnStack frame snd-slot) ≡ just snd-loc
      snd-ptr =
        let eq1 = cong (λ st → readLoc st (OnStack frame snd-slot)) s-final-eq
            eq2 = cong (λ st → readLoc st (OnStack frame snd-slot)) s-after-final-eq
        in trans eq1 (trans eq2 (trans lea-preserves-snd snd-written))

      ------------------------------------------------------------------------
      -- fst-valid and snd-valid (validity of sub-results)
      --
      -- Key insight: Use validityWF-trace-preserves with positive bounds.
      -- - fst-loc is BeforeFrontier at reclaim-f
      -- - After f, rest of trace writes above suc backup-slot > fst-slot
      -- - So fst-loc's validity is preserved
      ------------------------------------------------------------------------
      fst-before : BeforeFrontier alloc-final fst-loc
      fst-before = frontier-monotone alloc-after-f-reclaim alloc-final
                     refl
                     (IRResultAWF.slot-monotone result-g)
                     ≤-refl
                     fst-loc
                     (IRResultAWF.reclaim-preserves-result result-f)

      snd-before : BeforeFrontier alloc-final snd-loc
      snd-before = frontier-monotone (record alloc { next-slot = reclaim-g }) alloc-final
                     refl ≤-refl ≤-refl snd-loc
                     (IRResultAWF.reclaim-preserves-result result-g)

      -- sucLoc pair-loc = OnStack frame snd-slot
      sucLoc-pair-before : BeforeFrontier alloc-final (sucLoc pair-loc)
      sucLoc-pair-before = stack-before refl snd<reclaim-g

      ----------------------------------------------------------------------
      -- fst-valid: Validity of f's result at fst-loc in s-final
      --
      -- Strategy using POSITIVE BOUNDS:
      -- 1. reclaim-preserves-validity gives validity at s₁ with alloc-after-f-reclaim
      -- 2. Transfer validity from s₁ to s-after-f using validityWF-mem-preserved-in-regions
      --    Memory agrees in two disjoint regions:
      --      - Input region: [0, backup-slot) - preserved from initial state
      --      - Fresh region: [f-start, reclaim-f) - written by f-trace deterministically
      --    The gap [backup-slot, f-start) = {backup-slot, fst-slot, snd-slot} contains
      --    no sub-locations of fst-loc.
      -- 3. Apply validityWF-trace-preserves for rest-trace to reach s-final
      -- 4. Advance frontier from reclaim-f to reclaim-g
      --
      -- Key insight (positive characterization): fst-loc's sub-locations are in:
      --   - Input region: [0, backup-slot) - from input x
      --   - Fresh region: [f-start, reclaim-f) - from f's allocations
      ----------------------------------------------------------------------

      -- Step 1: Get validity at s₁ with alloc-after-f-reclaim
      valid-s1-reclaimed : ValidAtWF mF alloc-after-f-reclaim (eval primSem f x) fst-loc s₁
      valid-s1-reclaimed = IRResultAWF.reclaim-preserves-validity result-f

      -- fst-loc is before frontier at alloc-after-f-reclaim
      fst-loc-before-reclaimed : BeforeFrontier alloc-after-f-reclaim fst-loc
      fst-loc-before-reclaimed = IRResultAWF.reclaim-preserves-result result-f

      -- Step 2: Memory agreement from s₁ to s-after-f using POSITIVE BOUNDS
      -- s₁ = exec f-trace s alloc-after-pair-slots (recursive call result)
      -- s-after-f = exec f-trace s-after-setup alloc-after-setup
      --
      -- Region bounds for fst-loc's sub-locations:
      --   input-bound = backup-slot (sub-locations from x are < backup-slot)
      --   fresh-start = f-start (sub-locations from f are ≥ f-start)

      -- Memory agrees on input region [0, backup-slot)
      -- Both s₁ and s-after-f preserve this from initial state (f writes above f-start)
      f-mem-input-region : ∀ slot → slot < backup-slot →
        readLoc s-after-f (OnStack frame slot) ≡ readLoc s₁ (OnStack frame slot)
      f-mem-input-region slot slot<backup =
        let -- slot < backup-slot < f-start, so slot < f-start
            -- f-start = suc snd-slot = suc (suc (suc backup-slot))
            backup≤f-start' : backup-slot ≤ f-start
            backup≤f-start' = ≤-trans (n≤1+n backup-slot) (≤-trans (n≤1+n fst-slot) (n≤1+n snd-slot))
            slot<f-start : slot < f-start
            slot<f-start = ≤-trans slot<backup backup≤f-start'
            -- setup-trace writes at backup-slot, so TraceWritesAbove backup-slot
            setup-twa : TraceWritesAbove backup-slot setup-trace
            setup-twa = ≤-refl , tt  -- mov-to-output doesn't write, store-at-slot backup-slot writes at backup-slot
            setup-tnhw : TraceNoHeapWrites setup-trace
            setup-tnhw = tt
            -- s-after-f preserves slot from s-after-setup (f-trace writes above f-start > slot)
            f-pres = SMP.TracePrimitives.exec-trace-preserves-slot-below f-trace s-after-setup
                       alloc-after-setup f-start slot f-twa f-tnhw slot<f-start
            f-pres-frame = subst (λ fr → readLoc s-after-f (OnStack fr slot) ≡
                                         readLoc s-after-setup (OnStack fr slot))
                                 oaf-frame-setup f-pres
            -- s-after-setup preserves slot from s (setup-trace writes at backup-slot > slot)
            setup-pres = SMP.TracePrimitives.exec-trace-preserves-slot-below setup-trace s alloc
                           backup-slot slot setup-twa setup-tnhw slot<backup
            -- s₁ preserves slot from s (f-trace writes above f-start > slot)
            exec-f-pres = SMP.TracePrimitives.exec-trace-preserves-slot-below f-trace s
                            alloc-after-pair-slots f-start slot f-twa f-tnhw slot<f-start
            s₁-pres = subst (λ st → readLoc st (OnStack frame slot) ≡ readLoc s (OnStack frame slot))
                            (IRResultAWF.trace-correct result-f) exec-f-pres
        in trans f-pres-frame (trans setup-pres (sym s₁-pres))

      -- Memory agrees on fresh region [f-start, reclaim-f)
      -- Both executions of f-trace write same values (deterministic given same Input)
      f-mem-fresh-region : ∀ slot → f-start ≤ slot → slot < reclaim-f →
        readLoc s-after-f (OnStack frame slot) ≡ readLoc s₁ (OnStack frame slot)
      f-mem-fresh-region slot f-start≤slot slot<reclaim =
        let -- slot < reclaim-f ≤ max-slot-f
            slot<max : slot < max-slot-f
            slot<max = <-≤-trans slot<reclaim (IRResultAWF.max-slot-geq-final result-f)
            -- Use exec-trace-mem-deterministic to show both executions produce same memory
            -- Execution 1: f-trace from s-after-setup with alloc-after-setup → s-after-f
            -- Execution 2: f-trace from s with alloc-after-pair-slots → proj₁ (exec-trace f-trace s alloc-after-pair-slots)
            mem-det = SMP.TraceOutputDeterminism.exec-trace-mem-deterministic f-trace
                        s-after-setup s alloc-after-setup alloc-after-pair-slots f-start max-slot-f
                        not-halted-after-setup not-halted oaf-frame-eq oaf-input-preserved
                        f-tsra f-tsrb f-twa f-twb f-tnhw oaf-mem-agree
                        slot f-start≤slot slot<max
            -- Convert frame: result uses current-frame alloc-after-setup = frame
            mem-det-frame : readLoc s-after-f (OnStack frame slot) ≡
                            readLoc (proj₁ (exec-trace f-trace s alloc-after-pair-slots)) (OnStack frame slot)
            mem-det-frame = subst₂ (λ f1 f2 → readLoc s-after-f (OnStack f1 slot) ≡
                                              readLoc (proj₁ (exec-trace f-trace s alloc-after-pair-slots)) (OnStack f2 slot))
                                   oaf-frame-setup oaf-frame-pair-slots mem-det
            -- Convert exec result to s₁ using trace-correct
            s₁-eq : readLoc (proj₁ (exec-trace f-trace s alloc-after-pair-slots)) (OnStack frame slot) ≡
                    readLoc s₁ (OnStack frame slot)
            s₁-eq = cong (λ st → readLoc st (OnStack frame slot)) (IRResultAWF.trace-correct result-f)
        in trans mem-det-frame s₁-eq

      -- Memory agrees on heap (no heap writes)
      f-mem-heap : ∀ h → readLoc s-after-f (OnHeap h) ≡ readLoc s₁ (OnHeap h)
      f-mem-heap h =
        let -- s-after-f preserves heap from s-after-setup (f-trace has no heap writes)
            s-after-f-pres = SMP.TracePrimitives.exec-trace-preserves-heap-loc f-trace s-after-setup alloc-after-setup h f-tnhw
            -- s-after-setup preserves heap from s (setup-trace has no heap writes)
            setup-tnhw : TraceNoHeapWrites setup-trace
            setup-tnhw = tt
            s-setup-pres = SMP.TracePrimitives.exec-trace-preserves-heap-loc setup-trace s alloc h setup-tnhw
            -- s₁ preserves heap from s via trace-correct
            exec-f-pres = SMP.TracePrimitives.exec-trace-preserves-heap-loc f-trace s alloc-after-pair-slots h f-tnhw
            s₁-pres = subst (λ st → readLoc st (OnHeap h) ≡ readLoc s (OnHeap h))
                            (IRResultAWF.trace-correct result-f) exec-f-pres
        in trans s-after-f-pres (trans s-setup-pres (sym s₁-pres))

      -- Memory agrees on ancestor frames (f doesn't write there)
      f-mem-ancestors : ∀ f' k → current-frame alloc-after-f-reclaim ≺ f' →
        readLoc s-after-f (OnStack f' k) ≡ readLoc s₁ (OnStack f' k)
      f-mem-ancestors f' k cf≺f' =
        let -- current-frame alloc-after-f-reclaim = frame (only next-slot changed)
            -- So cf≺f' : frame ≺ f' by reflexivity
            -- s-after-f preserves ancestors from s-after-setup
            alloc-after-setup-cf≺f' : current-frame alloc-after-setup ≺ f'
            alloc-after-setup-cf≺f' = subst (_≺ f') (sym oaf-frame-setup) cf≺f'
            s-after-f-pres = SMP.TracePrimitives.exec-trace-preserves-ancestor f-trace s-after-setup
                               alloc-after-setup f' k alloc-after-setup-cf≺f' f-tnhw
            -- s-after-setup preserves ancestors from s
            setup-tnhw : TraceNoHeapWrites setup-trace
            setup-tnhw = tt
            s-setup-pres = SMP.TracePrimitives.exec-trace-preserves-ancestor setup-trace s alloc f' k cf≺f' setup-tnhw
            -- s₁ preserves ancestors from s via trace-correct
            alloc-pair-slots-cf≺f' : current-frame alloc-after-pair-slots ≺ f'
            alloc-pair-slots-cf≺f' = subst (_≺ f') (sym oaf-frame-pair-slots) cf≺f'
            exec-f-pres = SMP.TracePrimitives.exec-trace-preserves-ancestor f-trace s alloc-after-pair-slots
                            f' k alloc-pair-slots-cf≺f' f-tnhw
            s₁-pres = subst (λ st → readLoc st (OnStack f' k) ≡ readLoc s (OnStack f' k))
                            (IRResultAWF.trace-correct result-f) exec-f-pres
        in trans s-after-f-pres (trans s-setup-pres (sym s₁-pres))

      -- Region ordering: backup-slot ≤ f-start ≤ reclaim-f
      backup≤f-start : backup-slot ≤ f-start
      backup≤f-start = ≤-trans (n≤1+n backup-slot) (≤-trans (n≤1+n fst-slot) (n≤1+n snd-slot))

      f-start≤reclaim-f : f-start ≤ reclaim-f
      f-start≤reclaim-f = reclaim-f-above-f-start

      -- Transfer validity from s₁ to s-after-f using positive regions lemma
      valid-at-s-after-f : ValidAtWF mF alloc-after-f-reclaim (eval primSem f x) fst-loc s-after-f
      valid-at-s-after-f = validityWF-mem-preserved-in-regions alloc-after-f-reclaim
                             (eval primSem f x) fst-loc backup-slot f-start s₁ s-after-f
                             fst-loc-before-reclaimed backup≤f-start f-start≤reclaim-f
                             f-mem-input-region f-mem-fresh-region f-mem-heap f-mem-ancestors
                             valid-s1-reclaimed

      -- Step 3: Transfer validity from s-after-f to s-final using POSITIVE BOUNDS
      --
      -- rest-trace = middle ++ g ++ final writes to:
      --   - fst-slot, snd-slot (in gap [backup-slot, f-start))
      --   - g's allocations in [reclaim-f, max-g)
      --
      -- fst-loc's sub-locations are in [0, backup-slot) ∪ [f-start, reclaim-f).
      -- rest-trace does NOT write to these regions, so sub-locations are preserved.
      --
      -- Note: We can't use validityWF-trace-preserves here because rest-trace writes
      -- BELOW reclaim-f (at fst-slot, snd-slot). Instead, we use positive region
      -- preservation again.

      -- Memory agrees on input region [0, backup-slot): rest-trace writes above backup-slot
      rest-mem-input-region : ∀ slot → slot < backup-slot →
        readLoc s-final (OnStack frame slot) ≡ readLoc s-after-f (OnStack frame slot)
      rest-mem-input-region slot slot<backup =
        let -- slot < backup-slot < fst-slot = suc backup-slot
            slot<fst : slot < fst-slot
            slot<fst = ≤-trans slot<backup (n≤1+n backup-slot)
            slot<snd : slot < snd-slot
            slot<snd = ≤-trans slot<fst (n≤1+n fst-slot)
            slot<reclaim-f : slot < reclaim-f
            slot<reclaim-f = <-≤-trans slot<backup backup≤reclaim-f
            -- middle-trace writes at fst-slot, so TraceWritesAbove fst-slot
            middle-twa : TraceWritesAbove fst-slot middle-trace
            middle-twa = ≤-refl , tt  -- store-at-slot fst-slot writes at fst-slot, restore-input doesn't write
            middle-tnhw : TraceNoHeapWrites middle-trace
            middle-tnhw = tt
            -- middle-trace preserves slot from s-after-f to s-after-middle
            middle-pres = SMP.TracePrimitives.exec-trace-preserves-slot-below middle-trace
                            s-after-f alloc-after-f fst-slot slot middle-twa middle-tnhw slot<fst
            middle-pres-frame = subst (λ fr → readLoc s-after-middle (OnStack fr slot) ≡
                                              readLoc s-after-f (OnStack fr slot))
                                      frame-after-f-eq middle-pres
            -- g-trace writes above reclaim-f, so preserves slot < reclaim-f
            g-pres = SMP.TracePrimitives.exec-trace-preserves-slot-below g-trace
                       s-after-middle alloc-after-middle reclaim-f slot g-twa g-tnhw slot<reclaim-f
            g-pres-frame = subst (λ fr → readLoc s-after-g (OnStack fr slot) ≡
                                         readLoc s-after-middle (OnStack fr slot))
                                 oag-frame-middle g-pres
            -- final-trace writes at snd-slot, so TraceWritesAbove snd-slot
            final-twa : TraceWritesAbove snd-slot final-trace
            final-twa = ≤-refl , tt  -- store-at-slot snd-slot writes at snd-slot, lea doesn't write
            final-tnhw : TraceNoHeapWrites final-trace
            final-tnhw = tt
            -- final-trace preserves slot from s-after-g to s-after-final
            final-pres = SMP.TracePrimitives.exec-trace-preserves-slot-below final-trace
                           s-after-g alloc-after-g snd-slot slot final-twa final-tnhw slot<snd
            final-pres-frame = subst (λ fr → readLoc s-after-final (OnStack fr slot) ≡
                                             readLoc s-after-g (OnStack fr slot))
                                     frame-preserved-through final-pres
            -- Chain: s-after-final preserves from s-after-f
            chain = trans final-pres-frame (trans g-pres-frame middle-pres-frame)
            -- Use s-final-eq : s-final ≡ s-after-final
        in subst (λ st → readLoc st (OnStack frame slot) ≡ readLoc s-after-f (OnStack frame slot))
                 (sym s-final-eq) chain

      -- Memory agrees on fresh region [f-start, reclaim-f): rest-trace writes elsewhere
      -- rest-trace writes to [backup-slot, f-start) ∪ [reclaim-f, max-g), so [f-start, reclaim-f) preserved
      rest-mem-fresh-region : ∀ slot → f-start ≤ slot → slot < reclaim-f →
        readLoc s-final (OnStack frame slot) ≡ readLoc s-after-f (OnStack frame slot)
      rest-mem-fresh-region slot f-start≤slot slot<reclaim =
        let -- middle-trace writes at fst-slot < f-start, so preserves slot ≥ f-start
            -- fst-slot < f-start since suc fst-slot = snd-slot and f-start = suc snd-slot
            -- So fst-slot < f-start = suc fst-slot ≤ f-start = snd-slot ≤ suc snd-slot = n≤1+n snd-slot
            fst<f-start : fst-slot < f-start
            fst<f-start = n≤1+n snd-slot
            middle-twb : TraceWritesBelow f-start middle-trace
            middle-twb = fst<f-start , tt  -- store-at-slot fst-slot writes at fst-slot < f-start
            middle-tnhw : TraceNoHeapWrites middle-trace
            middle-tnhw = tt
            middle-pres = SMP.TracePrimitives.exec-trace-preserves-slot-above middle-trace
                            s-after-f alloc-after-f f-start slot middle-twb middle-tnhw f-start≤slot
            middle-pres-frame = subst (λ fr → readLoc s-after-middle (OnStack fr slot) ≡
                                              readLoc s-after-f (OnStack fr slot))
                                      frame-after-f-eq middle-pres
            -- g-trace writes above reclaim-f, so preserves slot < reclaim-f
            g-pres = SMP.TracePrimitives.exec-trace-preserves-slot-below g-trace
                       s-after-middle alloc-after-middle reclaim-f slot g-twa g-tnhw slot<reclaim
            g-pres-frame = subst (λ fr → readLoc s-after-g (OnStack fr slot) ≡
                                         readLoc s-after-middle (OnStack fr slot))
                                 oag-frame-middle g-pres
            -- final-trace writes at snd-slot < f-start, so preserves slot ≥ f-start
            -- snd-slot < f-start = suc snd-slot ≤ f-start = f-start ≤ f-start = ≤-refl
            snd<f-start : snd-slot < f-start
            snd<f-start = ≤-refl
            final-twb : TraceWritesBelow f-start final-trace
            final-twb = snd<f-start , tt  -- store-at-slot snd-slot writes at snd-slot < f-start
            final-tnhw : TraceNoHeapWrites final-trace
            final-tnhw = tt
            final-pres = SMP.TracePrimitives.exec-trace-preserves-slot-above final-trace
                           s-after-g alloc-after-g f-start slot final-twb final-tnhw f-start≤slot
            final-pres-frame = subst (λ fr → readLoc s-after-final (OnStack fr slot) ≡
                                             readLoc s-after-g (OnStack fr slot))
                                     frame-preserved-through final-pres
            -- Chain: s-after-final preserves from s-after-f
            chain = trans final-pres-frame (trans g-pres-frame middle-pres-frame)
            -- Use s-final-eq : s-final ≡ s-after-final
        in subst (λ st → readLoc st (OnStack frame slot) ≡ readLoc s-after-f (OnStack frame slot))
                 (sym s-final-eq) chain

      -- Memory agrees on heap (no heap writes in rest-trace)
      rest-mem-heap : ∀ h → readLoc s-final (OnHeap h) ≡ readLoc s-after-f (OnHeap h)
      rest-mem-heap h =
        let -- middle-trace preserves heap from s-after-f to s-after-middle
            middle-tnhw : TraceNoHeapWrites middle-trace
            middle-tnhw = tt
            middle-pres = SMP.TracePrimitives.exec-trace-preserves-heap-loc middle-trace s-after-f alloc-after-f h middle-tnhw
            -- g-trace preserves heap from s-after-middle to s-after-g
            g-pres = SMP.TracePrimitives.exec-trace-preserves-heap-loc g-trace s-after-middle alloc-after-middle h g-tnhw
            -- final-trace preserves heap from s-after-g to s-after-final
            final-tnhw : TraceNoHeapWrites final-trace
            final-tnhw = tt
            final-pres = SMP.TracePrimitives.exec-trace-preserves-heap-loc final-trace s-after-g alloc-after-g h final-tnhw
            -- Chain: s-after-final preserves from s-after-f
            chain = trans final-pres (trans g-pres middle-pres)
            -- Use s-final-eq : s-final ≡ s-after-final
        in subst (λ st → readLoc st (OnHeap h) ≡ readLoc s-after-f (OnHeap h))
                 (sym s-final-eq) chain

      -- Memory agrees on ancestor frames
      rest-mem-ancestors : ∀ f' k → current-frame alloc-after-f-reclaim ≺ f' →
        readLoc s-final (OnStack f' k) ≡ readLoc s-after-f (OnStack f' k)
      rest-mem-ancestors f' k cf≺f' =
        let -- Convert cf≺f' to work with each alloc (all have current-frame = frame)
            frame≺f' : frame ≺ f'
            frame≺f' = subst (_≺ f') oag-frame-reclaim cf≺f'
            -- middle-trace preserves ancestors from s-after-f to s-after-middle
            middle-tnhw : TraceNoHeapWrites middle-trace
            middle-tnhw = tt
            alloc-after-f-cf≺f' : current-frame alloc-after-f ≺ f'
            alloc-after-f-cf≺f' = subst (_≺ f') (sym frame-after-f-eq) frame≺f'
            middle-pres = SMP.TracePrimitives.exec-trace-preserves-ancestor middle-trace s-after-f
                            alloc-after-f f' k alloc-after-f-cf≺f' middle-tnhw
            -- g-trace preserves ancestors from s-after-middle to s-after-g
            alloc-after-middle-cf≺f' : current-frame alloc-after-middle ≺ f'
            alloc-after-middle-cf≺f' = subst (_≺ f') (sym oag-frame-middle) frame≺f'
            g-pres = SMP.TracePrimitives.exec-trace-preserves-ancestor g-trace s-after-middle
                       alloc-after-middle f' k alloc-after-middle-cf≺f' g-tnhw
            -- final-trace preserves ancestors from s-after-g to s-after-final
            final-tnhw : TraceNoHeapWrites final-trace
            final-tnhw = tt
            alloc-after-g-cf≺f' : current-frame alloc-after-g ≺ f'
            alloc-after-g-cf≺f' = subst (_≺ f') (sym frame-preserved-through) frame≺f'
            final-pres = SMP.TracePrimitives.exec-trace-preserves-ancestor final-trace s-after-g
                           alloc-after-g f' k alloc-after-g-cf≺f' final-tnhw
            -- Chain: s-after-final preserves from s-after-f
            chain = trans final-pres (trans g-pres middle-pres)
            -- Use s-final-eq : s-final ≡ s-after-final
        in subst (λ st → readLoc st (OnStack f' k) ≡ readLoc s-after-f (OnStack f' k))
                 (sym s-final-eq) chain

      -- Transfer validity from s-after-f to s-final using positive regions
      valid-at-s-final : ValidAtWF mF alloc-after-f-reclaim (eval primSem f x) fst-loc s-final
      valid-at-s-final = validityWF-mem-preserved-in-regions alloc-after-f-reclaim
                           (eval primSem f x) fst-loc backup-slot f-start s-after-f s-final
                           fst-loc-before-reclaimed backup≤f-start f-start≤reclaim-f
                           rest-mem-input-region rest-mem-fresh-region rest-mem-heap rest-mem-ancestors
                           valid-at-s-after-f

      -- Step 4: Advance frontier from alloc-after-f-reclaim to alloc-final
      fst-valid : ValidAtWF mF alloc-final (eval primSem f x) fst-loc s-final
      fst-valid = validityWF-frontier-advance (eval primSem f x) fst-loc s-final refl
                    (IRResultAWF.slot-monotone result-g) ≤-refl valid-at-s-final

      ----------------------------------------------------------------------
      -- snd-valid: Validity of g's result at snd-loc in s-final
      --
      -- Strategy using POSITIVE BOUNDS (same approach as fst-valid):
      -- 1. reclaim-preserves-validity gives validity at s₂ with alloc-reclaim-g
      -- 2. Transfer validity from s₂ to s-after-g using validityWF-mem-preserved-in-regions
      --    Memory agrees in two disjoint regions:
      --      - Input region: [0, backup-slot) - preserved from before g
      --      - Fresh region: [reclaim-f, reclaim-g) - written by g-trace deterministically
      -- 3. Transfer validity from s-after-g to s-final (final-trace preserves both regions)
      -- 4. Frontier advance is trivial (alloc-reclaim-g = alloc-final)
      ----------------------------------------------------------------------

      -- Alloc state after g's reclaim
      alloc-reclaim-g : AllocState {FS}
      alloc-reclaim-g = record alloc { next-slot = reclaim-g }

      -- Step 1: Get validity at s₂ with alloc-reclaim-g
      valid-s2-reclaimed : ValidAtWF mG alloc-reclaim-g (eval primSem g x) snd-loc s₂
      valid-s2-reclaimed = IRResultAWF.reclaim-preserves-validity result-g

      -- snd-loc is before frontier at alloc-reclaim-g
      snd-loc-before-reclaim-g : BeforeFrontier alloc-reclaim-g snd-loc
      snd-loc-before-reclaim-g = IRResultAWF.reclaim-preserves-result result-g

      -- Region bounds for snd-loc's sub-locations:
      --   input-bound = backup-slot (sub-locations from x are < backup-slot)
      --   fresh-start = reclaim-f (sub-locations from g are ≥ reclaim-f)
      backup≤reclaim-f' : backup-slot ≤ reclaim-f
      backup≤reclaim-f' = backup≤reclaim-f

      reclaim-f≤reclaim-g : reclaim-f ≤ reclaim-g
      reclaim-f≤reclaim-g = IRResultAWF.slot-monotone result-g  -- alloc-after-f-reclaim has next-slot = reclaim-f

      -- Step 2: Memory agreement from s₂ to s-after-g
      -- s₂ = exec g-trace s₁' alloc-after-f-reclaim (recursive call result)
      -- s-after-g = exec g-trace s-after-middle alloc-after-middle

      -- Memory agrees on input region [0, backup-slot)
      -- Both s₂ and s-after-g preserve this from before g runs
      g-mem-input-region : ∀ slot → slot < backup-slot →
        readLoc s-after-g (OnStack frame slot) ≡ readLoc s₂ (OnStack frame slot)
      g-mem-input-region slot slot<backup =
        let -- slot < backup-slot < reclaim-f, so g-trace preserves slot
            slot<reclaim-f : slot < reclaim-f
            slot<reclaim-f = <-≤-trans slot<backup backup≤reclaim-f'
            -- s-after-g preserves slot from s-after-middle (g-trace writes above reclaim-f)
            g-pres = SMP.TracePrimitives.exec-trace-preserves-slot-below g-trace s-after-middle
                       alloc-after-middle reclaim-f slot g-twa g-tnhw slot<reclaim-f
            g-pres-frame = subst (λ fr → readLoc s-after-g (OnStack fr slot) ≡
                                         readLoc s-after-middle (OnStack fr slot))
                                 oag-frame-middle g-pres
            -- s₂ preserves slot from s₁' (g-trace writes above reclaim-f)
            exec-g-pres = SMP.TracePrimitives.exec-trace-preserves-slot-below g-trace s₁'
                            alloc-after-f-reclaim reclaim-f slot g-twa g-tnhw slot<reclaim-f
            s₂-pres = subst (λ st → readLoc st (OnStack frame slot) ≡ readLoc s₁' (OnStack frame slot))
                            (IRResultAWF.trace-correct result-g) exec-g-pres
            -- s₁' has same memory as s₁ at this slot (only regs changed)
            s₁'-eq : readLoc s₁' (OnStack frame slot) ≡ readLoc s₁ (OnStack frame slot)
            s₁'-eq = refl
            -- Now chain back through middle, f, setup to compare with path from s-after-g
            -- Both paths end at same value from s
            -- Path 1: s-after-g <- s-after-middle
            -- We need s-after-middle to agree with s₁' at this slot
            -- Use f-mem-input-region and middle preservation
            slot<fst : slot < fst-slot
            slot<fst = ≤-trans slot<backup (n≤1+n backup-slot)
            middle-twa : TraceWritesAbove fst-slot middle-trace
            middle-twa = ≤-refl , tt
            middle-pres = SMP.TracePrimitives.exec-trace-preserves-slot-below middle-trace
                            s-after-f alloc-after-f fst-slot slot middle-twa tt slot<fst
            middle-pres-frame = subst (λ fr → readLoc s-after-middle (OnStack fr slot) ≡
                                              readLoc s-after-f (OnStack fr slot))
                                      frame-after-f-eq middle-pres
            -- Use f-mem-input-region for s-after-f vs s₁
            f-input-eq = f-mem-input-region slot slot<backup
        in trans g-pres-frame (trans middle-pres-frame (trans f-input-eq (trans (sym s₁'-eq) (sym s₂-pres))))

      -- Memory agrees on fresh region [reclaim-f, reclaim-g)
      -- Both executions of g-trace write same values (deterministic given same Input)
      g-mem-fresh-region : ∀ slot → reclaim-f ≤ slot → slot < reclaim-g →
        readLoc s-after-g (OnStack frame slot) ≡ readLoc s₂ (OnStack frame slot)
      g-mem-fresh-region slot rf≤slot slot<rg =
        let -- slot < reclaim-g ≤ max-slot-g
            slot<max : slot < max-slot-g
            slot<max = <-≤-trans slot<rg (IRResultAWF.max-slot-geq-final result-g)
            -- Use exec-trace-mem-deterministic for g-trace
            mem-det = SMP.TraceOutputDeterminism.exec-trace-mem-deterministic g-trace
                        s-after-middle s₁' alloc-after-middle alloc-after-f-reclaim reclaim-f max-slot-g
                        not-halted-after-middle (IRResultAWF.not-halted result-f) oag-frame-eq oag-input-eq
                        g-tsra (IRResultAWF.trace-slot-reads-below result-g)
                        g-twa g-twb g-tnhw oag-mem-agree
                        slot rf≤slot slot<max
            -- Convert frames
            mem-det-frame : readLoc s-after-g (OnStack frame slot) ≡
                            readLoc (proj₁ (exec-trace g-trace s₁' alloc-after-f-reclaim)) (OnStack frame slot)
            mem-det-frame = subst₂ (λ f1 f2 → readLoc s-after-g (OnStack f1 slot) ≡
                                              readLoc (proj₁ (exec-trace g-trace s₁' alloc-after-f-reclaim)) (OnStack f2 slot))
                                   oag-frame-middle oag-frame-reclaim mem-det
            -- Convert exec result to s₂ using trace-correct
            s₂-eq : readLoc (proj₁ (exec-trace g-trace s₁' alloc-after-f-reclaim)) (OnStack frame slot) ≡
                    readLoc s₂ (OnStack frame slot)
            s₂-eq = cong (λ st → readLoc st (OnStack frame slot)) (IRResultAWF.trace-correct result-g)
        in trans mem-det-frame s₂-eq

      -- Memory agrees on heap (no heap writes in g-trace)
      g-mem-heap : ∀ h → readLoc s-after-g (OnHeap h) ≡ readLoc s₂ (OnHeap h)
      g-mem-heap h =
        let -- s-after-g preserves heap from s-after-middle
            g-heap = SMP.TracePrimitives.exec-trace-preserves-heap-loc g-trace
                       s-after-middle alloc-after-middle h g-tnhw
            -- s₂ preserves heap from s₁'
            exec-g-heap = SMP.TracePrimitives.exec-trace-preserves-heap-loc g-trace
                            s₁' alloc-after-f-reclaim h g-tnhw
            s₂-heap = subst (λ st → readLoc st (OnHeap h) ≡ readLoc s₁' (OnHeap h))
                            (IRResultAWF.trace-correct result-g) exec-g-heap
            -- s₁' has same heap as s₁ (only regs changed)
            s₁'-heap : readLoc s₁' (OnHeap h) ≡ readLoc s₁ (OnHeap h)
            s₁'-heap = refl
            -- Chain back through middle, f, setup
            middle-heap = SMP.TracePrimitives.exec-trace-preserves-heap-loc middle-trace
                            s-after-f alloc-after-f h tt
            -- Use f-mem-heap
            f-heap-eq = f-mem-heap h
        in trans g-heap (trans middle-heap (trans f-heap-eq (trans (sym s₁'-heap) (sym s₂-heap))))

      -- Memory agrees on ancestor frames
      g-mem-ancestors : ∀ f' k → current-frame alloc-reclaim-g ≺ f' →
        readLoc s-after-g (OnStack f' k) ≡ readLoc s₂ (OnStack f' k)
      g-mem-ancestors f' k cf≺f' =
        let -- current-frame alloc-reclaim-g = frame
            frame≺f' : frame ≺ f'
            frame≺f' = cf≺f'
            -- s-after-g preserves ancestors from s-after-middle
            alloc-after-middle-cf≺f' : current-frame alloc-after-middle ≺ f'
            alloc-after-middle-cf≺f' = subst (_≺ f') (sym oag-frame-middle) frame≺f'
            g-anc = SMP.TracePrimitives.exec-trace-preserves-ancestor g-trace
                      s-after-middle alloc-after-middle f' k alloc-after-middle-cf≺f' g-tnhw
            -- s₂ preserves ancestors from s₁'
            alloc-f-reclaim-cf≺f' : current-frame alloc-after-f-reclaim ≺ f'
            alloc-f-reclaim-cf≺f' = frame≺f'
            exec-g-anc = SMP.TracePrimitives.exec-trace-preserves-ancestor g-trace
                           s₁' alloc-after-f-reclaim f' k alloc-f-reclaim-cf≺f' g-tnhw
            s₂-anc = subst (λ st → readLoc st (OnStack f' k) ≡ readLoc s₁' (OnStack f' k))
                           (IRResultAWF.trace-correct result-g) exec-g-anc
            -- s₁' has same stack as s₁
            s₁'-anc : readLoc s₁' (OnStack f' k) ≡ readLoc s₁ (OnStack f' k)
            s₁'-anc = refl
            -- Chain back through middle, f
            alloc-after-f-cf≺f' : current-frame alloc-after-f ≺ f'
            alloc-after-f-cf≺f' = subst (_≺ f') (sym frame-after-f-eq) frame≺f'
            middle-anc = SMP.TracePrimitives.exec-trace-preserves-ancestor middle-trace
                           s-after-f alloc-after-f f' k alloc-after-f-cf≺f' tt
            -- Use f-mem-ancestors
            f-anc-eq = f-mem-ancestors f' k frame≺f'
        in trans g-anc (trans middle-anc (trans f-anc-eq (trans (sym s₁'-anc) (sym s₂-anc))))

      -- Transfer validity from s₂ to s-after-g using positive regions
      valid-at-s-after-g : ValidAtWF mG alloc-reclaim-g (eval primSem g x) snd-loc s-after-g
      valid-at-s-after-g = validityWF-mem-preserved-in-regions alloc-reclaim-g
                             (eval primSem g x) snd-loc backup-slot reclaim-f s₂ s-after-g
                             snd-loc-before-reclaim-g backup≤reclaim-f' reclaim-f≤reclaim-g
                             g-mem-input-region g-mem-fresh-region g-mem-heap g-mem-ancestors
                             valid-s2-reclaimed

      -- Step 3: Transfer validity from s-after-g to s-final
      -- final-trace writes at snd-slot which is in [backup-slot, f-start) ⊂ [backup-slot, reclaim-f)
      -- So it doesn't write to input region [0, backup-slot) or fresh region [reclaim-f, reclaim-g)

      -- Memory agrees on input region [0, backup-slot): final-trace writes above backup-slot
      final-mem-input-region : ∀ slot → slot < backup-slot →
        readLoc s-final (OnStack frame slot) ≡ readLoc s-after-g (OnStack frame slot)
      final-mem-input-region slot slot<backup =
        let slot<snd : slot < snd-slot
            slot<snd = ≤-trans slot<backup (≤-trans (n≤1+n backup-slot) (n≤1+n fst-slot))
            final-twa : TraceWritesAbove snd-slot final-trace
            final-twa = ≤-refl , tt
            final-pres = SMP.TracePrimitives.exec-trace-preserves-slot-below final-trace
                           s-after-g alloc-after-g snd-slot slot final-twa tt slot<snd
            final-pres-frame = subst (λ fr → readLoc s-after-final (OnStack fr slot) ≡
                                             readLoc s-after-g (OnStack fr slot))
                                     frame-preserved-through final-pres
        in subst (λ st → readLoc st (OnStack frame slot) ≡ readLoc s-after-g (OnStack frame slot))
                 (sym s-final-eq) final-pres-frame

      -- Memory agrees on fresh region [reclaim-f, reclaim-g): final-trace writes below reclaim-f
      final-mem-fresh-region : ∀ slot → reclaim-f ≤ slot → slot < reclaim-g →
        readLoc s-final (OnStack frame slot) ≡ readLoc s-after-g (OnStack frame slot)
      final-mem-fresh-region slot rf≤slot _ =
        let final-twb : TraceWritesBelow reclaim-f final-trace
            final-twb = snd-slot<reclaim-f , tt  -- snd-slot < f-start ≤ reclaim-f
            final-pres = SMP.TracePrimitives.exec-trace-preserves-slot-above final-trace
                           s-after-g alloc-after-g reclaim-f slot final-twb tt rf≤slot
            final-pres-frame = subst (λ fr → readLoc s-after-final (OnStack fr slot) ≡
                                             readLoc s-after-g (OnStack fr slot))
                                     frame-preserved-through final-pres
        in subst (λ st → readLoc st (OnStack frame slot) ≡ readLoc s-after-g (OnStack frame slot))
                 (sym s-final-eq) final-pres-frame

      -- Memory agrees on heap (no heap writes in final-trace)
      final-mem-heap : ∀ h → readLoc s-final (OnHeap h) ≡ readLoc s-after-g (OnHeap h)
      final-mem-heap h =
        let final-heap = SMP.TracePrimitives.exec-trace-preserves-heap-loc final-trace
                           s-after-g alloc-after-g h tt
        in subst (λ st → readLoc st (OnHeap h) ≡ readLoc s-after-g (OnHeap h))
                 (sym s-final-eq) final-heap

      -- Memory agrees on ancestor frames
      final-mem-ancestors : ∀ f' k → current-frame alloc-reclaim-g ≺ f' →
        readLoc s-final (OnStack f' k) ≡ readLoc s-after-g (OnStack f' k)
      final-mem-ancestors f' k cf≺f' =
        let frame≺f' : frame ≺ f'
            frame≺f' = cf≺f'
            alloc-after-g-cf≺f' : current-frame alloc-after-g ≺ f'
            alloc-after-g-cf≺f' = subst (_≺ f') (sym frame-preserved-through) frame≺f'
            final-anc = SMP.TracePrimitives.exec-trace-preserves-ancestor final-trace
                          s-after-g alloc-after-g f' k alloc-after-g-cf≺f' tt
        in subst (λ st → readLoc st (OnStack f' k) ≡ readLoc s-after-g (OnStack f' k))
                 (sym s-final-eq) final-anc

      -- Transfer validity from s-after-g to s-final using positive regions
      snd-valid-at-s-final : ValidAtWF mG alloc-reclaim-g (eval primSem g x) snd-loc s-final
      snd-valid-at-s-final = validityWF-mem-preserved-in-regions alloc-reclaim-g
                               (eval primSem g x) snd-loc backup-slot reclaim-f s-after-g s-final
                               snd-loc-before-reclaim-g backup≤reclaim-f' reclaim-f≤reclaim-g
                               final-mem-input-region final-mem-fresh-region final-mem-heap final-mem-ancestors
                               valid-at-s-after-g

      -- Step 4: Frontier advance (trivial since alloc-reclaim-g and alloc-final both have next-slot = reclaim-g)
      snd-valid : ValidAtWF mG alloc-final (eval primSem g x) snd-loc s-final
      snd-valid = validityWF-frontier-advance (eval primSem g x) snd-loc s-final refl ≤-refl ≤-refl snd-valid-at-s-final

      ------------------------------------------------------------------------
      -- Final pair validity
      ------------------------------------------------------------------------
      pair-valid-wf-final : ValidAtWF m alloc-final
                              (pair (eval primSem f x) (eval primSem g x)) pair-loc s-final
      pair-valid-wf-final = valid-pair-wf fst-ptr snd-ptr fst-before snd-before
                              sucLoc-pair-before fst-valid snd-valid
