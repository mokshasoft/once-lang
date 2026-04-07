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
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; n≤1+n; +-comm; +-assoc; +-suc; +-identityʳ; +-monoˡ-≤; +-monoʳ-≤; <-≤-trans; <⇒≤; m≤m⊔n; m≤n⊔m; ⊔-lub)
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
open import Once.CCC.Target.X86-64.Types
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

  -- Types from ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound primSem
    using (ValidAtWF; IRResultAWF; RecDispatcherWF;
           valid-pair-wf;
           validityWF-mem-only; validityWF-mem-preserved;
           validityWF-frontier-advance;
           validityWF-trace-preserves)

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
    next-slot alloc +ℕ ir-stack-requirement (⟨ f , g ⟩ m) ≤ frame-capacity alloc →
    IRResultAWF m (⟨ f , g ⟩ m) x s alloc

  run-pair {A} {B} {C} mIn f g m rec-wf x input-loc s alloc
           input-valid-wf input-before not-halted rdi-eq combined-cap =
    record
      { result-loc = pair-loc
      ; final-state = s-final
      ; final-alloc = alloc-final
      ; trace = pair-trace
      ; trace-correct = refl  -- s-final DEFINED by trace
      ; alloc-correct = SMP.!!
      ; result-valid-wf = pair-valid-wf-final
      ; result-before = pair-before
      ; rax-is-result = rax-eq
      ; not-halted = not-halted-final
      ; frame-preserved = refl
      ; slot-monotone = slot-monotone-pair
      ; heap-monotone = ≤-refl
      ; capacity-preserved = refl
      ; mem-preserved-before = mem-preserved-pair
      ; reclaimable-slot = pair-reclaim
      ; reclaim-monotone = pair-reclaim-monotone
      ; reclaim-bounded = ≤-refl
      ; reclaim-preserves-result = λ _ → pair-before
      ; reclaim-preserves-validity = λ _ → pair-valid-wf-final
      ; reclaim-size-bound = pair-reclaim-size-bound
      ; max-slot-written = pair-max-slot
      ; max-slot-geq-reclaim = pair-max-slot-geq-reclaim
      ; max-slot-usage-bound = pair-max-slot-bound
      ; max-slot-eq-reclaim = SMP.!!
      ; frontier-slot-stable = pair-frontier-stable
      ; trace-writes-above = pair-trace-writes-above
      ; trace-slot-reads-above = pair-trace-slot-reads-above
      ; trace-writes-below = pair-trace-writes-below
      ; trace-slot-reads-below = pair-trace-slot-reads-below
      ; trace-preserves-capacity = pair-trace-preserves-capacity
      ; trace-no-heap-writes = pair-trace-no-heap-writes
      ; trace-preserves-halted = pair-trace-preserves-halted
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
      -- Helper: n + 2 ≡ suc (suc n)
      plus-two : ∀ n → n +ℕ 2 ≡ suc (suc n)
      plus-two n = trans (+-suc n 1) (cong suc (trans (+-suc n 0) (cong suc (+-identityʳ n))))

      combined-cap-expanded : (backup-slot +ℕ 1) +ℕ rf +ℕ rg +ℕ 2 ≤ frame-capacity alloc
      combined-cap-expanded = ⟨,⟩-capacity-for-pair f g m backup-slot (frame-capacity alloc) combined-cap

      combined-cap-f : f-start +ℕ rf ≤ frame-capacity alloc
      combined-cap-f = ≤-trans step1 (≤-trans step2 combined-cap-suc)
        where
          combined-cap-suc : suc backup-slot +ℕ rf +ℕ rg +ℕ 2 ≤ frame-capacity alloc
          combined-cap-suc = subst (λ x → x +ℕ rf +ℕ rg +ℕ 2 ≤ frame-capacity alloc)
                               (+-comm backup-slot 1) combined-cap-expanded
          step1 : f-start +ℕ rf ≤ f-start +ℕ rf +ℕ rg
          step1 = m≤m+n (f-start +ℕ rf) rg
          step2-eq : f-start +ℕ rf +ℕ rg ≡ suc backup-slot +ℕ rf +ℕ rg +ℕ 2
          step2-eq = sym (cong suc (plus-two (backup-slot +ℕ rf +ℕ rg)))
          step2 : f-start +ℕ rf +ℕ rg ≤ suc backup-slot +ℕ rf +ℕ rg +ℕ 2
          step2 = subst (f-start +ℕ rf +ℕ rg ≤_) refl
                    (subst (_≤ suc backup-slot +ℕ rf +ℕ rg +ℕ 2) (sym step2-eq) ≤-refl)

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
                        input-valid-wf-at-f-start input-before-at-f-start not-halted rdi-eq combined-cap-f
      mF = proj₁ f-exec-result
      result-f = proj₂ f-exec-result
      s₁ = IRResultAWF.final-state result-f
      fst-loc = IRResultAWF.result-loc result-f
      f-trace = IRResultAWF.trace result-f

      ------------------------------------------------------------------------
      -- Reclaim after f
      ------------------------------------------------------------------------
      reclaim-f = IRResultAWF.reclaimable-slot result-f

      reclaim-f-bound : reclaim-f ≤ f-start +ℕ rf
      reclaim-f-bound = IRResultAWF.reclaim-size-bound result-f

      reclaim-f-fits : reclaim-f ≤ frame-capacity alloc
      reclaim-f-fits = ≤-trans reclaim-f-bound combined-cap-f

      reclaim-f-above-f-start : f-start ≤ reclaim-f
      reclaim-f-above-f-start = IRResultAWF.reclaim-monotone result-f

      alloc-after-f-reclaim : AllocState {FS}
      alloc-after-f-reclaim = record alloc { next-slot = reclaim-f }

      ------------------------------------------------------------------------
      -- Capacity for g
      ------------------------------------------------------------------------
      combined-cap-g : reclaim-f +ℕ rg ≤ frame-capacity alloc
      combined-cap-g =
        let step1 : reclaim-f +ℕ rg ≤ (f-start +ℕ rf) +ℕ rg
            step1 = +-monoˡ-≤ rg reclaim-f-bound
            step2-eq : (f-start +ℕ rf) +ℕ rg ≡ suc backup-slot +ℕ rf +ℕ rg +ℕ 2
            step2-eq = sym (cong suc (plus-two (backup-slot +ℕ rf +ℕ rg)))
            combined-cap-suc : suc backup-slot +ℕ rf +ℕ rg +ℕ 2 ≤ frame-capacity alloc
            combined-cap-suc = subst (λ x → x +ℕ rf +ℕ rg +ℕ 2 ≤ frame-capacity alloc)
                                 (+-comm backup-slot 1) combined-cap-expanded
            step2 : (f-start +ℕ rf) +ℕ rg ≤ suc backup-slot +ℕ rf +ℕ rg +ℕ 2
            step2 = subst ((f-start +ℕ rf) +ℕ rg ≤_) refl
                      (subst (_≤ suc backup-slot +ℕ rf +ℕ rg +ℕ 2) (sym step2-eq) ≤-refl)
        in ≤-trans step1 (≤-trans step2 combined-cap-suc)

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
                            (λ loc bf → IRResultAWF.mem-preserved-before result-f loc (bf-to-after-pair-slots loc bf))
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
                        (IRResultAWF.not-halted result-f) rdi-eq₁ combined-cap-g
      mG = proj₁ g-exec-result
      result-g = proj₂ g-exec-result
      s₂ = IRResultAWF.final-state result-g
      snd-loc = IRResultAWF.result-loc result-g
      g-trace = IRResultAWF.trace result-g

      ------------------------------------------------------------------------
      -- Reclaim after g
      ------------------------------------------------------------------------
      reclaim-g = IRResultAWF.reclaimable-slot result-g

      reclaim-g-bound : reclaim-g ≤ reclaim-f +ℕ rg
      reclaim-g-bound = IRResultAWF.reclaim-size-bound result-g

      reclaim-g-fits : reclaim-g ≤ frame-capacity alloc
      reclaim-g-fits = ≤-trans reclaim-g-bound combined-cap-g

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
                                    (≤-trans reclaim-f-above-f-start (IRResultAWF.reclaim-monotone result-g))))

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

      f-tpc : TracePreservesCapacity f-trace
      f-tpc = IRResultAWF.trace-preserves-capacity result-f

      f-tph : TracePreservesHaltedP f-trace
      f-tph = IRResultAWF.trace-preserves-halted result-f

      g-twa : TraceWritesAbove reclaim-f g-trace
      g-twa = IRResultAWF.trace-writes-above result-g

      g-twb : TraceWritesBelow (IRResultAWF.max-slot-written result-g) g-trace
      g-twb = IRResultAWF.trace-writes-below result-g

      g-tnhw : TraceNoHeapWrites g-trace
      g-tnhw = IRResultAWF.trace-no-heap-writes result-g

      g-tpc : TracePreservesCapacity g-trace
      g-tpc = IRResultAWF.trace-preserves-capacity result-g

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

      pair-max-slot-geq-reclaim : pair-reclaim ≤ pair-max-slot
      pair-max-slot-geq-reclaim = ≤-trans (IRResultAWF.max-slot-geq-reclaim result-g) (m≤n⊔m max-slot-f max-slot-g)

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
      fst<reclaim-g = <-≤-trans fst-slot<reclaim-f (IRResultAWF.reclaim-monotone result-g)

      snd<reclaim-g : snd-slot < reclaim-g
      snd<reclaim-g = <-≤-trans snd-slot<reclaim-f (IRResultAWF.reclaim-monotone result-g)

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
                    (≤-trans (IRResultAWF.max-slot-geq-reclaim result-f) max-slot-f≤pair)

      snd<bound : snd-slot < pair-max-slot
      snd<bound = <-≤-trans snd-slot<reclaim-f
                    (≤-trans (IRResultAWF.max-slot-geq-reclaim result-f) max-slot-f≤pair)

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

      ------------------------------------------------------------------------
      -- Trace preserves capacity
      ------------------------------------------------------------------------
      pair-trace-preserves-capacity : TracePreservesCapacity pair-trace
      pair-trace-preserves-capacity =
        tpc-∷ ipc-mov-to-output
        (tpc-∷ ipc-store-at-slot
        (tpc-++ f-tpc
        (tpc-∷ ipc-store-at-slot
        (tpc-∷ ipc-restore-input
        (tpc-++ g-tpc
        (tpc-∷ ipc-store-at-slot
        (tpc-∷ ipc-lea-slot tpc-[])))))))

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
      -- PROOF OBLIGATION: Requires trace determinism - showing that:
      --   s-after-f = proj₁ (exec-trace f-trace s-after-setup alloc-after-setup)
      --   has the same Output register as
      --   s₁ = IRResultAWF.final-state result-f (where rax-is-result gives Output ≡ fst-loc)
      -- The two differ in starting state (s-after-setup vs s) and alloc (alloc-after-setup vs alloc-after-pair-slots)
      -- but the trace and relevant register/memory inputs are the same.
      output-after-f : readReg (regs s-after-f) Output ≡ fst-loc
      output-after-f = SMP.!!

      -- Output at s-after-g contains snd-loc
      -- PROOF OBLIGATION: Same as output-after-f, for g instead of f
      output-after-g : readReg (regs s-after-g) Output ≡ snd-loc
      output-after-g = SMP.!!

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
                     (IRResultAWF.reclaim-monotone result-g)
                     ≤-refl
                     fst-loc
                     (IRResultAWF.reclaim-preserves-result result-f reclaim-f-fits)

      snd-before : BeforeFrontier alloc-final snd-loc
      snd-before = frontier-monotone (record alloc { next-slot = reclaim-g }) alloc-final
                     refl ≤-refl ≤-refl snd-loc
                     (IRResultAWF.reclaim-preserves-result result-g reclaim-g-fits)

      -- sucLoc pair-loc = OnStack frame snd-slot
      sucLoc-pair-before : BeforeFrontier alloc-final (sucLoc pair-loc)
      sucLoc-pair-before = stack-before refl snd<reclaim-g

      -- f's result validity at final state
      -- PROOF OBLIGATION: Transfer validity from s₁ (recursive call result) to s-final (our decomposition)
      -- Strategy: Use IRResultAWF.reclaim-preserves-validity to get validity at reclaim-f,
      -- then use validityWF-trace-preserves to show it's preserved through the rest of the trace.
      -- This depends on output-after-f (trace determinism) to relate s₁ and s-after-f.
      fst-valid : ValidAtWF mF alloc-final (eval primSem f x) fst-loc s-final
      fst-valid = SMP.!!

      -- g's result validity at final state
      -- PROOF OBLIGATION: Same as fst-valid, for g instead of f
      snd-valid : ValidAtWF mG alloc-final (eval primSem g x) snd-loc s-final
      snd-valid = SMP.!!

      ------------------------------------------------------------------------
      -- Final pair validity
      ------------------------------------------------------------------------
      pair-valid-wf-final : ValidAtWF m alloc-final
                              (pair (eval primSem f x) (eval primSem g x)) pair-loc s-final
      pair-valid-wf-final = valid-pair-wf fst-ptr snd-ptr fst-before snd-before
                              sucLoc-pair-before fst-valid snd-valid
