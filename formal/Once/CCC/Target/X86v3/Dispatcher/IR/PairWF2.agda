------------------------------------------------------------------------
-- Once.CCC.Target.X86v3.IR.PairWF2
--
-- PairWF proof using SMPrimitives for memory reasoning.
--
-- NOTE: Due to duplicate type definitions between SMCore and SlotMachine,
-- we import SMPrimitives qualified and use it for the memory primitives.
------------------------------------------------------------------------

module Once.CCC.Target.X86v3.Dispatcher.IR.PairWF2 where

open import Data.Nat using (ℕ; suc; _<_; _≤_; s≤s; z≤n) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; n≤1+n; +-comm; +-assoc; +-monoˡ-≤; +-monoʳ-≤; m<m+n; <-≤-trans; <⇒≢)
open import Data.Bool using (false)
open import Data.Unit using (tt)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym; cong; subst)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.SlotMachine hiding (AllocMode; Stack; Heap)
open import Once.CCC.Target.X86v3.Types
open import Once.CCC.IR
open import Once.CCC.Target.X86v3.Dispatcher.Allocation hiding (AllocMode)
open import Once.CCC.Target.X86v3.Dispatcher.ClosureWellFormed

-- Import SMPrimitives qualified for memory reasoning primitives
import Once.CCC.SMPrimitives as SMP

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
           validityWF-mem-preserved-excluding)

  -- Helper lemmas
  open import Once.CCC.Target.X86v3.Dispatcher.DispatcherArithmeticLemma
    using (suc<+2)
  open import Once.CCC.Target.X86v3.Dispatcher.FrontierLemma
  open FrontierLemmas {FS}
    using (at-frontier-before-pair)

  ------------------------------------------------------------------------
  -- run-pair: Same type as PairWF.run-pair
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
      ; final-alloc = alloc₃
      ; trace = pair-trace
      ; trace-correct = refl  -- s-final DEFINED by trace
      ; result-valid-wf = pair-valid-wf-final
      ; result-before = pair-before
      ; rax-is-result = rax-eq
      ; not-halted = not-halted-final
      ; frame-preserved = refl
      ; slot-monotone = slot-monotone-pair
      ; heap-monotone = ≤-refl
      ; heap-preserved = refl
      ; capacity-preserved = refl
      ; mem-preserved-before = mem-preserved-pair
      ; reclaimable-slot = pair-reclaim
      ; reclaim-monotone = pair-reclaim-monotone
      ; reclaim-bounded = ≤-refl
      ; reclaim-preserves-result = λ _ → pair-before
      ; reclaim-preserves-validity = λ _ → pair-valid-wf-final
      ; reclaim-size-bound = pair-reclaim-size-bound
      ; frontier-slot-stable = pair-frontier-stable
      ; trace-writes-above = pair-trace-writes-above
      ; trace-slot-reads-above = pair-trace-slot-reads-above
      ; trace-writes-below = pair-trace-writes-below
      ; trace-slot-reads-below = pair-trace-slot-reads-below
      ; trace-preserves-capacity = pair-trace-preserves-capacity
      ; trace-no-store-indirect = pair-trace-no-store-indirect
      }
    where
      -- Abbreviations
      rf = ir-stack-requirement f
      rg = ir-stack-requirement g
      req-pair = ir-stack-requirement (⟨ f , g ⟩ m)
      ps : ℕ
      ps = 2
      ps≥1 : 1 ≤ ps
      ps≥1 = s≤s z≤n
      ps≥2 : 2 ≤ ps
      ps≥2 = ≤-refl
      frame = current-frame alloc
      backup-slot = next-slot alloc

      ----------------------------------------------------------------------
      -- Capacity derivations
      ----------------------------------------------------------------------
      alloc-after-backup : AllocState {FS}
      alloc-after-backup = record alloc { next-slot = suc backup-slot }

      combined-cap-expanded : (backup-slot +ℕ 1) +ℕ rf +ℕ rg +ℕ ps ≤ frame-capacity alloc
      combined-cap-expanded = ⟨,⟩-capacity-for-pair f g m backup-slot (frame-capacity alloc) combined-cap

      combined-cap-suc : suc backup-slot +ℕ rf +ℕ rg +ℕ ps ≤ frame-capacity alloc
      combined-cap-suc = subst (λ x → x +ℕ rf +ℕ rg +ℕ ps ≤ frame-capacity alloc)
                           (+-comm backup-slot 1) combined-cap-expanded

      combined-cap-f : suc backup-slot +ℕ rf ≤ frame-capacity alloc
      combined-cap-f = ≤-trans (m≤m+n (suc backup-slot +ℕ rf) (rg +ℕ ps))
                         (subst (_≤ frame-capacity alloc)
                           (+-assoc (suc backup-slot +ℕ rf) rg ps) combined-cap-suc)

      input-before-after-backup : BeforeFrontier alloc-after-backup input-loc
      input-before-after-backup = frontier-monotone alloc alloc-after-backup refl
                                    (n≤1+n backup-slot) ≤-refl input-loc input-before

      bf-to-after-backup : ∀ loc → BeforeFrontier alloc loc → BeforeFrontier alloc-after-backup loc
      bf-to-after-backup loc bf = frontier-monotone alloc alloc-after-backup refl
                                    (n≤1+n backup-slot) ≤-refl loc bf

      input-valid-wf-after-backup : ValidAtWF mIn alloc-after-backup x input-loc s
      input-valid-wf-after-backup = validityWF-frontier-advance x input-loc s refl
                                      (n≤1+n backup-slot) ≤-refl input-valid-wf

      ----------------------------------------------------------------------
      -- Run f via recursive dispatch
      ----------------------------------------------------------------------
      f-exec-result : ∃[ mOut ] IRResultAWF mOut f x s alloc-after-backup
      f-exec-result = rec-wf mIn f (⟨,⟩-f-smaller f g {m}) x input-loc s alloc-after-backup
                        input-valid-wf-after-backup input-before-after-backup not-halted rdi-eq combined-cap-f
      mF = proj₁ f-exec-result
      result-f = proj₂ f-exec-result
      s₁ = IRResultAWF.final-state result-f
      fst-loc = IRResultAWF.result-loc result-f

      ----------------------------------------------------------------------
      -- Reclaim after f
      ----------------------------------------------------------------------
      reclaim-f = IRResultAWF.reclaimable-slot result-f

      reclaim-f-bound : reclaim-f ≤ suc backup-slot +ℕ rf
      reclaim-f-bound = IRResultAWF.reclaim-size-bound result-f

      reclaim-f-fits : reclaim-f ≤ frame-capacity alloc
      reclaim-f-fits = ≤-trans reclaim-f-bound combined-cap-f

      reclaim-f-above-backup : suc backup-slot ≤ reclaim-f
      reclaim-f-above-backup = IRResultAWF.reclaim-monotone result-f

      alloc₁-reclaimed : AllocState {FS}
      alloc₁-reclaimed = record alloc { next-slot = reclaim-f }

      ----------------------------------------------------------------------
      -- Capacity for g
      ----------------------------------------------------------------------
      combined-cap-g : reclaim-f +ℕ rg ≤ frame-capacity alloc
      combined-cap-g = ≤-trans (+-monoˡ-≤ rg reclaim-f-bound)
                         (≤-trans (m≤m+n (suc backup-slot +ℕ rf +ℕ rg) ps) combined-cap-suc)

      input-before₁-reclaimed : BeforeFrontier alloc₁-reclaimed input-loc
      input-before₁-reclaimed = frontier-monotone alloc alloc₁-reclaimed refl
                                  (≤-trans (n≤1+n backup-slot) reclaim-f-above-backup)
                                  ≤-refl input-loc input-before

      input-valid-wf-s1 : ValidAtWF mIn alloc x input-loc s₁
      input-valid-wf-s1 = validityWF-mem-preserved x input-loc s s₁ input-before
                            (λ loc bf → IRResultAWF.mem-preserved-before result-f loc (bf-to-after-backup loc bf))
                            input-valid-wf

      input-valid-wf₁-reclaimed : ValidAtWF mIn alloc₁-reclaimed x input-loc s₁
      input-valid-wf₁-reclaimed = validityWF-frontier-advance x input-loc s₁ refl
                                    (≤-trans (n≤1+n backup-slot) reclaim-f-above-backup)
                                    ≤-refl input-valid-wf-s1

      s₁' = record s₁ { regs = writeReg (regs s₁) Input input-loc }
      rdi-eq₁ : readReg (regs s₁') Input ≡ input-loc
      rdi-eq₁ = writeReg-same (regs s₁) Input input-loc

      input-valid-wf₁' : ValidAtWF mIn alloc₁-reclaimed x input-loc s₁'
      input-valid-wf₁' = validityWF-mem-only x input-loc s₁ s₁' refl refl input-valid-wf₁-reclaimed

      ----------------------------------------------------------------------
      -- Run g via recursive dispatch
      ----------------------------------------------------------------------
      g-exec-result : ∃[ mOut ] IRResultAWF mOut g x s₁' alloc₁-reclaimed
      g-exec-result = rec-wf mIn g (⟨,⟩-g-smaller f g {m}) x input-loc s₁' alloc₁-reclaimed
                        input-valid-wf₁' input-before₁-reclaimed
                        (IRResultAWF.not-halted result-f) rdi-eq₁ combined-cap-g
      mG = proj₁ g-exec-result
      result-g = proj₂ g-exec-result
      s₂ = IRResultAWF.final-state result-g
      snd-loc = IRResultAWF.result-loc result-g

      ----------------------------------------------------------------------
      -- Pair allocation
      ----------------------------------------------------------------------
      reclaim-g = IRResultAWF.reclaimable-slot result-g

      reclaim-g-bound : reclaim-g ≤ reclaim-f +ℕ rg
      reclaim-g-bound = IRResultAWF.reclaim-size-bound result-g

      reclaim-g-fits : reclaim-g ≤ frame-capacity alloc
      reclaim-g-fits = ≤-trans reclaim-g-bound (≤-trans (+-monoˡ-≤ rg reclaim-f-bound)
                         (≤-trans (m≤m+n (suc backup-slot +ℕ rf +ℕ rg) ps) combined-cap-suc))

      pair-loc = OnStack frame reclaim-g
      fst-slot = reclaim-g
      snd-slot = suc reclaim-g
      fst-loc-stack : ValueLocation FS
      fst-loc-stack = OnStack frame fst-slot
      snd-loc-stack : ValueLocation FS
      snd-loc-stack = OnStack frame snd-slot
      backup-loc : ValueLocation FS
      backup-loc = OnStack frame backup-slot

      alloc₃ : AllocState {FS}
      alloc₃ = record alloc { next-slot = reclaim-g +ℕ ps }

      ----------------------------------------------------------------------
      -- TRACE CONSTRUCTION (identical to PairWF)
      ----------------------------------------------------------------------
      f-trace = IRResultAWF.trace result-f
      g-trace = IRResultAWF.trace result-g

      pair-trace : AbstractTrace
      pair-trace = mov-to-output ∷ store-at-slot backup-slot ∷
                   f-trace ++
                   store-at-slot fst-slot ∷ restore-input backup-slot ∷
                   g-trace ++
                   store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []

      ----------------------------------------------------------------------
      -- s-final DEFINED by trace (makes trace-correct = refl)
      ----------------------------------------------------------------------
      s-final : LocState FS
      s-final = proj₁ (exec-trace pair-trace s alloc)

      ----------------------------------------------------------------------
      -- TRACE DECOMPOSITION
      -- Define intermediate states for proving properties
      ----------------------------------------------------------------------

      -- Trace segments
      setup-trace : AbstractTrace
      setup-trace = mov-to-output ∷ store-at-slot backup-slot ∷ []

      middle-trace : AbstractTrace
      middle-trace = store-at-slot fst-slot ∷ restore-input backup-slot ∷ []

      final-trace : AbstractTrace
      final-trace = store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []

      -- Intermediate states
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

      -- Halted propagation helpers (use SMPrimitives halted preservation)
      setup-tph : TracePreservesHaltedP setup-trace
      setup-tph = tph-∷ iph-mov-to-output (tph-∷ iph-store-at-slot tph-[])

      not-halted-after-setup : halted s-after-setup ≡ false
      not-halted-after-setup = exec-trace-preserves-halted setup-trace s alloc not-halted setup-tph

      ----------------------------------------------------------------------
      -- POSITIVE WRITE CHARACTERIZATION from sub-IRs
      -- These use SMPrimitives predicates
      ----------------------------------------------------------------------
      f-writes-above : SMP.TraceWritesAbove (suc backup-slot) f-trace
      f-writes-above = IRResultAWF.trace-writes-above result-f

      f-writes-below : SMP.TraceWritesBelow reclaim-f f-trace
      f-writes-below = IRResultAWF.trace-writes-below result-f

      f-tnsi : SMP.TraceNoStoreIndirect f-trace
      f-tnsi = IRResultAWF.trace-no-store-indirect result-f

      g-writes-above : SMP.TraceWritesAbove reclaim-f g-trace
      g-writes-above = IRResultAWF.trace-writes-above result-g

      g-writes-below : SMP.TraceWritesBelow reclaim-g g-trace
      g-writes-below = IRResultAWF.trace-writes-below result-g

      g-tnsi : SMP.TraceNoStoreIndirect g-trace
      g-tnsi = IRResultAWF.trace-no-store-indirect result-g

      f-tpc : TracePreservesCapacity f-trace
      f-tpc = IRResultAWF.trace-preserves-capacity result-f

      g-tpc : TracePreservesCapacity g-trace
      g-tpc = IRResultAWF.trace-preserves-capacity result-g

      f-reads-above : SMP.TraceSlotReadsAbove (suc backup-slot) f-trace
      f-reads-above = IRResultAWF.trace-slot-reads-above result-f

      g-reads-above : SMP.TraceSlotReadsAbove reclaim-f g-trace
      g-reads-above = IRResultAWF.trace-slot-reads-above result-g

      f-reads-below : SMP.TraceSlotReadsBelow reclaim-f f-trace
      f-reads-below = IRResultAWF.trace-slot-reads-below result-f

      g-reads-below : SMP.TraceSlotReadsBelow reclaim-g g-trace
      g-reads-below = IRResultAWF.trace-slot-reads-below result-g

      ----------------------------------------------------------------------
      -- Trace characterization using SMPrimitives
      ----------------------------------------------------------------------
      pair-trace-no-store-indirect : SMP.TraceNoStoreIndirect pair-trace
      pair-trace-no-store-indirect =
        tt , tt , SMP.trace-no-store-indirect-append f-trace _
          f-tnsi (tt , tt , SMP.trace-no-store-indirect-append g-trace _ g-tnsi (tt , tt , tt))

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

      -- Helper bounds for trace predicates
      backup≤fst : backup-slot ≤ fst-slot
      backup≤fst = ≤-trans (n≤1+n backup-slot)
                     (≤-trans reclaim-f-above-backup (IRResultAWF.reclaim-monotone result-g))

      backup≤snd : backup-slot ≤ snd-slot
      backup≤snd = ≤-trans backup≤fst (n≤1+n fst-slot)

      backup≤reclaim-f : backup-slot ≤ reclaim-f
      backup≤reclaim-f = ≤-trans (n≤1+n backup-slot) reclaim-f-above-backup

      fst<bound : fst-slot < reclaim-g +ℕ ps
      fst<bound = m<m+n reclaim-g {ps} ps≥1

      snd<bound : snd-slot < reclaim-g +ℕ ps
      snd<bound = suc<+2 reclaim-g  -- suc reclaim-g < reclaim-g + 2

      backup<bound : backup-slot < reclaim-g +ℕ ps
      backup<bound = ≤-trans (s≤s backup≤fst) fst<bound

      -- Final trace segment (after g-trace)
      final-seg : AbstractTrace
      final-seg = store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []

      final-seg-writes-above : SMP.TraceWritesAbove backup-slot final-seg
      final-seg-writes-above = backup≤snd , tt

      final-seg-writes-below : SMP.TraceWritesBelow (reclaim-g +ℕ ps) final-seg
      final-seg-writes-below = snd<bound , tt

      -- Middle segment (store fst, restore, g-trace, final)
      middle-plus-g-plus-final : AbstractTrace
      middle-plus-g-plus-final = store-at-slot fst-slot ∷ restore-input backup-slot ∷
                                 g-trace ++ final-seg

      g-plus-final-writes-above : SMP.TraceWritesAbove backup-slot (g-trace ++ final-seg)
      g-plus-final-writes-above = SMP.trace-writes-above-append backup-slot g-trace final-seg
                                    (SMP.trace-writes-above-mono backup-slot reclaim-f g-trace
                                       backup≤reclaim-f g-writes-above)
                                    final-seg-writes-above

      g-plus-final-writes-below : SMP.TraceWritesBelow (reclaim-g +ℕ ps) (g-trace ++ final-seg)
      g-plus-final-writes-below = SMP.trace-writes-below-append (reclaim-g +ℕ ps) g-trace final-seg
                                    (SMP.trace-writes-below-mono reclaim-g (reclaim-g +ℕ ps) g-trace
                                       (m≤m+n reclaim-g ps) g-writes-below)
                                    final-seg-writes-below
        where
          open SMP using (trace-writes-below-mono)

      middle-plus-writes-above : SMP.TraceWritesAbove backup-slot middle-plus-g-plus-final
      middle-plus-writes-above = backup≤fst , g-plus-final-writes-above

      middle-plus-writes-below : SMP.TraceWritesBelow (reclaim-g +ℕ ps) middle-plus-g-plus-final
      middle-plus-writes-below = fst<bound , g-plus-final-writes-below

      -- f-trace plus middle (store-at-slot fst-slot ∷ rest)
      f-plus-rest : AbstractTrace
      f-plus-rest = f-trace ++ middle-plus-g-plus-final

      f-plus-rest-writes-above : SMP.TraceWritesAbove backup-slot f-plus-rest
      f-plus-rest-writes-above = SMP.trace-writes-above-append backup-slot f-trace middle-plus-g-plus-final
                                   (SMP.trace-writes-above-mono backup-slot (suc backup-slot) f-trace
                                      (n≤1+n backup-slot) f-writes-above)
                                   middle-plus-writes-above

      f-plus-rest-writes-below : SMP.TraceWritesBelow (reclaim-g +ℕ ps) f-plus-rest
      f-plus-rest-writes-below = SMP.trace-writes-below-append (reclaim-g +ℕ ps) f-trace middle-plus-g-plus-final
                                   (SMP.trace-writes-below-mono reclaim-f (reclaim-g +ℕ ps) f-trace
                                      (≤-trans (IRResultAWF.reclaim-monotone result-g) (m≤m+n reclaim-g ps))
                                      f-writes-below)
                                   middle-plus-writes-below
        where
          open SMP using (trace-writes-below-mono)

      pair-trace-writes-above : SMP.TraceWritesAbove backup-slot pair-trace
      pair-trace-writes-above = ≤-refl , f-plus-rest-writes-above

      -- Build reads-above similarly to writes-above
      final-seg-reads-above : SMP.TraceSlotReadsAbove backup-slot final-seg
      final-seg-reads-above = tt  -- no reads in store-at-slot or lea-slot

      g-plus-final-reads-above : SMP.TraceSlotReadsAbove backup-slot (g-trace ++ final-seg)
      g-plus-final-reads-above = SMP.trace-slot-reads-above-append backup-slot g-trace final-seg
                                   (SMP.trace-slot-reads-above-mono backup-slot reclaim-f g-trace
                                      backup≤reclaim-f g-reads-above)
                                   final-seg-reads-above

      middle-plus-reads-above : SMP.TraceSlotReadsAbove backup-slot middle-plus-g-plus-final
      middle-plus-reads-above = ≤-refl , g-plus-final-reads-above
        -- store-at-slot has no read, restore-input backup-slot reads backup-slot ≥ backup-slot

      f-plus-rest-reads-above : SMP.TraceSlotReadsAbove backup-slot f-plus-rest
      f-plus-rest-reads-above = SMP.trace-slot-reads-above-append backup-slot f-trace middle-plus-g-plus-final
                                  (SMP.trace-slot-reads-above-mono backup-slot (suc backup-slot) f-trace
                                     (n≤1+n backup-slot) f-reads-above)
                                  middle-plus-reads-above

      pair-trace-slot-reads-above : SMP.TraceSlotReadsAbove backup-slot pair-trace
      pair-trace-slot-reads-above = f-plus-rest-reads-above
        -- mov-to-output and store-at-slot have no reads

      pair-trace-writes-below : SMP.TraceWritesBelow (reclaim-g +ℕ ps) pair-trace
      pair-trace-writes-below = backup<bound , f-plus-rest-writes-below

      -- Build reads-below similarly
      final-seg-reads-below : SMP.TraceSlotReadsBelow (reclaim-g +ℕ ps) final-seg
      final-seg-reads-below = tt

      g-plus-final-reads-below : SMP.TraceSlotReadsBelow (reclaim-g +ℕ ps) (g-trace ++ final-seg)
      g-plus-final-reads-below = SMP.trace-slot-reads-below-append (reclaim-g +ℕ ps) g-trace final-seg
                                   (SMP.trace-slot-reads-below-mono reclaim-g (reclaim-g +ℕ ps) g-trace
                                      (m≤m+n reclaim-g ps) g-reads-below)
                                   final-seg-reads-below

      middle-plus-reads-below : SMP.TraceSlotReadsBelow (reclaim-g +ℕ ps) middle-plus-g-plus-final
      middle-plus-reads-below = backup<bound , g-plus-final-reads-below
        -- restore-input backup-slot reads backup-slot < reclaim-g + ps

      f-plus-rest-reads-below : SMP.TraceSlotReadsBelow (reclaim-g +ℕ ps) f-plus-rest
      f-plus-rest-reads-below = SMP.trace-slot-reads-below-append (reclaim-g +ℕ ps) f-trace middle-plus-g-plus-final
                                  (SMP.trace-slot-reads-below-mono reclaim-f (reclaim-g +ℕ ps) f-trace
                                     (≤-trans (IRResultAWF.reclaim-monotone result-g) (m≤m+n reclaim-g ps))
                                     f-reads-below)
                                  middle-plus-reads-below

      pair-trace-slot-reads-below : SMP.TraceSlotReadsBelow (reclaim-g +ℕ ps) pair-trace
      pair-trace-slot-reads-below = f-plus-rest-reads-below

      ----------------------------------------------------------------------
      -- KEY PROOFS using SMPrimitives memory axioms
      ----------------------------------------------------------------------

      -- POSTULATE: These require trace decomposition (same structure as PairWF)
      -- The last instruction is lea-slot fst-slot which sets Output := OnStack frame fst-slot = pair-loc
      postulate
        rax-eq : readReg (regs s-final) Output ≡ pair-loc
        -- Proof: trace decomposition to final lea-slot, then writeReg-same

        not-halted-final : halted s-final ≡ false
        -- Proof: propagate not-halted through each instruction

      slot-monotone-pair : next-slot alloc ≤ next-slot alloc₃
      slot-monotone-pair = ≤-trans (n≤1+n backup-slot)
                             (≤-trans reclaim-f-above-backup
                               (≤-trans (IRResultAWF.reclaim-monotone result-g)
                                 (m≤m+n reclaim-g ps)))

      pair-before : BeforeFrontier alloc₃ pair-loc
      pair-before = stack-before refl (m<m+n reclaim-g {ps} ps≥1)

      pair-reclaim : ℕ
      pair-reclaim = reclaim-g +ℕ ps

      pair-reclaim-monotone : next-slot alloc ≤ pair-reclaim
      pair-reclaim-monotone = ≤-trans (n≤1+n backup-slot)
                                (≤-trans reclaim-f-above-backup
                                  (≤-trans (IRResultAWF.reclaim-monotone result-g)
                                    (m≤m+n reclaim-g ps)))

      -- Arithmetic bound: reclaim-g + ps ≤ backup-slot + req-pair
      -- where req-pair = ir-stack-requirement (⟨ f , g ⟩ m) = 1 + rf + rg + ps
      -- Proof: reclaim-g ≤ reclaim-f + rg ≤ (suc backup + rf) + rg
      --        reclaim-g + ps ≤ (suc backup + rf + rg) + ps
      --        and (suc backup + rf + rg) + ps = backup + (1 + rf + rg + ps)
      reclaim-g≤-rf-rg : reclaim-g ≤ (suc backup-slot +ℕ rf) +ℕ rg
      reclaim-g≤-rf-rg = ≤-trans reclaim-g-bound (+-monoˡ-≤ rg reclaim-f-bound)

      pair-reclaim-step1 : reclaim-g +ℕ ps ≤ ((suc backup-slot +ℕ rf) +ℕ rg) +ℕ ps
      pair-reclaim-step1 = +-monoˡ-≤ ps reclaim-g≤-rf-rg

      -- Prove: ((suc b + rf) + rg) + ps = b + req-pair  where b = backup-slot
      -- LHS = suc b + rf + rg + ps = suc (b + rf + rg + ps)
      -- RHS = b + (1 + rf + rg + ps) = b + suc (rf + rg + ps)
      --     = suc (b + rf + rg + ps)  (by +-suc)
      -- So LHS = RHS
      open import Data.Nat.Properties using (+-suc)
      pair-reclaim-eq : ((suc backup-slot +ℕ rf) +ℕ rg) +ℕ ps ≡ backup-slot +ℕ req-pair
      pair-reclaim-eq =
        -- ((suc b + rf) + rg) + ps
        trans (+-assoc (suc backup-slot +ℕ rf) rg ps)     -- = (suc b + rf) + (rg + ps)
        (trans (+-assoc (suc backup-slot) rf (rg +ℕ ps))  -- = suc b + (rf + (rg + ps))
        (trans (cong (suc backup-slot +ℕ_) (sym (+-assoc rf rg ps)))  -- = suc b + (rf + rg + ps)
        -- Now suc b + n = suc (b + n) definitionally, so:
        -- = suc (b + (rf + rg + ps))
        -- And we need: b + (1 + rf + rg + ps) = b + suc (rf + rg + ps)
        --            = suc (b + (rf + rg + ps))  by +-suc
        (sym (+-suc backup-slot (rf +ℕ rg +ℕ ps)))))

      pair-reclaim-size-bound : pair-reclaim ≤ backup-slot +ℕ req-pair
      pair-reclaim-size-bound = subst (reclaim-g +ℕ ps ≤_) pair-reclaim-eq pair-reclaim-step1

      -- POSTULATE: Backup slot preservation (same structure as PairWF)
      postulate
        pair-frontier-stable : ∀ (s' : LocState FS) (input-loc' : ValueLocation FS) →
          halted s' ≡ false →
          readReg (regs s') Input ≡ input-loc' →
          readLoc s' (OnStack frame backup-slot) ≡ just input-loc' →
          readLoc (proj₁ (exec-trace pair-trace s' alloc))
                  (OnStack frame backup-slot) ≡ just input-loc'
        -- Proof: trace decomposition showing backup-slot is preserved
        -- store-at-slot backup-slot writes backup, but then no other write affects it
        -- since f-trace and g-trace write to slots > backup-slot

      ----------------------------------------------------------------------
      -- KEY: mem-preserved-pair using SMPrimitives
      --
      -- This is the core memory reasoning using positive characterization:
      --   1. pair-trace writes to slots ≥ backup-slot (TraceWritesAbove)
      --   2. BeforeFrontier means loc is at slot < backup-slot
      --   3. Therefore loc NOT in write set
      --   4. By exec-trace-read-write-other: loc is preserved
      ----------------------------------------------------------------------
      -- KEY PROOF using SMPrimitives positive write characterization
      -- This demonstrates the SMPrimitives approach:
      --   1. We have pair-trace-writes-above : TraceWritesAbove backup-slot pair-trace
      --   2. BeforeFrontier alloc loc means loc is at slot < backup-slot (for stack-before)
      --   3. Apply exec-trace-preserves-disjoint to get preservation
      --
      -- All cases (stack-before, stack-ancestor, heap-before) handled by disjoint condition.
      mem-preserved-pair : ∀ loc → BeforeFrontier alloc loc → readLoc s-final loc ≡ readLoc s loc
      mem-preserved-pair loc bf = exec-trace-preserves-disjoint pair-trace s alloc loc backup-slot
                                    pair-trace-writes-above pair-trace-no-store-indirect disjoint-proof
        where
          -- Locations before frontier are disjoint from all slots ≥ backup-slot
          disjoint-proof : ∀ slot → backup-slot ≤ slot → OnStack frame slot ≢ loc
          disjoint-proof slot backup≤slot eq = bf-disjoint bf slot backup≤slot (sym eq)
            where
              -- BeforeFrontier implies the location is not at slots ≥ next-slot
              bf-disjoint : BeforeFrontier alloc loc → ∀ slot' → backup-slot ≤ slot' →
                            loc ≢ OnStack frame slot'
              bf-disjoint (stack-before {f'} {k} frame-eq k<next) slot' backup≤slot' eq' =
                -- k < next-slot alloc = backup-slot ≤ slot'
                -- But eq' says OnStack f' k ≡ OnStack frame slot', so k ≡ slot'
                -- Contradiction: k < backup-slot ≤ slot' = k
                let k<slot' : k < slot'
                    k<slot' = <-≤-trans k<next backup≤slot'
                    k≡slot' = stack-slot-injective eq'
                in <⇒≢ k<slot' k≡slot'
              bf-disjoint (stack-ancestor {f'} cf≺f _) slot' backup≤slot' eq' =
                -- f' is an ancestor frame (cf ≺ f'), but eq' says OnStack f' k ≡ OnStack frame slot'
                -- This implies f' ≡ frame, contradicting cf ≺ frame (irreflexivity)
                let f'≡frame = stack-frame-injective eq'
                in ≺⇒≢ cf≺f (sym f'≡frame)
              bf-disjoint (heap-before _) slot' backup≤slot' ()
                -- OnHeap ≢ OnStack is immediate (different constructors)

      ----------------------------------------------------------------------
      -- KEY: fst-ptr using SMPrimitives memory axioms
      --
      -- Proof structure:
      -- 1. store-at-slot fst-slot writes fst-loc (readLoc-writeLoc-same)
      -- 2. g-trace writes ≥ reclaim-f > fst (exec-trace-read-write-other)
      -- 3. store-at-slot snd-slot: snd ≠ fst (readLoc-writeLoc-other)
      -- 4. lea-slot: no memory write
      ----------------------------------------------------------------------
      -- POSTULATE: Pointer values in final state
      -- These use trace decomposition + SMPrimitives memory axioms
      postulate
        fst-ptr : readLoc s-final fst-loc-stack ≡ just fst-loc
        -- Proof using SMPrimitives:
        -- 1. store-at-slot fst-slot writes fst-loc (readLoc-writeLoc-same)
        -- 2. g-trace writes ≥ reclaim-f, fst-slot = reclaim-g < reclaim-f is FALSE
        --    Actually fst-slot = reclaim-g ≥ reclaim-f, so use:
        --    g-trace writes to [reclaim-f, reclaim-g), so reclaim-g is NOT written
        -- 3. store-at-slot snd-slot: snd ≠ fst (readLoc-writeLoc-other)
        -- 4. lea-slot: no memory write

        snd-ptr : readLoc s-final snd-loc-stack ≡ just snd-loc
        -- Proof: store-at-slot snd-slot writes snd-loc, then lea-slot doesn't modify

      ----------------------------------------------------------------------
      -- Validity proofs
      ----------------------------------------------------------------------
      -- POSTULATE: Validity preservation
      -- These follow the same pattern as PairWF, using validityWF-mem-preserved
      postulate
        fst-valid : ValidAtWF mF alloc₃ (eval primSem f x) fst-loc s-final
        -- Proof: validityWF-frontier-advance from result-f validity
        --   + validityWF-mem-preserved using mem-preserved-pair

        snd-valid : ValidAtWF mG alloc₃ (eval primSem g x) snd-loc s-final
        -- Proof: validityWF-frontier-advance from result-g validity
        --   + validityWF-mem-preserved using SMPrimitives preservation

      fst-before : BeforeFrontier alloc₃ fst-loc
      fst-before = frontier-monotone alloc₁-reclaimed alloc₃
                     refl
                     (≤-trans (IRResultAWF.reclaim-monotone result-g) (m≤m+n reclaim-g ps))
                     ≤-refl
                     fst-loc
                     (IRResultAWF.reclaim-preserves-result result-f reclaim-f-fits)

      snd-before : BeforeFrontier alloc₃ snd-loc
      snd-before = frontier-monotone (record alloc { next-slot = reclaim-g }) alloc₃
                     refl
                     (m≤m+n reclaim-g ps)
                     ≤-refl
                     snd-loc
                     (IRResultAWF.reclaim-preserves-result result-g reclaim-g-fits)

      suc<+ps : suc reclaim-g < reclaim-g +ℕ ps
      suc<+ps = ≤-trans (suc<+2 reclaim-g) (+-monoʳ-≤ reclaim-g ps≥2)

      sucLoc-pair-before : BeforeFrontier alloc₃ (sucLoc pair-loc)
      sucLoc-pair-before = stack-before refl suc<+ps

      pair-valid-wf-final : ValidAtWF m alloc₃
                              (pair (eval primSem f x) (eval primSem g x)) pair-loc s-final
      pair-valid-wf-final = valid-pair-wf fst-ptr snd-ptr fst-before snd-before
                              sucLoc-pair-before fst-valid snd-valid
