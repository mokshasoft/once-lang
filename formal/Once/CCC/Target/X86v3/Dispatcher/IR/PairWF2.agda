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
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym; cong; subst; subst₂)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.SlotMachine hiding (AllocMode; Stack; Heap)
open import Once.CCC.Target.X86v3.Types
open import Once.CCC.IR
open import Once.CCC.Target.X86v3.Dispatcher.Allocation hiding (AllocMode)
open import Once.CCC.Target.X86v3.Dispatcher.ClosureWellFormed

-- Import SMPrimitives qualified for memory reasoning primitives
import Once.CCC.SMPrimitives as SMP

------------------------------------------------------------------------
-- Proof obligation marker (to be replaced with actual proofs)
------------------------------------------------------------------------

postulate
  !! : ∀ {ℓ} {A : Set ℓ} → A

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
           validityWF-frontier-advance;
           validityWF-mem-preserved-excluding;
           validityWF-trace-preserves)

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
      ; trace-preserves-halted = pair-trace-preserves-halted
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
      -- TRACE STRUCTURAL DECOMPOSITION
      -- Connect s-final to intermediate states step by step
      ----------------------------------------------------------------------

      -- Final state after executing all segments
      s-after-final : LocState FS
      s-after-final = proj₁ (exec-trace final-trace s-after-g alloc-after-g)

      alloc-after-final : AllocState {FS}
      alloc-after-final = proj₂ (exec-trace final-trace s-after-g alloc-after-g)

      -- Define the trace "rest" after setup (what pair-trace looks like after first 2 instrs)
      rest-after-setup : AbstractTrace
      rest-after-setup = f-trace ++
                         store-at-slot fst-slot ∷ restore-input backup-slot ∷
                         g-trace ++
                         store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []

      -- pair-trace ≡ setup-trace ++ rest-after-setup (by definition, essentially refl)
      pair-trace-as-setup : pair-trace ≡ setup-trace ++ rest-after-setup
      pair-trace-as-setup = refl

      -- Define rest traces for decomposition
      rest-after-f : AbstractTrace
      rest-after-f = store-at-slot fst-slot ∷ restore-input backup-slot ∷
                     g-trace ++
                     store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []

      rest-after-middle : AbstractTrace
      rest-after-middle = g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []

      -- Show rest-after-setup = f-trace ++ rest-after-f
      rest-after-setup-eq : rest-after-setup ≡ f-trace ++ rest-after-f
      rest-after-setup-eq = refl

      -- Show rest-after-f = middle-trace ++ rest-after-middle
      rest-after-f-eq : rest-after-f ≡ middle-trace ++ rest-after-middle
      rest-after-f-eq = refl

      -- Show rest-after-middle = g-trace ++ final-trace
      rest-after-middle-eq : rest-after-middle ≡ g-trace ++ final-trace
      rest-after-middle-eq = refl

      -- KEY LEMMA: s-final ≡ s-after-final
      -- We use exec-trace-append to decompose step by step
      s-final-eq : s-final ≡ s-after-final
      s-final-eq =
        -- Step 1: pair-trace = setup-trace ++ rest-after-setup
        let step1 : exec-trace pair-trace s alloc ≡
                    exec-trace rest-after-setup s-after-setup alloc-after-setup
            step1 = exec-trace-append setup-trace rest-after-setup s alloc

            -- Step 2: rest-after-setup = f-trace ++ rest-after-f
            step2 : exec-trace rest-after-setup s-after-setup alloc-after-setup ≡
                    exec-trace rest-after-f s-after-f alloc-after-f
            step2 = exec-trace-append f-trace rest-after-f s-after-setup alloc-after-setup

            -- Step 3: rest-after-f = middle-trace ++ rest-after-middle
            step3 : exec-trace rest-after-f s-after-f alloc-after-f ≡
                    exec-trace rest-after-middle s-after-middle alloc-after-middle
            step3 = exec-trace-append middle-trace rest-after-middle s-after-f alloc-after-f

            -- Step 4: rest-after-middle = g-trace ++ final-trace
            step4 : exec-trace rest-after-middle s-after-middle alloc-after-middle ≡
                    exec-trace final-trace s-after-g alloc-after-g
            step4 = exec-trace-append g-trace final-trace s-after-middle alloc-after-middle
        in cong proj₁ (trans step1 (trans step2 (trans step3 step4)))

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

      -- TPH proofs from sub-IR results
      f-tph : TracePreservesHaltedP f-trace
      f-tph = IRResultAWF.trace-preserves-halted result-f

      g-tph : TracePreservesHaltedP g-trace
      g-tph = IRResultAWF.trace-preserves-halted result-g

      -- Trace preserves halted through pair-trace
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

      -- Halted preservation chain through intermediate states
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
      -- KEY PROOFS using SMPrimitives memory axioms + trace decomposition
      ----------------------------------------------------------------------

      -- TPH proof for final-trace
      final-tph : TracePreservesHaltedP final-trace
      final-tph = tph-∷ iph-store-at-slot (tph-∷ iph-lea-slot tph-[])

      -- Frame preserved through to alloc-after-g
      frame-preserved-to-g : current-frame alloc-after-g ≡ frame
      frame-preserved-to-g =
        trans (exec-trace-preserves-frame g-trace s-after-middle alloc-after-middle)
        (trans (exec-trace-preserves-frame middle-trace s-after-f alloc-after-f)
        (trans (exec-trace-preserves-frame f-trace s-after-setup alloc-after-setup)
               (exec-trace-preserves-frame setup-trace s alloc)))

      -- Trace for first instruction of final-trace
      first-final-instr : AbstractTrace
      first-final-instr = store-at-slot snd-slot ∷ []

      -- After store-at-slot snd-slot (using exec-trace for compatibility with exec-trace-append)
      s-after-snd-store' : LocState FS
      s-after-snd-store' = proj₁ (exec-trace first-final-instr s-after-g alloc-after-g)

      alloc-after-snd-store' : AllocState {FS}
      alloc-after-snd-store' = proj₂ (exec-trace first-final-instr s-after-g alloc-after-g)

      -- Connect exec-trace [i] to exec-abstract i when not halted
      first-final-as-abstract : exec-trace first-final-instr s-after-g alloc-after-g ≡
                                exec-abstract (store-at-slot snd-slot) s-after-g alloc-after-g
      first-final-as-abstract = exec-trace-single (store-at-slot snd-slot) s-after-g alloc-after-g not-halted-after-g

      not-halted-after-snd-store : halted s-after-snd-store' ≡ false
      not-halted-after-snd-store =
        trans (cong halted (cong proj₁ first-final-as-abstract))
              (trans (store-at-slot-halted snd-slot s-after-g alloc-after-g) not-halted-after-g)

      -- s-after-final via final-trace = [store-at-slot snd-slot, lea-slot fst-slot]
      -- Decomposition: final-trace = first-final-instr ++ (lea-slot fst-slot ∷ [])
      final-trace-split : final-trace ≡ first-final-instr ++ (lea-slot fst-slot ∷ [])
      final-trace-split = refl

      -- exec-trace decomposes via exec-trace-append
      final-trace-exec-step1 : exec-trace final-trace s-after-g alloc-after-g ≡
                               exec-trace (lea-slot fst-slot ∷ []) s-after-snd-store' alloc-after-snd-store'
      final-trace-exec-step1 = exec-trace-append first-final-instr (lea-slot fst-slot ∷ []) s-after-g alloc-after-g

      -- Second step: single instruction lea-slot
      final-trace-exec-step2 : exec-trace (lea-slot fst-slot ∷ []) s-after-snd-store' alloc-after-snd-store' ≡
                               exec-abstract (lea-slot fst-slot) s-after-snd-store' alloc-after-snd-store'
      final-trace-exec-step2 = exec-trace-single (lea-slot fst-slot) s-after-snd-store' alloc-after-snd-store' not-halted-after-snd-store

      -- Combined: s-after-final = proj₁ (exec-abstract (lea-slot fst-slot) ...)
      final-trace-exec : s-after-final ≡ proj₁ (exec-abstract (lea-slot fst-slot) s-after-snd-store' alloc-after-snd-store')
      final-trace-exec = cong proj₁ (trans final-trace-exec-step1 final-trace-exec-step2)

      -- Frame preserved through alloc-after-snd-store'
      frame-after-snd-store : current-frame alloc-after-snd-store' ≡ frame
      frame-after-snd-store =
        trans (exec-trace-preserves-frame first-final-instr s-after-g alloc-after-g)
              frame-preserved-to-g

      -- rax-eq: The last instruction is lea-slot fst-slot which sets Output := OnStack frame fst-slot
      rax-eq : readReg (regs s-final) Output ≡ pair-loc
      rax-eq =
        let -- s-final ≡ s-after-final
            eq1 : readReg (regs s-final) Output ≡ readReg (regs s-after-final) Output
            eq1 = cong (λ s' → readReg (regs s') Output) s-final-eq

            -- s-after-final ≡ exec lea-slot ...
            eq2 : s-after-final ≡ proj₁ (exec-abstract (lea-slot fst-slot) s-after-snd-store' alloc-after-snd-store')
            eq2 = final-trace-exec

            -- lea-slot result
            eq3 : readReg (regs (proj₁ (exec-abstract (lea-slot fst-slot) s-after-snd-store' alloc-after-snd-store'))) Output ≡
                  OnStack (current-frame alloc-after-snd-store') fst-slot
            eq3 = lea-slot-result fst-slot s-after-snd-store' alloc-after-snd-store'

            -- Frame equality
            eq4 : OnStack (current-frame alloc-after-snd-store') fst-slot ≡ pair-loc
            eq4 = cong (λ f → OnStack f fst-slot) frame-after-snd-store
        in trans eq1 (trans (cong (λ s' → readReg (regs s') Output) eq2) (trans eq3 eq4))

      not-halted-final : halted s-final ≡ false
      not-halted-final =
        let -- s-final ≡ s-after-final
            eq1 : halted s-final ≡ halted s-after-final
            eq1 = cong halted s-final-eq

            -- final-trace preserves halted
            eq2 : halted s-after-final ≡ false
            eq2 = exec-trace-preserves-halted final-trace s-after-g alloc-after-g not-halted-after-g final-tph
        in trans eq1 eq2

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

      -- Backup slot preservation using store-then-preserve pattern
      -- Structure:
      -- 1. mov-to-output sets Output = Input = input-loc'
      -- 2. store-at-slot backup-slot writes Output to backup-slot
      -- 3. Rest of trace writes above suc backup-slot, so backup-slot is preserved
      pair-frontier-stable : ∀ (s' : LocState FS) (input-loc' : ValueLocation FS) →
        halted s' ≡ false →
        readReg (regs s') Input ≡ input-loc' →
        readLoc s' (OnStack frame backup-slot) ≡ just input-loc' →
        readLoc (proj₁ (exec-trace pair-trace s' alloc))
                (OnStack frame backup-slot) ≡ just input-loc'
      pair-frontier-stable s' input-loc' not-halted' rdi-eq' _ =
        -- pair-trace = mov-to-output ∷ store-at-slot backup-slot ∷ rest
        -- where rest writes above suc backup-slot
        let -- After mov-to-output
            s'-after-mov = proj₁ (exec-abstract mov-to-output s' alloc)
            alloc'-after-mov = proj₂ (exec-abstract mov-to-output s' alloc)

            -- mov-to-output sets Output = Input (from definition)
            -- exec-abstract mov-to-output s alloc = (record s { regs = writeReg (regs s) Output (readReg (regs s) Input) }, alloc)
            mov-output : readReg (regs s'-after-mov) Output ≡ input-loc'
            mov-output = trans (writeReg-same (regs s') Output (readReg (regs s') Input)) rdi-eq'

            -- mov-to-output preserves halted (from exec-abstract-preserves-halted or directly)
            not-halted-after-mov : halted s'-after-mov ≡ false
            not-halted-after-mov = exec-abstract-preserves-halted mov-to-output s' alloc not-halted' iph-mov-to-output

            -- Rest trace after setup
            rest-trace : AbstractTrace
            rest-trace = f-trace ++
                         store-at-slot fst-slot ∷ restore-input backup-slot ∷
                         g-trace ++
                         store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []

            -- After-f part writes above suc backup-slot (using backup≤fst and g-writes-above)
            after-f-trace : AbstractTrace
            after-f-trace = store-at-slot fst-slot ∷ restore-input backup-slot ∷
                            g-trace ++
                            store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []

            after-g-trace : AbstractTrace
            after-g-trace = store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []

            -- suc backup-slot ≤ fst-slot (needed for store-at-slot fst-slot)
            -- reclaim-f-above-backup : suc backup-slot ≤ reclaim-f
            -- IRResultAWF.reclaim-monotone result-g : reclaim-f ≤ reclaim-g = fst-slot
            suc-backup≤fst : suc backup-slot ≤ fst-slot
            suc-backup≤fst = ≤-trans reclaim-f-above-backup (IRResultAWF.reclaim-monotone result-g)

            -- g-plus-after writes above suc backup-slot
            -- after-g-trace = store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []
            -- TraceWritesAbove (suc backup-slot) means: for store-at-slot snd-slot, suc backup-slot ≤ snd-slot
            -- snd-slot = suc fst-slot, so we need suc backup-slot ≤ suc fst-slot
            -- We have suc-backup≤fst : suc backup-slot ≤ fst-slot, so s≤s on that gives suc² backup-slot ≤ suc fst-slot
            -- Actually simpler: ≤-trans suc-backup≤fst (n≤1+n fst-slot) : suc backup-slot ≤ snd-slot
            suc-backup≤snd : suc backup-slot ≤ snd-slot
            suc-backup≤snd = ≤-trans suc-backup≤fst (n≤1+n fst-slot)

            after-g-writes-above : SMP.TraceWritesAbove (suc backup-slot) after-g-trace
            after-g-writes-above = suc-backup≤snd , tt

            g-plus-after-writes-above : SMP.TraceWritesAbove (suc backup-slot) (g-trace ++ after-g-trace)
            g-plus-after-writes-above = SMP.trace-writes-above-append (suc backup-slot) g-trace after-g-trace
                                          (SMP.trace-writes-above-mono (suc backup-slot) reclaim-f g-trace
                                            reclaim-f-above-backup g-writes-above)
                                          after-g-writes-above

            after-f-writes-above : SMP.TraceWritesAbove (suc backup-slot) after-f-trace
            after-f-writes-above = suc-backup≤fst , g-plus-after-writes-above

            -- rest-trace writes above suc backup-slot
            rest-writes-above : SMP.TraceWritesAbove (suc backup-slot) rest-trace
            rest-writes-above = SMP.trace-writes-above-append (suc backup-slot) f-trace after-f-trace
                                  f-writes-above after-f-writes-above

            -- rest-trace tnsi
            after-g-tnsi : SMP.TraceNoStoreIndirect after-g-trace
            after-g-tnsi = tt , tt , tt

            g-plus-after-tnsi : SMP.TraceNoStoreIndirect (g-trace ++ after-g-trace)
            g-plus-after-tnsi = SMP.trace-no-store-indirect-append g-trace after-g-trace g-tnsi after-g-tnsi

            after-f-tnsi : SMP.TraceNoStoreIndirect after-f-trace
            after-f-tnsi = tt , tt , g-plus-after-tnsi

            rest-tnsi : SMP.TraceNoStoreIndirect rest-trace
            rest-tnsi = SMP.trace-no-store-indirect-append f-trace after-f-trace f-tnsi after-f-tnsi

            -- Apply store-then-preserve: store-at-slot backup-slot ∷ rest preserves backup-slot
            -- We need to show s'-after-mov has Output = input-loc', which we have from mov-output
            store-pres : readLoc (proj₁ (exec-trace (store-at-slot backup-slot ∷ rest-trace) s'-after-mov alloc'-after-mov))
                                 (OnStack (current-frame alloc'-after-mov) backup-slot) ≡ just input-loc'
            store-pres = trans (store-then-preserve backup-slot rest-trace s'-after-mov alloc'-after-mov
                                  not-halted-after-mov rest-writes-above rest-tnsi)
                               (cong just mov-output)

            -- Frame preservation
            frame-eq-mov : current-frame alloc'-after-mov ≡ frame
            frame-eq-mov = exec-abstract-preserves-frame mov-to-output s' alloc

            -- Connect exec-abstract to exec-trace for mov-to-output
            exec-trace-mov : exec-trace (mov-to-output ∷ []) s' alloc ≡
                             exec-abstract mov-to-output s' alloc
            exec-trace-mov = exec-trace-single mov-to-output s' alloc not-halted'

            -- Connect s'-after-mov and alloc'-after-mov to exec-trace result
            s'-after-mov-eq : s'-after-mov ≡ proj₁ (exec-trace (mov-to-output ∷ []) s' alloc)
            s'-after-mov-eq = sym (cong proj₁ exec-trace-mov)

            alloc'-after-mov-eq : alloc'-after-mov ≡ proj₂ (exec-trace (mov-to-output ∷ []) s' alloc)
            alloc'-after-mov-eq = sym (cong proj₂ exec-trace-mov)

            -- Connect to pair-trace execution using exec-trace decomposition
            -- exec-trace (t1 ++ t2) s alloc = exec-trace t2 (proj₁ (exec-trace t1 ...)) (proj₂ (exec-trace t1 ...))
            exec-decomp : exec-trace pair-trace s' alloc ≡
                          exec-trace (store-at-slot backup-slot ∷ rest-trace)
                                     (proj₁ (exec-trace (mov-to-output ∷ []) s' alloc))
                                     (proj₂ (exec-trace (mov-to-output ∷ []) s' alloc))
            exec-decomp = exec-trace-append (mov-to-output ∷ []) (store-at-slot backup-slot ∷ rest-trace) s' alloc

            -- Rewrite store-pres with the exec-trace versions
            store-pres' : readLoc (proj₁ (exec-trace (store-at-slot backup-slot ∷ rest-trace)
                                           (proj₁ (exec-trace (mov-to-output ∷ []) s' alloc))
                                           (proj₂ (exec-trace (mov-to-output ∷ []) s' alloc))))
                                  (OnStack (current-frame (proj₂ (exec-trace (mov-to-output ∷ []) s' alloc))) backup-slot)
                          ≡ just input-loc'
            store-pres' = subst₂ (λ s'' a'' → readLoc (proj₁ (exec-trace (store-at-slot backup-slot ∷ rest-trace) s'' a''))
                                                       (OnStack (current-frame a'') backup-slot) ≡ just input-loc')
                                 s'-after-mov-eq alloc'-after-mov-eq store-pres

            -- Frame preserved through exec-trace
            frame-eq-mov' : current-frame (proj₂ (exec-trace (mov-to-output ∷ []) s' alloc)) ≡ frame
            frame-eq-mov' = exec-trace-preserves-frame (mov-to-output ∷ []) s' alloc

            -- The goal is: readLoc (proj₁ (exec-trace pair-trace s' alloc)) (OnStack frame backup-slot) ≡ just input-loc'
            -- We have store-pres' with OnStack (current-frame (...)) backup-slot
            -- frame-eq-mov' : current-frame (...) ≡ frame, so subst with frame-eq-mov' goes from (cf ...) to frame

            -- First, use exec-decomp to convert pair-trace execution
            step1 : readLoc (proj₁ (exec-trace (store-at-slot backup-slot ∷ rest-trace)
                                      (proj₁ (exec-trace (mov-to-output ∷ []) s' alloc))
                                      (proj₂ (exec-trace (mov-to-output ∷ []) s' alloc))))
                            (OnStack (current-frame (proj₂ (exec-trace (mov-to-output ∷ []) s' alloc))) backup-slot)
                    ≡ just input-loc'
            step1 = store-pres'

            -- Use frame-eq-mov' to convert current-frame to frame
            step2 : readLoc (proj₁ (exec-trace (store-at-slot backup-slot ∷ rest-trace)
                                      (proj₁ (exec-trace (mov-to-output ∷ []) s' alloc))
                                      (proj₂ (exec-trace (mov-to-output ∷ []) s' alloc))))
                            (OnStack frame backup-slot)
                    ≡ just input-loc'
            step2 = subst (λ f' → readLoc (proj₁ (exec-trace (store-at-slot backup-slot ∷ rest-trace)
                                                    (proj₁ (exec-trace (mov-to-output ∷ []) s' alloc))
                                                    (proj₂ (exec-trace (mov-to-output ∷ []) s' alloc))))
                                          (OnStack f' backup-slot) ≡ just input-loc')
                          frame-eq-mov' step1

            -- Use exec-decomp to convert back to pair-trace
            step3 : readLoc (proj₁ (exec-trace pair-trace s' alloc)) (OnStack frame backup-slot) ≡ just input-loc'
            step3 = subst (λ r → readLoc (proj₁ r) (OnStack frame backup-slot) ≡ just input-loc')
                          (sym exec-decomp) step2

        in step3

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
      -- KEY: fst-ptr and snd-ptr using SMPrimitives memory axioms
      ----------------------------------------------------------------------

      -- Trace segment after store fst-slot: rest of trace that must preserve fst-slot
      after-fst-store : AbstractTrace
      after-fst-store = restore-input backup-slot ∷ g-trace ++ final-seg

      -- TraceWritesBelow fst-slot for g-trace (writes in [reclaim-f, reclaim-g))
      -- fst-slot = reclaim-g, so g-trace writes at slots < fst-slot
      -- Note: g-writes-below : TraceWritesBelow reclaim-g g-trace

      -- final-seg = store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []
      -- store-at-slot snd-slot writes at suc fst-slot ≠ fst-slot
      -- lea-slot doesn't write

      -- snd-slot ≠ fst-slot
      snd≢fst : snd-slot ≢ fst-slot
      snd≢fst eq = <⇒≢ ≤-refl (sym eq)  -- suc fst-slot ≢ fst-slot

      fst≢snd : fst-slot ≢ snd-slot
      fst≢snd eq = snd≢fst (sym eq)

      -- TraceNoStoreIndirect for after-fst-store
      -- after-fst-store = restore-input backup-slot ∷ g-trace ++ final-seg
      after-fst-tnsi : SMP.TraceNoStoreIndirect after-fst-store
      after-fst-tnsi = tt , SMP.trace-no-store-indirect-append g-trace final-seg g-tnsi (tt , tt , tt)

      -- Intermediate states for snd-ptr proof
      -- Use exec-abstract directly (easier to reason about)
      s-after-snd-store : LocState FS
      s-after-snd-store = proj₁ (exec-abstract (store-at-slot snd-slot) s-after-g alloc-after-g)

      alloc-after-snd-store : AllocState {FS}
      alloc-after-snd-store = proj₂ (exec-abstract (store-at-slot snd-slot) s-after-g alloc-after-g)

      ----------------------------------------------------------------------
      -- snd-ptr: proved using SMPrimitives
      --
      -- Structure:
      -- 1. At s-after-g, Output = snd-loc (from g-trace result)
      -- 2. store-at-slot snd-slot writes Output to snd-slot
      -- 3. lea-slot fst-slot doesn't modify memory
      ----------------------------------------------------------------------

      -- Output = snd-loc at s-after-g
      -- This follows from connecting s-after-g (defined by trace execution)
      -- to result-g (from recursive dispatch)
      --
      -- The key insight: s-after-g and proj₁ (exec-trace g-trace s₁' alloc₁-reclaimed)
      -- produce the same Output because:
      -- 1. Both execute g-trace
      -- 2. Starting states agree on Input register and memory at slots ≥ reclaim-f
      -- 3. Frame is the same
      output-after-g-is-snd : readReg (regs s-after-g) Output ≡ snd-loc
      output-after-g-is-snd =
        -- The result-g was computed from s₁' with alloc₁-reclaimed
        -- s-after-g is from s-after-middle with alloc-after-middle
        -- These produce the same Output by trace determinism
        -- For now, use !! as this requires careful alignment of the trace executions
        -- The proof structure: show both states agree on inputs to g-trace
        !!

      -- lea-slot preserves snd-slot (no memory write)
      lea-preserves-snd : ∀ (s' : LocState FS) (alloc' : AllocState {FS}) →
        readLoc (proj₁ (exec-abstract (lea-slot fst-slot) s' alloc')) snd-loc-stack ≡
        readLoc s' snd-loc-stack
      lea-preserves-snd s' alloc' = lea-slot-preserves-mem fst-slot s' alloc' snd-loc-stack

      -- store-at-slot snd-slot result (if not halted)
      -- Note: frame is preserved through trace
      frame-at-g : current-frame alloc-after-g ≡ frame
      frame-at-g = trans (exec-trace-preserves-frame g-trace s-after-middle alloc-after-middle)
                    (trans (exec-trace-preserves-frame middle-trace s-after-f alloc-after-f)
                      (trans (exec-trace-preserves-frame f-trace s-after-setup alloc-after-setup)
                        (exec-trace-preserves-frame setup-trace s alloc)))

      snd-loc-stack-at-g : snd-loc-stack ≡ OnStack (current-frame alloc-after-g) snd-slot
      snd-loc-stack-at-g = cong (λ f → OnStack f snd-slot) (sym frame-at-g)

      snd-written : readLoc s-after-snd-store snd-loc-stack ≡ just snd-loc
      snd-written =
        subst (λ loc → readLoc s-after-snd-store loc ≡ just snd-loc) (sym snd-loc-stack-at-g)
          (trans (store-at-slot-result snd-slot s-after-g alloc-after-g)
                 (cong just output-after-g-is-snd))

      -- snd-ptr: use trace decomposition
      -- s-after-snd-store' ≡ s-after-snd-store (via first-final-as-abstract)
      snd-store-states-eq : s-after-snd-store' ≡ s-after-snd-store
      snd-store-states-eq = cong proj₁ first-final-as-abstract

      -- snd-written in terms of s-after-snd-store'
      snd-written' : readLoc s-after-snd-store' snd-loc-stack ≡ just snd-loc
      snd-written' = subst (λ s' → readLoc s' snd-loc-stack ≡ just snd-loc)
                           (sym snd-store-states-eq) snd-written

      -- lea-slot preserves the value at snd-slot
      -- s-after-final = exec lea-slot s-after-snd-store' ...
      snd-in-final : readLoc s-after-final snd-loc-stack ≡ just snd-loc
      snd-in-final =
        let eq1 : readLoc s-after-final snd-loc-stack ≡
                  readLoc (proj₁ (exec-abstract (lea-slot fst-slot) s-after-snd-store' alloc-after-snd-store')) snd-loc-stack
            eq1 = cong (λ s' → readLoc s' snd-loc-stack) final-trace-exec
            eq2 : readLoc (proj₁ (exec-abstract (lea-slot fst-slot) s-after-snd-store' alloc-after-snd-store')) snd-loc-stack ≡
                  readLoc s-after-snd-store' snd-loc-stack
            eq2 = lea-preserves-snd s-after-snd-store' alloc-after-snd-store'
        in trans eq1 (trans eq2 snd-written')

      -- Connect to s-final via s-final-eq
      snd-ptr : readLoc s-final snd-loc-stack ≡ just snd-loc
      snd-ptr = trans (cong (λ s' → readLoc s' snd-loc-stack) s-final-eq) snd-in-final

      ----------------------------------------------------------------------
      -- fst-ptr: proved using SMPrimitives
      --
      -- Structure:
      -- 1. At s-after-f, Output = fst-loc (from f-trace result)
      -- 2. store-at-slot fst-slot writes Output to fst-slot
      -- 3. restore-input backup-slot doesn't write to stack
      -- 4. g-trace writes below fst-slot (TraceWritesBelow reclaim-g)
      -- 5. store-at-slot snd-slot writes to snd-slot ≠ fst-slot
      -- 6. lea-slot doesn't modify memory
      ----------------------------------------------------------------------

      -- Output = fst-loc at s-after-f
      -- Using trace output determinism:
      -- f-trace executed from s (with alloc-after-backup) produces fst-loc in Output
      -- f-trace executed from s-after-setup (with alloc-after-setup) should produce same Output
      -- because they agree on Input register and memory at slots ≥ suc backup-slot

      -- First, get the result from executing f-trace from s
      s₁-output : readReg (regs (proj₁ (exec-trace f-trace s alloc-after-backup))) Output ≡ fst-loc
      s₁-output = subst (λ s' → readReg (regs s') Output ≡ fst-loc)
                        (sym (IRResultAWF.trace-correct result-f))
                        (IRResultAWF.rax-is-result result-f)

      -- Frame equality: current-frame alloc-after-backup ≡ current-frame alloc-after-setup
      frame-eq-backup-setup : current-frame alloc-after-backup ≡ current-frame alloc-after-setup
      frame-eq-backup-setup =
        trans refl  -- alloc-after-backup.frame = frame
              (sym (exec-trace-preserves-frame setup-trace s alloc))

      -- Input preserved through setup-trace
      -- mov-to-output writes to Output, not Input
      -- store-at-slot doesn't modify registers
      -- Proof: writeReg-preserves for mov, writeLoc-regs for store
      input-preserved-setup : readReg (regs s-after-setup) Input ≡ readReg (regs s) Input
      input-preserved-setup =
        let -- Intermediate state after mov-to-output
            s₁ = proj₁ (exec-abstract mov-to-output s alloc)
            alloc₁ = proj₂ (exec-abstract mov-to-output s alloc)

            -- Step 1: Decompose setup-trace using exec-trace-cons
            decomp : exec-trace setup-trace s alloc ≡
                     exec-trace (store-at-slot backup-slot ∷ []) s₁ alloc₁
            decomp = exec-trace-cons mov-to-output (store-at-slot backup-slot ∷ []) s alloc not-halted

            -- Step 2: halted s₁ ≡ false (mov-to-output preserves halted)
            halted-s₁ : halted s₁ ≡ false
            halted-s₁ = exec-abstract-preserves-halted mov-to-output s alloc not-halted iph-mov-to-output

            -- Step 3: exec-trace-single for the remaining trace
            single : exec-trace (store-at-slot backup-slot ∷ []) s₁ alloc₁ ≡
                     exec-abstract (store-at-slot backup-slot) s₁ alloc₁
            single = exec-trace-single (store-at-slot backup-slot) s₁ alloc₁ halted-s₁

            -- Step 4: s-after-setup equals proj₁ of exec-abstract (store-at-slot backup-slot) s₁ alloc₁
            s-after-setup-eq : s-after-setup ≡ proj₁ (exec-abstract (store-at-slot backup-slot) s₁ alloc₁)
            s-after-setup-eq = cong proj₁ (trans decomp single)

            -- Step 5: Input preserved through writeReg Output (mov-to-output)
            -- s₁ = record s { regs = writeReg (regs s) Output ... }, so regs s₁ = writeReg ...
            input-s₁ : readReg (regs s₁) Input ≡ readReg (regs s) Input
            input-s₁ = writeReg-preserves (regs s) Output Input (readReg (regs s) Input) (λ ())

            -- Step 6: store-at-slot preserves registers
            regs-after-store : regs (proj₁ (exec-abstract (store-at-slot backup-slot) s₁ alloc₁)) ≡ regs s₁
            regs-after-store = store-at-slot-regs backup-slot s₁ alloc₁

            -- Step 7: Combine: Input preserved through store
            input-after-store : readReg (regs (proj₁ (exec-abstract (store-at-slot backup-slot) s₁ alloc₁))) Input ≡
                                readReg (regs s) Input
            input-after-store = trans (cong (λ r → readReg r Input) regs-after-store) input-s₁

        in trans (cong (λ st → readReg (regs st) Input) s-after-setup-eq) input-after-store

      -- Memory at slots ≥ suc backup-slot preserved through setup-trace
      -- setup-trace = [mov-to-output, store-at-slot backup-slot]
      -- mov-to-output doesn't write memory, store-at-slot backup-slot writes only to backup-slot
      -- Proof: exec-abstract-preserves-mem for mov, store-at-slot-preserves-other for store
      mem-preserved-setup : ∀ slot → suc backup-slot ≤ slot →
        readLoc s (OnStack (current-frame alloc-after-backup) slot) ≡
        readLoc s-after-setup (OnStack (current-frame alloc-after-setup) slot)
      mem-preserved-setup slot suc-b≤slot =
        let -- Intermediate state after mov-to-output
            s₁ = proj₁ (exec-abstract mov-to-output s alloc)
            alloc₁ = proj₂ (exec-abstract mov-to-output s alloc)

            -- Step 1: Decompose setup-trace using exec-trace-cons
            decomp : exec-trace setup-trace s alloc ≡
                     exec-trace (store-at-slot backup-slot ∷ []) s₁ alloc₁
            decomp = exec-trace-cons mov-to-output (store-at-slot backup-slot ∷ []) s alloc not-halted

            -- Step 2: halted s₁ ≡ false
            halted-s₁ : halted s₁ ≡ false
            halted-s₁ = exec-abstract-preserves-halted mov-to-output s alloc not-halted iph-mov-to-output

            -- Step 3: exec-trace-single for the remaining trace
            single : exec-trace (store-at-slot backup-slot ∷ []) s₁ alloc₁ ≡
                     exec-abstract (store-at-slot backup-slot) s₁ alloc₁
            single = exec-trace-single (store-at-slot backup-slot) s₁ alloc₁ halted-s₁

            -- Step 4: s-after-setup = proj₁ (exec-abstract (store-at-slot backup-slot) s₁ alloc₁)
            s-after-setup-eq : s-after-setup ≡ proj₁ (exec-abstract (store-at-slot backup-slot) s₁ alloc₁)
            s-after-setup-eq = cong proj₁ (trans decomp single)

            -- Step 5: alloc₁ = alloc (mov-to-output doesn't change alloc)
            alloc₁-eq : alloc₁ ≡ alloc
            alloc₁-eq = refl

            -- Step 6: current-frame alloc = current-frame alloc-after-backup = frame
            frame-eq : current-frame alloc ≡ current-frame alloc-after-backup
            frame-eq = refl

            -- Step 7: mov-to-output preserves memory (writes only to registers)
            -- Use readLoc-stackMem-eq directly since mov-to-output only modifies regs
            mov-preserves : readLoc s₁ (OnStack (current-frame alloc) slot) ≡
                            readLoc s (OnStack (current-frame alloc) slot)
            mov-preserves = readLoc-stackMem-eq s₁ s (OnStack (current-frame alloc) slot) refl refl

            -- Step 8: backup-slot ≢ slot (since suc backup-slot ≤ slot ≡ backup-slot < slot)
            b≢slot : backup-slot ≢ slot
            b≢slot = <⇒≢ suc-b≤slot

            -- Step 9: store-at-slot backup-slot preserves slot (since backup-slot ≢ slot)
            -- Need to use alloc₁ which equals alloc
            store-preserves : readLoc (proj₁ (exec-abstract (store-at-slot backup-slot) s₁ alloc₁))
                                (OnStack (current-frame alloc₁) slot) ≡
                              readLoc s₁ (OnStack (current-frame alloc₁) slot)
            store-preserves = store-at-slot-preserves-other backup-slot slot s₁ alloc₁ b≢slot

            -- Step 10: Combine: readLoc s-after-setup loc = readLoc s loc
            -- Note: current-frame alloc-after-setup = current-frame alloc = frame
            frame-setup-eq : current-frame alloc-after-setup ≡ current-frame alloc
            frame-setup-eq = exec-trace-preserves-frame setup-trace s alloc

            loc-setup = OnStack (current-frame alloc-after-setup) slot
            loc-backup = OnStack (current-frame alloc-after-backup) slot
            loc-alloc = OnStack (current-frame alloc) slot

            -- Rewrite using frame equalities
            loc-eq-1 : loc-setup ≡ loc-alloc
            loc-eq-1 = cong (λ f → OnStack f slot) frame-setup-eq

            loc-eq-2 : loc-backup ≡ loc-alloc
            loc-eq-2 = cong (λ f → OnStack f slot) frame-eq

        in sym (trans (cong (λ loc → readLoc s-after-setup loc) loc-eq-1)
                (trans (cong (λ st → readLoc st loc-alloc) s-after-setup-eq)
                (trans store-preserves
                (trans mov-preserves
                       (cong (λ loc → readLoc s loc) (sym loc-eq-2))))))

      output-after-f-is-fst : readReg (regs s-after-f) Output ≡ fst-loc
      output-after-f-is-fst =
        let determ = exec-trace-output-deterministic f-trace s s-after-setup
                       alloc-after-backup alloc-after-setup (suc backup-slot)
                       not-halted not-halted-after-setup
                       frame-eq-backup-setup
                       (sym input-preserved-setup)
                       f-reads-above f-writes-above f-tnsi
                       mem-preserved-setup
        in trans (sym determ) s₁-output

      -- Note: not-halted-after-f is now proven above using exec-trace-preserves-halted

      -- Frame preservation through trace up to s-after-f
      frame-at-f : current-frame alloc-after-f ≡ frame
      frame-at-f = trans (exec-trace-preserves-frame f-trace s-after-setup alloc-after-setup)
                    (exec-trace-preserves-frame setup-trace s alloc)

      fst-loc-stack-at-f : fst-loc-stack ≡ OnStack (current-frame alloc-after-f) fst-slot
      fst-loc-stack-at-f = cong (λ f → OnStack f fst-slot) (sym frame-at-f)

      -- After store-at-slot fst-slot from s-after-f
      s-after-fst-store : LocState FS
      s-after-fst-store = proj₁ (exec-abstract (store-at-slot fst-slot) s-after-f alloc-after-f)

      fst-written : readLoc s-after-fst-store fst-loc-stack ≡ just fst-loc
      fst-written =
        subst (λ loc → readLoc s-after-fst-store loc ≡ just fst-loc) (sym fst-loc-stack-at-f)
          (trans (store-at-slot-result fst-slot s-after-f alloc-after-f)
                 (cong just output-after-f-is-fst))

      -- g-trace preserves fst-slot (writes below fst-slot = reclaim-g)
      -- Uses exec-trace-slot-value-below
      g-preserves-fst : ∀ (s' : LocState FS) (alloc' : AllocState {FS}) (v : ValueLocation FS) →
        current-frame alloc' ≡ frame →
        readLoc s' (OnStack frame fst-slot) ≡ just v →
        readLoc (proj₁ (exec-trace g-trace s' alloc')) (OnStack frame fst-slot) ≡ just v
      g-preserves-fst s' alloc' v frame-eq slot-has-v =
        let alloc'-after = proj₂ (exec-trace g-trace s' alloc')
            frame-after-eq : current-frame alloc'-after ≡ frame
            frame-after-eq = trans (exec-trace-preserves-frame g-trace s' alloc') frame-eq
            -- exec-trace-slot-value-below uses alloc''s frame
            inner : readLoc (proj₁ (exec-trace g-trace s' alloc')) (OnStack (current-frame alloc') fst-slot) ≡ just v
            inner = exec-trace-slot-value-below g-trace s' alloc' fst-slot v
                      (subst (λ f → readLoc s' (OnStack f fst-slot) ≡ just v) (sym frame-eq) slot-has-v)
                      g-writes-below g-tnsi
        in subst (λ f → readLoc (proj₁ (exec-trace g-trace s' alloc')) (OnStack f fst-slot) ≡ just v)
             frame-eq inner

      -- store-at-slot snd-slot preserves fst-slot (different slots)
      snd-store-preserves-fst : ∀ (s' : LocState FS) (alloc' : AllocState {FS}) →
        current-frame alloc' ≡ frame →
        readLoc (proj₁ (exec-abstract (store-at-slot snd-slot) s' alloc')) (OnStack frame fst-slot) ≡
        readLoc s' (OnStack frame fst-slot)
      snd-store-preserves-fst s' alloc' frame-eq =
        -- store-at-slot-preserves-other gives us the result with alloc' frame
        -- We substitute using frame-eq to get the result with 'frame'
        let inner : readLoc (proj₁ (exec-abstract (store-at-slot snd-slot) s' alloc'))
                           (OnStack (current-frame alloc') fst-slot) ≡
                    readLoc s' (OnStack (current-frame alloc') fst-slot)
            inner = store-at-slot-preserves-other snd-slot fst-slot s' alloc' snd≢fst
        in subst₂ (λ f₁ f₂ → readLoc (proj₁ (exec-abstract (store-at-slot snd-slot) s' alloc'))
                                    (OnStack f₁ fst-slot) ≡ readLoc s' (OnStack f₂ fst-slot))
             frame-eq frame-eq inner
        where
          open import Relation.Binary.PropositionalEquality using (subst₂)

      -- lea-slot preserves fst-slot (no memory write)
      lea-preserves-fst : ∀ (s' : LocState FS) (alloc' : AllocState {FS}) →
        readLoc (proj₁ (exec-abstract (lea-slot fst-slot) s' alloc')) fst-loc-stack ≡
        readLoc s' fst-loc-stack
      lea-preserves-fst s' alloc' = lea-slot-preserves-mem fst-slot s' alloc' fst-loc-stack

      -- fst-ptr proof using trace decomposition
      -- Step 1: fst-written shows s-after-fst-store has fst-loc (assuming output-after-f-is-fst)
      --
      -- middle-trace = store-at-slot fst-slot ∷ restore-input backup-slot ∷ []
      -- After middle-trace, fst-slot should still have fst-loc
      -- We need to show s-after-middle has fst-loc at fst-slot

      -- Frame preserved through middle-trace
      frame-after-middle : current-frame alloc-after-middle ≡ frame
      frame-after-middle = trans (exec-trace-preserves-frame middle-trace s-after-f alloc-after-f) frame-at-f

      -- rest of middle-trace writes above fst-slot (restore-input doesn't write to stack)
      rest-middle-writes-above : SMP.TraceWritesAbove (suc fst-slot) (restore-input backup-slot ∷ [])
      rest-middle-writes-above = tt  -- restore-input has no stack write

      rest-middle-tnsi : SMP.TraceNoStoreIndirect (restore-input backup-slot ∷ [])
      rest-middle-tnsi = tt , tt

      -- fst-slot has fst-loc in s-after-middle using store-then-preserve pattern
      -- middle-trace = store-at-slot fst-slot ∷ restore-input backup-slot ∷ []
      fst-in-middle : readLoc s-after-middle fst-loc-stack ≡ just fst-loc
      fst-in-middle =
        let -- Use store-then-preserve: after store-at-slot k ∷ rest, slot k = Output
            stp : readLoc s-after-middle (OnStack (current-frame alloc-after-f) fst-slot) ≡
                  just (readReg (regs s-after-f) Output)
            stp = store-then-preserve fst-slot (restore-input backup-slot ∷ []) s-after-f alloc-after-f
                    not-halted-after-f rest-middle-writes-above rest-middle-tnsi
            -- output-after-f-is-fst : readReg (regs s-after-f) Output ≡ fst-loc
            out-eq : just (readReg (regs s-after-f) Output) ≡ just fst-loc
            out-eq = cong just output-after-f-is-fst
            -- frame-at-f : current-frame alloc-after-f ≡ frame
            frame-eq : OnStack (current-frame alloc-after-f) fst-slot ≡ fst-loc-stack
            frame-eq = cong (λ f' → OnStack f' fst-slot) frame-at-f
        in subst (λ loc → readLoc s-after-middle loc ≡ just fst-loc)
                 frame-eq (trans stp out-eq)

      -- fst-slot has fst-loc in s-after-g (preserved through g-trace)
      -- g_preserves_fst works with OnStack frame fst-slot, need to connect to fst-loc-stack
      fst-in-g : readLoc s-after-g fst-loc-stack ≡ just fst-loc
      fst-in-g =
        -- fst-loc-stack = OnStack frame fst-slot
        -- g-preserves-fst gives us the result in terms of OnStack frame fst-slot
        let g-pres : readLoc s-after-g (OnStack frame fst-slot) ≡ just fst-loc
            g-pres = g-preserves-fst s-after-middle alloc-after-middle fst-loc
                       frame-after-middle fst-in-middle
        in g-pres  -- fst-loc-stack = OnStack frame fst-slot by definition

      -- fst-slot has fst-loc in s-after-snd-store' (preserved through store snd-slot)
      fst-in-snd-store : readLoc s-after-snd-store' fst-loc-stack ≡ just fst-loc
      fst-in-snd-store =
        -- Use snd-store-preserves-fst which is already defined
        let pres : readLoc s-after-snd-store' (OnStack frame fst-slot) ≡ readLoc s-after-g (OnStack frame fst-slot)
            pres = trans (cong (λ s' → readLoc s' (OnStack frame fst-slot)) snd-store-states-eq)
                         (snd-store-preserves-fst s-after-g alloc-after-g frame-at-g)
        in trans pres fst-in-g

      -- fst-slot has fst-loc in s-after-final (preserved through lea-slot)
      fst-in-final : readLoc s-after-final fst-loc-stack ≡ just fst-loc
      fst-in-final =
        let pres : readLoc s-after-final fst-loc-stack ≡ readLoc s-after-snd-store' fst-loc-stack
            pres = trans (cong (λ s' → readLoc s' fst-loc-stack) final-trace-exec)
                         (lea-preserves-fst s-after-snd-store' alloc-after-snd-store')
        in trans pres fst-in-snd-store

      -- fst-ptr: connect to s-final via s-final-eq
      fst-ptr : readLoc s-final fst-loc-stack ≡ just fst-loc
      fst-ptr = trans (cong (λ s' → readLoc s' fst-loc-stack) s-final-eq) fst-in-final

      ----------------------------------------------------------------------
      -- Validity proofs
      ----------------------------------------------------------------------

      -- fst validity: result-f gave us fst-loc with fst-value at s₁
      -- We need to show it's valid at s-final with alloc₃
      fst-valid : ValidAtWF mF alloc₃ (eval primSem f x) fst-loc s-final
      fst-valid =
        -- result-f.result-valid-wf gives validity at (s₁, alloc-after-f)
        -- where alloc-after-f has next-slot somewhere
        -- We need validity at (s-final, alloc₃) where alloc₃ has next-slot = reclaim-g + ps
        --
        -- Steps:
        -- 1. fst-loc is before frontier at alloc₃ (shown by fst-before)
        -- 2. Memory at fst-loc is preserved from s₁ to s-final (fst-loc < backup-slot? No!)
        --    Actually fst-loc = fst-loc-stack = OnStack frame fst-slot where fst-slot = reclaim-g
        --    This is written by our pair trace, not by result-f
        --
        -- Actually, the value at fst-loc in s-final is fst-loc (the pointer), not the fst value itself
        -- The fst VALUE is eval primSem f x, and it's stored at location fst-loc
        -- result-f says that after f executes, Output = fst-loc (the result location)
        -- and the value at fst-loc is valid
        --
        -- Wait, I need to trace through more carefully:
        -- - result-f has result-loc = fst-loc (which is IRResultAWF.result-loc result-f)
        -- - result-f has result-valid-wf : ValidAtWF mF alloc-after-f (eval primSem f x) fst-loc s₁
        --
        -- So at s₁, fst-loc contains (a representation of) eval primSem f x
        -- We need to show at s-final, fst-loc still contains that value
        --
        -- But fst-loc might change! fst-loc = IRResultAWF.result-loc result-f
        -- This depends on where f decided to put its result
        --
        -- Actually, mF determines whether result is on stack or heap
        -- If Stack: fst-loc is OnStack frame (some slot allocated by f)
        -- If Heap: fst-loc is OnHeap (some heap location)
        --
        -- For memory preservation:
        -- - f executes and puts result at fst-loc
        -- - g executes, possibly overwriting some slots but not fst-loc (if fst-loc is below g's allocation)
        -- - pair-trace stores fst-loc to fst-slot (this is storing the POINTER, not following it)
        --
        -- The key insight: fst-loc (from result-f) is at a slot < reclaim-f
        -- (because after f, we reclaim down to reclaim-f, and fst-loc is still valid after reclaim)
        -- Then g writes to slots ≥ reclaim-f
        -- So fst-loc's contents are preserved through g
        -- And the rest of pair-trace writes to fst-slot, snd-slot ≥ reclaim-g ≥ reclaim-f
        --
        -- So the preservation chain: s₁ → s₂ → s-final all preserve fst-loc

        -- Step 1: Get validity at s₁ with result-f's alloc
        let result-f-valid : ValidAtWF mF (IRResultAWF.final-alloc result-f) (eval primSem f x) fst-loc s₁
            result-f-valid = IRResultAWF.result-valid-wf result-f

            -- Step 2: fst-loc is before frontier at alloc₃
            -- This is proven as fst-before

            -- Step 3: fst-loc contents preserved from s₁ to s-final
            -- This requires showing fst-loc is outside the write regions of:
            -- - g-trace (writes ≥ reclaim-f, fst-loc from result-f should be < reclaim-f)
            -- - pair-trace setup after g

            -- The key: result-f.reclaim-preserves-result says fst-loc is valid even after reclaim
            -- This means fst-loc is "durable" - it's at a slot that won't be overwritten

            -- Actually, we need to show validity is preserved through the entire trace
            -- This is complex because validity involves not just the location but
            -- the entire structure at that location

        -- For now, use !! as this requires careful validity threading
        in !!

      snd-valid : ValidAtWF mG alloc₃ (eval primSem g x) snd-loc s-final
      snd-valid =
        -- Similar to fst-valid: snd-loc from result-g is valid at s₂
        -- Need to show validity preserved to s-final with alloc₃
        -- snd-loc is valid at s₂, and snd-loc is at slot < reclaim-g
        -- pair-trace writes to fst-slot = reclaim-g and snd-slot = suc reclaim-g
        -- These are ≥ reclaim-g, so don't interfere with snd-loc contents
        !!

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
