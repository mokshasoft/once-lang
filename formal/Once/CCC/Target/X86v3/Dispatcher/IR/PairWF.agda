------------------------------------------------------------------------
-- Once.CCC.Target.X86v3.IR.PairWF
--
-- PairWF proof using SMPrimitives for memory reasoning.
--
-- NOTE: Due to duplicate type definitions between SMCore and SlotMachine,
-- we import SMPrimitives qualified and use it for the memory primitives.
------------------------------------------------------------------------

module Once.CCC.Target.X86v3.Dispatcher.IR.PairWF where

open import Data.Nat using (ℕ; suc; _<_; _≤_; _≥_; s≤s; z≤n) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-antisym; m≤m+n; n≤1+n; +-comm; +-assoc; +-monoˡ-≤; +-monoʳ-≤; m<m+n; <-≤-trans; ≤-<-trans; <⇒≤; <⇒≢; ≮⇒≥; ≰⇒>; ≤∧≢⇒<; _<?_; _≤?_; m<1+n⇒m≤n)
open import Data.Empty using (⊥-elim)
open import Data.Bool using (false)
open import Data.Unit using (tt)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym; cong; cong₂; subst; subst₂)
open import Relation.Nullary using (yes; no)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.SMCore hiding (AllocMode; Stack; Heap)
open import Once.CCC.Target.X86v3.Types
open import Once.CCC.IR
open import Once.CCC.Target.X86v3.Dispatcher.Allocation hiding (AllocMode)
open import Once.CCC.Target.X86v3.Dispatcher.ClosureWellFormed

-- Import SMPrimitives qualified for memory reasoning primitives
import Once.CCC.SMPrimitives as SMP

-- Helper: just is injective
just-injective : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-injective refl = refl

------------------------------------------------------------------------
-- PairWF Implementation
------------------------------------------------------------------------

module PairWFImpl {FS : FrameSemantics} (program-bound : ℕ) (primSem : PrimSem) where
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

      -- setup-trace has no store-indirect instructions
      setup-tnsi : SMP.TraceNoStoreIndirect setup-trace
      setup-tnsi = tt , tt , tt

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
      -- This demonstrates the positive characterization approach:
      --   1. We have pair-trace-writes-above : TraceWritesAbove backup-slot pair-trace
      --   2. BeforeFrontier alloc loc means:
      --      - stack-before: slot k < backup-slot on current frame → use preserves-slot-below
      --      - stack-ancestor: different frame → use preserves-ancestor
      --      - heap-before: heap location → use preserves-heap-loc
      --
      -- Each case uses the appropriate positive lemma directly.
      mem-preserved-pair : ∀ loc → BeforeFrontier alloc loc → readLoc s-final loc ≡ readLoc s loc
      mem-preserved-pair (OnStack f' k) (stack-before {.f'} {.k} frame-eq k<next) =
        -- k < next-slot alloc = backup-slot, so slot k is below write region
        let f'≡frame : f' ≡ frame
            f'≡frame = frame-eq
        in subst (λ f → readLoc s-final (OnStack f k) ≡ readLoc s (OnStack f k))
                 (sym f'≡frame)
                 (exec-trace-preserves-slot-below pair-trace s alloc backup-slot k
                    pair-trace-writes-above pair-trace-no-store-indirect k<next)
      mem-preserved-pair (OnStack f' k) (stack-ancestor {.f'} cf≺f' _) =
        -- f' is an ancestor frame (current-frame alloc ≺ f')
        exec-trace-preserves-ancestor pair-trace s alloc f' k cf≺f' pair-trace-no-store-indirect
      mem-preserved-pair (OnHeap h) (heap-before _) =
        -- Heap location, use preserves-heap-loc
        exec-trace-preserves-heap-loc pair-trace s alloc h pair-trace-no-store-indirect

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

      -- fst-slot < snd-slot (since snd-slot = suc fst-slot)
      fst<snd : fst-slot < snd-slot
      fst<snd = ≤-refl  -- snd-slot = suc fst-slot, so fst-slot < suc fst-slot = snd-slot

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
      -- Frame equality for g's allocs
      frame-eq-g : current-frame alloc₁-reclaimed ≡ current-frame alloc-after-middle
      frame-eq-g =
        let frame-at-f' : current-frame alloc-after-f ≡ frame
            frame-at-f' = trans (exec-trace-preserves-frame f-trace s-after-setup alloc-after-setup)
                                (exec-trace-preserves-frame setup-trace s alloc)
        in trans refl  -- alloc₁-reclaimed.frame = frame
                 (sym (trans (exec-trace-preserves-frame middle-trace s-after-f alloc-after-f)
                             frame-at-f'))

      -- Input register in s-after-middle
      -- middle-trace = store-at-slot fst-slot ∷ restore-input backup-slot ∷ []
      -- After store-at-slot: Input unchanged
      -- After restore-input: Input = readLoc (OnStack frame backup-slot)
      -- backup-slot still has input-loc from setup-trace (f-trace and store fst-slot don't write there)
      input-after-middle : readReg (regs s-after-middle) Input ≡ input-loc
      input-after-middle = trans (cong (λ s' → readReg (regs s') Input) iam-middle-decomp)
                                 (trans (cong (λ s' → readReg (regs s') Input) iam-restore-via-abstract)
                                        iam-restore-input-result)
        where
          -- Intermediate states
          iam-s-after-mov : LocState FS
          iam-s-after-mov = proj₁ (exec-abstract mov-to-output s alloc)
          iam-alloc-after-mov : AllocState {FS}
          iam-alloc-after-mov = proj₂ (exec-abstract mov-to-output s alloc)
          iam-s-after-store-fst : LocState FS
          iam-s-after-store-fst = proj₁ (exec-abstract (store-at-slot fst-slot) s-after-f alloc-after-f)
          iam-alloc-after-store-fst : AllocState {FS}
          iam-alloc-after-store-fst = proj₂ (exec-abstract (store-at-slot fst-slot) s-after-f alloc-after-f)

          -- Frame equalities
          iam-frame-after-f : current-frame alloc-after-f ≡ frame
          iam-frame-after-f = trans (exec-trace-preserves-frame f-trace s-after-setup alloc-after-setup)
                                    (exec-trace-preserves-frame setup-trace s alloc)
          iam-frame-at-store-fst : current-frame iam-alloc-after-store-fst ≡ frame
          iam-frame-at-store-fst = trans (exec-abstract-preserves-frame (store-at-slot fst-slot) s-after-f alloc-after-f)
                                         iam-frame-after-f

          -- Step 1: mov-to-output sets Output = input-loc
          iam-mov-output : readReg (regs iam-s-after-mov) Output ≡ input-loc
          iam-mov-output = trans (writeReg-same (regs s) Output (readReg (regs s) Input)) rdi-eq

          -- Step 1: setup-trace stores input-loc to backup-slot
          iam-setup-decomp : exec-trace setup-trace s alloc ≡
                             exec-trace (store-at-slot backup-slot ∷ [])
                                        (proj₁ (exec-trace (mov-to-output ∷ []) s alloc))
                                        (proj₂ (exec-trace (mov-to-output ∷ []) s alloc))
          iam-setup-decomp = exec-trace-append (mov-to-output ∷ []) (store-at-slot backup-slot ∷ []) s alloc

          iam-mov-single : exec-trace (mov-to-output ∷ []) s alloc ≡ exec-abstract mov-to-output s alloc
          iam-mov-single = exec-trace-single mov-to-output s alloc not-halted

          iam-store-single : exec-trace (store-at-slot backup-slot ∷ []) iam-s-after-mov iam-alloc-after-mov ≡
                             exec-abstract (store-at-slot backup-slot) iam-s-after-mov iam-alloc-after-mov
          iam-store-single = exec-trace-single (store-at-slot backup-slot) iam-s-after-mov iam-alloc-after-mov
                               (exec-abstract-preserves-halted mov-to-output s alloc not-halted iph-mov-to-output)

          iam-store-via-abstract : s-after-setup ≡ proj₁ (exec-abstract (store-at-slot backup-slot) iam-s-after-mov iam-alloc-after-mov)
          iam-store-via-abstract = cong proj₁ (trans iam-setup-decomp (trans (cong₂ (λ s' a' → exec-trace (store-at-slot backup-slot ∷ []) s' a')
                                                                                    (cong proj₁ iam-mov-single) (cong proj₂ iam-mov-single))
                                                                             iam-store-single))

          iam-frame-after-mov : current-frame iam-alloc-after-mov ≡ frame
          iam-frame-after-mov = exec-abstract-preserves-frame mov-to-output s alloc

          iam-frame-after-setup : current-frame alloc-after-setup ≡ frame
          iam-frame-after-setup = exec-trace-preserves-frame setup-trace s alloc

          iam-store-result : readLoc (proj₁ (exec-abstract (store-at-slot backup-slot) iam-s-after-mov iam-alloc-after-mov))
                                     (OnStack (current-frame iam-alloc-after-mov) backup-slot) ≡ just (readReg (regs iam-s-after-mov) Output)
          iam-store-result = store-at-slot-result backup-slot iam-s-after-mov iam-alloc-after-mov

          -- Prove at frame directly, which is easier
          iam-store-at-frame : readLoc (proj₁ (exec-abstract (store-at-slot backup-slot) iam-s-after-mov iam-alloc-after-mov))
                                       (OnStack frame backup-slot) ≡ just input-loc
          iam-store-at-frame =
            subst (λ f → readLoc (proj₁ (exec-abstract (store-at-slot backup-slot) iam-s-after-mov iam-alloc-after-mov))
                                 (OnStack f backup-slot) ≡ just input-loc)
                  iam-frame-after-mov
                  (trans iam-store-result (cong just iam-mov-output))

          iam-backup-at-setup : readLoc s-after-setup (OnStack (current-frame alloc-after-setup) backup-slot) ≡ just input-loc
          iam-backup-at-setup =
            subst (λ f → readLoc s-after-setup (OnStack f backup-slot) ≡ just input-loc)
                  (sym iam-frame-after-setup)
                  (trans (cong (λ s' → readLoc s' (OnStack frame backup-slot)) iam-store-via-abstract)
                         iam-store-at-frame)

          -- Step 2: f-trace preserves backup-slot
          iam-backup-at-setup-frame : readLoc s-after-setup (OnStack frame backup-slot) ≡ just input-loc
          iam-backup-at-setup-frame = subst (λ f' → readLoc s-after-setup (OnStack f' backup-slot) ≡ just input-loc)
                                            iam-frame-after-setup iam-backup-at-setup

          iam-preserved-f : readLoc (proj₁ (exec-trace f-trace s-after-setup alloc-after-setup))
                                    (OnStack (current-frame alloc-after-setup) backup-slot) ≡ just input-loc
          iam-preserved-f = exec-trace-slot-value f-trace s-after-setup alloc-after-setup backup-slot input-loc
                              (subst (λ f' → readLoc s-after-setup (OnStack f' backup-slot) ≡ just input-loc)
                                     (sym iam-frame-after-setup) iam-backup-at-setup-frame)
                              f-writes-above f-tnsi

          iam-frame-eq-f : current-frame alloc-after-f ≡ frame
          iam-frame-eq-f = trans (exec-trace-preserves-frame f-trace s-after-setup alloc-after-setup) iam-frame-after-setup

          -- First convert from (current-frame alloc-after-setup) to frame using iam-frame-after-setup
          iam-preserved-at-frame : readLoc s-after-f (OnStack frame backup-slot) ≡ just input-loc
          iam-preserved-at-frame = subst (λ f' → readLoc s-after-f (OnStack f' backup-slot) ≡ just input-loc)
                                         iam-frame-after-setup iam-preserved-f

          -- Then convert from frame to (current-frame alloc-after-f) using sym iam-frame-eq-f
          iam-backup-at-f : readLoc s-after-f (OnStack (current-frame alloc-after-f) backup-slot) ≡ just input-loc
          iam-backup-at-f = subst (λ f' → readLoc s-after-f (OnStack f' backup-slot) ≡ just input-loc)
                                  (sym iam-frame-eq-f) iam-preserved-at-frame

          -- Step 3: store-at-slot fst-slot preserves backup-slot
          -- fst-slot = reclaim-g ≥ reclaim-f > suc backup-slot > backup-slot
          iam-backup<fst : backup-slot < fst-slot
          iam-backup<fst = ≤-trans reclaim-f-above-backup (IRResultAWF.reclaim-monotone result-g)

          iam-store-fst-preserves : readLoc iam-s-after-store-fst (OnStack (current-frame alloc-after-f) backup-slot) ≡
                                    readLoc s-after-f (OnStack (current-frame alloc-after-f) backup-slot)
          iam-store-fst-preserves = store-at-slot-preserves-other fst-slot backup-slot s-after-f alloc-after-f (inj₂ iam-backup<fst)

          -- Convert iam-backup-at-f from (current-frame alloc-after-f) to frame
          iam-backup-at-f-frame : readLoc s-after-f (OnStack frame backup-slot) ≡ just input-loc
          iam-backup-at-f-frame = subst (λ f' → readLoc s-after-f (OnStack f' backup-slot) ≡ just input-loc)
                                        iam-frame-after-f iam-backup-at-f

          -- store-fst-preserves works at (current-frame alloc-after-f)
          -- Convert to frame
          iam-store-fst-preserves-frame : readLoc iam-s-after-store-fst (OnStack frame backup-slot) ≡
                                          readLoc s-after-f (OnStack frame backup-slot)
          iam-store-fst-preserves-frame =
            trans (subst (λ f' → readLoc iam-s-after-store-fst (OnStack f' backup-slot) ≡
                                 readLoc iam-s-after-store-fst (OnStack (current-frame alloc-after-f) backup-slot))
                         iam-frame-after-f refl)
                  (trans iam-store-fst-preserves
                         (subst (λ f' → readLoc s-after-f (OnStack (current-frame alloc-after-f) backup-slot) ≡
                                        readLoc s-after-f (OnStack f' backup-slot))
                                iam-frame-after-f refl))

          iam-backup-at-store-fst : readLoc iam-s-after-store-fst (OnStack frame backup-slot) ≡ just input-loc
          iam-backup-at-store-fst = trans iam-store-fst-preserves-frame iam-backup-at-f-frame

          -- Step 4: restore-input sets Input to backup-slot value
          iam-not-halted-after-store-fst : halted iam-s-after-store-fst ≡ false
          iam-not-halted-after-store-fst = trans (store-at-slot-halted fst-slot s-after-f alloc-after-f) not-halted-after-f

          iam-middle-step1 : exec-trace middle-trace s-after-f alloc-after-f ≡
                             exec-trace (restore-input backup-slot ∷ [])
                                        (proj₁ (exec-trace (store-at-slot fst-slot ∷ []) s-after-f alloc-after-f))
                                        (proj₂ (exec-trace (store-at-slot fst-slot ∷ []) s-after-f alloc-after-f))
          iam-middle-step1 = exec-trace-append (store-at-slot fst-slot ∷ []) (restore-input backup-slot ∷ []) s-after-f alloc-after-f

          iam-store-fst-single : exec-trace (store-at-slot fst-slot ∷ []) s-after-f alloc-after-f ≡
                                 exec-abstract (store-at-slot fst-slot) s-after-f alloc-after-f
          iam-store-fst-single = exec-trace-single (store-at-slot fst-slot) s-after-f alloc-after-f not-halted-after-f

          iam-middle-decomp : s-after-middle ≡ proj₁ (exec-trace (restore-input backup-slot ∷ []) iam-s-after-store-fst iam-alloc-after-store-fst)
          iam-middle-decomp = cong proj₁ (trans iam-middle-step1 (cong₂ (λ s' a' → exec-trace (restore-input backup-slot ∷ []) s' a')
                                                                        (cong proj₁ iam-store-fst-single) (cong proj₂ iam-store-fst-single)))

          iam-restore-via-abstract : proj₁ (exec-trace (restore-input backup-slot ∷ []) iam-s-after-store-fst iam-alloc-after-store-fst) ≡
                                     proj₁ (exec-abstract (restore-input backup-slot) iam-s-after-store-fst iam-alloc-after-store-fst)
          iam-restore-via-abstract = cong proj₁ (exec-trace-single (restore-input backup-slot) iam-s-after-store-fst iam-alloc-after-store-fst
                                                   iam-not-halted-after-store-fst)

          iam-backup-slot-read : readLoc iam-s-after-store-fst (OnStack (current-frame iam-alloc-after-store-fst) backup-slot) ≡ just input-loc
          iam-backup-slot-read = subst (λ f' → readLoc iam-s-after-store-fst (OnStack f' backup-slot) ≡ just input-loc)
                                       (sym iam-frame-at-store-fst) iam-backup-at-store-fst

          -- The key: restore-input reads backup-slot and sets Input
          iam-restore-input-result : readReg (regs (proj₁ (exec-abstract (restore-input backup-slot) iam-s-after-store-fst iam-alloc-after-store-fst))) Input ≡ input-loc
          iam-restore-input-result with readLoc iam-s-after-store-fst (OnStack (current-frame iam-alloc-after-store-fst) backup-slot) | iam-backup-slot-read
          ... | just v | eq = trans (writeReg-same (regs iam-s-after-store-fst) Input v) (just-injective eq)

      -- Memory at slots ≥ reclaim-f is preserved from s₁' to s-after-middle
      -- s₁' has f's result at slots [suc backup-slot, reclaim-f)
      -- s-after-middle has: setup effects + f effects + middle effects
      -- middle-trace writes to fst-slot = reclaim-g ≥ reclaim-f, so memory < reclaim-f is same as after f
      -- Key: both paths have same memory at slots ≥ reclaim-f because:
      --   - s₁' = s₁ with Input rewritten (s₁ is from exec f-trace s alloc-after-backup)
      --   - s-after-middle is from exec middle-trace (exec f-trace (exec setup-trace s))
      --   - Both have f-trace's writes, and middle-trace writes above reclaim-f
      mem-preserved-for-g : ∀ slot → reclaim-f ≤ slot → slot < reclaim-g →
        readLoc s₁' (OnStack (current-frame alloc₁-reclaimed) slot) ≡
        readLoc s-after-middle (OnStack (current-frame alloc-after-middle) slot)
      mem-preserved-for-g slot reclaim-f≤slot slot<reclaim-g = mpg-final
        where
          -- Frame equalities
          mpg-frame-alloc₁ : current-frame alloc₁-reclaimed ≡ frame
          mpg-frame-alloc₁ = refl

          mpg-frame-after-middle : current-frame alloc-after-middle ≡ frame
          mpg-frame-after-middle = trans (exec-trace-preserves-frame middle-trace s-after-f alloc-after-f)
                                         (trans (exec-trace-preserves-frame f-trace s-after-setup alloc-after-setup)
                                                (exec-trace-preserves-frame setup-trace s alloc))

          mpg-frame-after-f : current-frame alloc-after-f ≡ frame
          mpg-frame-after-f = trans (exec-trace-preserves-frame f-trace s-after-setup alloc-after-setup)
                                    (exec-trace-preserves-frame setup-trace s alloc)

          mpg-frame-after-setup : current-frame alloc-after-setup ≡ frame
          mpg-frame-after-setup = exec-trace-preserves-frame setup-trace s alloc

          mpg-frame-after-backup : current-frame alloc-after-backup ≡ frame
          mpg-frame-after-backup = refl

          -- s₁' has same memory as s₁ (only regs differ)
          mpg-s1'-eq-s1 : readLoc s₁' (OnStack frame slot) ≡ readLoc s₁ (OnStack frame slot)
          mpg-s1'-eq-s1 = refl  -- s₁' = record s₁ { regs = ... } doesn't change memory

          -- s₁ = exec f-trace s alloc-after-backup (by trace-correct)
          mpg-s1-via-trace : s₁ ≡ proj₁ (exec-trace f-trace s alloc-after-backup)
          mpg-s1-via-trace = sym (IRResultAWF.trace-correct result-f)

          -- f-trace preserves slot (f writes below reclaim-f, slot ≥ reclaim-f)
          -- Using positive characterization: exec-trace-preserves-slot-above
          mpg-f-preserves-in-s1 : readLoc s₁ (OnStack frame slot) ≡ readLoc s (OnStack frame slot)
          mpg-f-preserves-in-s1 =
            let slot-at-s : readLoc s₁ (OnStack frame slot) ≡
                            readLoc (proj₁ (exec-trace f-trace s alloc-after-backup)) (OnStack frame slot)
                slot-at-s = cong (λ st → readLoc st (OnStack frame slot)) mpg-s1-via-trace
                -- current-frame alloc-after-backup = frame (definitionally)
                preserved : readLoc (proj₁ (exec-trace f-trace s alloc-after-backup)) (OnStack (current-frame alloc-after-backup) slot) ≡
                            readLoc s (OnStack (current-frame alloc-after-backup) slot)
                preserved = exec-trace-preserves-slot-above f-trace s alloc-after-backup reclaim-f slot
                              f-writes-below f-tnsi reclaim-f≤slot
            in trans slot-at-s preserved

          -- setup-trace preserves slot (setup writes at backup-slot, slot ≥ reclaim-f > backup-slot)
          -- setup-trace = mov-to-output ∷ store-at-slot backup-slot ∷ []
          -- Inline the proof since mem-preserved-setup is defined later in the file
          mpg-backup<slot : backup-slot < slot
          mpg-backup<slot = ≤-trans reclaim-f-above-backup reclaim-f≤slot

          mpg-setup-preserves : readLoc s-after-setup (OnStack frame slot) ≡ readLoc s (OnStack frame slot)
          mpg-setup-preserves =
            let -- Intermediate state after mov-to-output
                s₁' = proj₁ (exec-abstract mov-to-output s alloc)
                alloc₁' = proj₂ (exec-abstract mov-to-output s alloc)
                -- halted s₁' ≡ false
                halted-s₁' : halted s₁' ≡ false
                halted-s₁' = exec-abstract-preserves-halted mov-to-output s alloc not-halted iph-mov-to-output
                -- Decompose setup-trace
                decomp : exec-trace setup-trace s alloc ≡
                         exec-trace (store-at-slot backup-slot ∷ []) s₁' alloc₁'
                decomp = exec-trace-cons mov-to-output (store-at-slot backup-slot ∷ []) s alloc not-halted
                -- exec-trace-single for the remaining trace
                single : exec-trace (store-at-slot backup-slot ∷ []) s₁' alloc₁' ≡
                         exec-abstract (store-at-slot backup-slot) s₁' alloc₁'
                single = exec-trace-single (store-at-slot backup-slot) s₁' alloc₁' halted-s₁'
                -- s-after-setup = proj₁ (exec-abstract (store-at-slot backup-slot) s₁' alloc₁')
                s-after-setup-eq : s-after-setup ≡ proj₁ (exec-abstract (store-at-slot backup-slot) s₁' alloc₁')
                s-after-setup-eq = cong proj₁ (trans decomp single)
                -- mov-to-output preserves memory (only writes registers)
                mov-preserves : readLoc s₁' (OnStack (current-frame alloc) slot) ≡
                                readLoc s (OnStack (current-frame alloc) slot)
                mov-preserves = readLoc-stackMem-eq s₁' s (OnStack (current-frame alloc) slot) refl refl
                -- store-at-slot backup-slot preserves slot
                store-preserves : readLoc (proj₁ (exec-abstract (store-at-slot backup-slot) s₁' alloc₁'))
                                    (OnStack (current-frame alloc₁') slot) ≡
                                  readLoc s₁' (OnStack (current-frame alloc₁') slot)
                store-preserves = store-at-slot-preserves-other backup-slot slot s₁' alloc₁' (inj₁ mpg-backup<slot)
                -- Combine
                result : readLoc s-after-setup (OnStack frame slot) ≡ readLoc s (OnStack frame slot)
                result = trans (cong (λ st → readLoc st (OnStack frame slot)) s-after-setup-eq)
                               (trans store-preserves mov-preserves)
            in result

          -- f-trace preserves slot in s-after-f path
          -- f writes below reclaim-f, slot ≥ reclaim-f
          mpg-f-preserves-in-path2 : readLoc s-after-f (OnStack frame slot) ≡ readLoc s-after-setup (OnStack frame slot)
          mpg-f-preserves-in-path2 =
            let preserved : readLoc (proj₁ (exec-trace f-trace s-after-setup alloc-after-setup))
                              (OnStack (current-frame alloc-after-setup) slot) ≡
                            readLoc s-after-setup (OnStack (current-frame alloc-after-setup) slot)
                preserved = exec-trace-preserves-slot-above f-trace s-after-setup alloc-after-setup reclaim-f slot
                              f-writes-below f-tnsi reclaim-f≤slot
            in subst (λ f' → readLoc s-after-f (OnStack f' slot) ≡ readLoc s-after-setup (OnStack f' slot))
                     mpg-frame-after-setup preserved

          -- middle-trace preserves slot if slot < fst-slot = reclaim-g
          -- middle-trace = store-at-slot fst-slot ∷ restore-input backup-slot ∷ []
          -- store-at-slot fst-slot writes at fst-slot = reclaim-g
          -- restore-input doesn't write to stack
          mpg-middle-writes-above : SMP.TraceWritesAbove reclaim-g middle-trace
          mpg-middle-writes-above = ≤-refl , tt

          -- For slot < reclaim-g, middle-trace preserves the slot
          -- middle-trace writes above reclaim-g, slot < reclaim-g, so slot not in write set
          mpg-middle-tnsi : SMP.TraceNoStoreIndirect middle-trace
          mpg-middle-tnsi = tt , tt , tt

          mpg-middle-preserves : slot < reclaim-g →
            readLoc s-after-middle (OnStack frame slot) ≡ readLoc s-after-f (OnStack frame slot)
          mpg-middle-preserves slot<rg =
            -- middle-trace writes above reclaim-g, slot < reclaim-g, so slot is preserved
            let preserved : readLoc (proj₁ (exec-trace middle-trace s-after-f alloc-after-f))
                              (OnStack (current-frame alloc-after-f) slot) ≡
                            readLoc s-after-f (OnStack (current-frame alloc-after-f) slot)
                preserved = exec-trace-preserves-slot-below middle-trace s-after-f alloc-after-f reclaim-g slot
                              mpg-middle-writes-above mpg-middle-tnsi slot<rg
            in subst (λ f' → readLoc s-after-middle (OnStack f' slot) ≡ readLoc s-after-f (OnStack f' slot))
                     mpg-frame-after-f preserved

          -- g-trace only reads from [reclaim-f, reclaim-g), so we only need memory
          -- agreement in that range. The slot<reclaim-g bound ensures middle-trace
          -- preserves the slot value.
          mpg-slot-proof : readLoc s₁' (OnStack frame slot) ≡ readLoc s-after-middle (OnStack frame slot)
          mpg-slot-proof =
            trans mpg-s1'-eq-s1
                  (trans mpg-f-preserves-in-s1
                         (trans (sym mpg-setup-preserves)
                                (trans (sym mpg-f-preserves-in-path2)
                                       (sym (mpg-middle-preserves slot<reclaim-g)))))

          mpg-final : readLoc s₁' (OnStack (current-frame alloc₁-reclaimed) slot) ≡
                      readLoc s-after-middle (OnStack (current-frame alloc-after-middle) slot)
          mpg-final = subst₂ (λ f1 f2 → readLoc s₁' (OnStack f1 slot) ≡ readLoc s-after-middle (OnStack f2 slot))
                             (sym mpg-frame-alloc₁) (sym mpg-frame-after-middle) mpg-slot-proof

      -- s₂ output (from result-g) - converted to trace form using trace-correct
      s₂-output : readReg (regs (proj₁ (exec-trace g-trace s₁' alloc₁-reclaimed))) Output ≡ snd-loc
      s₂-output = subst (λ s' → readReg (regs s') Output ≡ snd-loc)
                        (sym (IRResultAWF.trace-correct result-g))
                        (IRResultAWF.rax-is-result result-g)

      -- halted flags
      not-halted-s1' : halted s₁' ≡ false
      not-halted-s1' = IRResultAWF.not-halted result-f  -- s₁' has same halted as s₁

      output-after-g-is-snd : readReg (regs s-after-g) Output ≡ snd-loc
      output-after-g-is-snd =
        let determ = exec-trace-output-deterministic g-trace s₁' s-after-middle
                       alloc₁-reclaimed alloc-after-middle reclaim-f reclaim-g
                       not-halted-s1' not-halted-after-middle
                       frame-eq-g
                       (trans rdi-eq₁ (sym input-after-middle))
                       g-reads-above g-reads-below g-writes-above g-tnsi
                       mem-preserved-for-g
        in trans (sym determ) s₂-output

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
      mem-preserved-setup : ∀ slot → suc backup-slot ≤ slot → slot < reclaim-f →
        readLoc s (OnStack (current-frame alloc-after-backup) slot) ≡
        readLoc s-after-setup (OnStack (current-frame alloc-after-setup) slot)
      mem-preserved-setup slot suc-b≤slot _ =
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

            -- Step 8-9: store-at-slot backup-slot preserves slot (since backup-slot < slot)
            -- suc-b≤slot : suc backup-slot ≤ slot, which is backup-slot < slot
            store-preserves : readLoc (proj₁ (exec-abstract (store-at-slot backup-slot) s₁ alloc₁))
                                (OnStack (current-frame alloc₁) slot) ≡
                              readLoc s₁ (OnStack (current-frame alloc₁) slot)
            store-preserves = store-at-slot-preserves-other backup-slot slot s₁ alloc₁ (inj₁ suc-b≤slot)

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
                       alloc-after-backup alloc-after-setup (suc backup-slot) reclaim-f
                       not-halted not-halted-after-setup
                       frame-eq-backup-setup
                       (sym input-preserved-setup)
                       f-reads-above f-reads-below f-writes-above f-tnsi
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
            inner = store-at-slot-preserves-other snd-slot fst-slot s' alloc' (inj₂ fst<snd)
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
      ----------------------------------------------------------------------
      -- fst-valid: Validity of f's result at fst-loc in s-final
      --
      -- Strategy:
      -- 1. result-f gives validity at s₁ with final-alloc result-f
      -- 2. Transfer validity to s-after-f using validityWF-mem-preserved-excluding
      --    (memory differs only at backup-slot, which is not a sub-location)
      -- 3. Adjust alloc to alloc₁-reclaimed (frontier monotone)
      -- 4. Apply validityWF-trace-preserves for rest-trace to reach s-final
      -- 5. Adjust alloc to alloc₃ (frontier monotone)
      ----------------------------------------------------------------------

      -- Key: fst-loc's sub-locations are at:
      --   - Input slots: < backup-slot (from x)
      --   - Fresh allocations: ≥ suc backup-slot (from f)
      -- So backup-slot is a "gap" never accessed by fst-loc's structure.

      -- rest-trace: the trace from s-after-f to s-final
      rest-trace-after-f : AbstractTrace
      rest-trace-after-f = middle-trace ++ g-trace ++ final-trace

      -- rest-trace writes above reclaim-f
      rest-trace-writes-above : SMP.TraceWritesAbove reclaim-f rest-trace-after-f
      rest-trace-writes-above =
        -- middle-trace = store-at-slot fst-slot ∷ restore-input backup-slot ∷ []
        -- fst-slot = reclaim-g ≥ reclaim-f (from reclaim-monotone result-g)
        -- restore-input doesn't write to stack
        let reclaim-f≤reclaim-g : reclaim-f ≤ reclaim-g
            reclaim-f≤reclaim-g = IRResultAWF.reclaim-monotone result-g
            middle-writes : SMP.TraceWritesAbove reclaim-f middle-trace
            middle-writes = reclaim-f≤reclaim-g , tt
            g-writes : SMP.TraceWritesAbove reclaim-f g-trace
            g-writes = g-writes-above
            final-writes : SMP.TraceWritesAbove reclaim-f final-trace
            final-writes = ≤-trans reclaim-f≤reclaim-g (n≤1+n reclaim-g) , tt
        in SMP.trace-writes-above-append reclaim-f middle-trace (g-trace ++ final-trace)
             middle-writes
             (SMP.trace-writes-above-append reclaim-f g-trace final-trace g-writes final-writes)

      -- rest-trace has no store-indirect
      rest-trace-tnsi : SMP.TraceNoStoreIndirect rest-trace-after-f
      rest-trace-tnsi =
        let middle-tnsi : SMP.TraceNoStoreIndirect middle-trace
            middle-tnsi = tt , tt , tt
            final-tnsi : SMP.TraceNoStoreIndirect final-trace
            final-tnsi = tt , tt , tt
        in SMP.trace-no-store-indirect-append middle-trace (g-trace ++ final-trace)
             middle-tnsi
             (SMP.trace-no-store-indirect-append g-trace final-trace g-tnsi final-tnsi)

      -- fst-loc is before frontier at alloc₁-reclaimed
      fst-loc-before-reclaimed : BeforeFrontier alloc₁-reclaimed fst-loc
      fst-loc-before-reclaimed = IRResultAWF.reclaim-preserves-result result-f reclaim-f-fits

      -- rest-trace preserves halted
      rest-trace-tph : TracePreservesHaltedP rest-trace-after-f
      rest-trace-tph = tph-++ middle-tph (tph-++ g-tph final-tph)

      -- Not halted after f-trace (already proven as not-halted-after-f)

      -- alloc₁-reclaimed has next-slot = reclaim-f
      alloc₁-reclaimed-next : next-slot alloc₁-reclaimed ≡ reclaim-f
      alloc₁-reclaimed-next = refl

      -- Memory at BeforeFrontier locations (except backup) is same in s₁ and s-after-f
      -- This is the key lemma for transferring validity between the two execution paths.
      -- f-trace produces the same memory writes in both cases because:
      --   1. Input register is the same (input-preserved-setup)
      --   2. Memory at slots it reads (≥ suc backup-slot) is the same (mem-preserved-setup)
      --   3. f-trace is deterministic given these inputs
      f-trace-mem-same : ∀ (loc' : ValueLocation FS) →
        BeforeFrontier alloc₁-reclaimed loc' →
        loc' ≢ OnStack frame backup-slot →
        readLoc s₁ loc' ≡ readLoc s-after-f loc'
      f-trace-mem-same (OnStack f' k) (stack-before f'-eq k<reclaim-f) loc'≢backup =
        -- f' = frame, k < reclaim-f
        -- Case split on whether k is in the write region [suc backup-slot, reclaim-f)
        let f'≡frame : f' ≡ frame
            f'≡frame = f'-eq
            -- Convert loc'≢backup from OnStack f' k ≢ ... to OnStack frame k ≢ ...
            loc'≢backup' : OnStack frame k ≢ OnStack frame backup-slot
            loc'≢backup' = subst (λ f → OnStack f k ≢ OnStack frame backup-slot)
                                 f'≡frame loc'≢backup
            result-with-frame : readLoc s₁ (OnStack frame k) ≡ readLoc s-after-f (OnStack frame k)
            result-with-frame = ftms-stack-current k refl k<reclaim-f loc'≢backup'
        in subst (λ f → readLoc s₁ (OnStack f k) ≡ readLoc s-after-f (OnStack f k))
                 (sym f'≡frame) result-with-frame
        where
          -- Helper: s₁ = exec f-trace s, s-after-f = exec f-trace s-after-setup
          ftms-s1-eq : s₁ ≡ proj₁ (exec-trace f-trace s alloc-after-backup)
          ftms-s1-eq = sym (IRResultAWF.trace-correct result-f)

          -- Memory agreement at slots in [suc backup-slot, reclaim-f) (same frame on both sides)
          -- Since pair doesn't change frames, we use alloc-after-backup for both
          -- f reads in [suc backup-slot, reclaim-f), so we only need agreement there
          ftms-mem-agree : ∀ slot → suc backup-slot ≤ slot → slot < reclaim-f →
            readLoc s (OnStack (current-frame alloc-after-backup) slot) ≡
            readLoc s-after-setup (OnStack (current-frame alloc-after-backup) slot)
          ftms-mem-agree slot suc-b≤slot slot<rf =
            let -- mem-preserved-setup gives equality with different frames
                raw : readLoc s (OnStack (current-frame alloc-after-backup) slot) ≡
                      readLoc s-after-setup (OnStack (current-frame alloc-after-setup) slot)
                raw = mem-preserved-setup slot suc-b≤slot slot<rf
                -- current-frame alloc-after-backup = current-frame alloc (definitionally)
                -- exec-trace-preserves-frame gives: current-frame alloc-after-setup = current-frame alloc
                -- So: current-frame alloc-after-setup = current-frame alloc = current-frame alloc-after-backup
                setup-frame : current-frame alloc-after-setup ≡ current-frame alloc
                setup-frame = exec-trace-preserves-frame setup-trace s alloc
                -- subst replaces current-frame alloc-after-setup with current-frame alloc
                -- (which equals current-frame alloc-after-backup definitionally)
            in subst (λ f → readLoc s (OnStack (current-frame alloc-after-backup) slot) ≡
                           readLoc s-after-setup (OnStack f slot))
                     setup-frame raw

          -- For slots < suc backup-slot and ≠ backup-slot, setup preserves them
          ftms-setup-preserves-below : ∀ slot → slot < backup-slot →
            readLoc s-after-setup (OnStack frame slot) ≡ readLoc s (OnStack frame slot)
          ftms-setup-preserves-below slot slot<backup =
            -- setup-trace = mov-to-output ∷ store-at-slot backup-slot ∷ []
            -- mov-to-output doesn't write memory
            -- store-at-slot backup-slot writes only at backup-slot, slot < backup-slot
            let s₁' = proj₁ (exec-abstract mov-to-output s alloc)
                alloc₁' = proj₂ (exec-abstract mov-to-output s alloc)
                halted-s₁' : halted s₁' ≡ false
                halted-s₁' = exec-abstract-preserves-halted mov-to-output s alloc not-halted iph-mov-to-output
                decomp : exec-trace setup-trace s alloc ≡
                         exec-trace (store-at-slot backup-slot ∷ []) s₁' alloc₁'
                decomp = exec-trace-cons mov-to-output (store-at-slot backup-slot ∷ []) s alloc not-halted
                single : exec-trace (store-at-slot backup-slot ∷ []) s₁' alloc₁' ≡
                         exec-abstract (store-at-slot backup-slot) s₁' alloc₁'
                single = exec-trace-single (store-at-slot backup-slot) s₁' alloc₁' halted-s₁'
                s-setup-eq : s-after-setup ≡ proj₁ (exec-abstract (store-at-slot backup-slot) s₁' alloc₁')
                s-setup-eq = cong proj₁ (trans decomp single)
                mov-preserves : readLoc s₁' (OnStack frame slot) ≡ readLoc s (OnStack frame slot)
                mov-preserves = readLoc-stackMem-eq s₁' s (OnStack frame slot) refl refl
                store-preserves : readLoc (proj₁ (exec-abstract (store-at-slot backup-slot) s₁' alloc₁'))
                                    (OnStack (current-frame alloc₁') slot) ≡
                                  readLoc s₁' (OnStack (current-frame alloc₁') slot)
                store-preserves = store-at-slot-preserves-other backup-slot slot s₁' alloc₁' (inj₂ slot<backup)
            in trans (cong (λ st → readLoc st (OnStack frame slot)) s-setup-eq)
                     (trans store-preserves mov-preserves)

          -- f-trace preserves slots < suc backup-slot (f writes above suc backup-slot)
          ftms-f-preserves-below : ∀ slot → slot < suc backup-slot →
            readLoc (proj₁ (exec-trace f-trace s alloc-after-backup)) (OnStack frame slot) ≡
            readLoc s (OnStack frame slot)
          ftms-f-preserves-below slot slot<suc-b =
            exec-trace-preserves-slot-below f-trace s alloc-after-backup (suc backup-slot) slot
              f-writes-above f-tnsi slot<suc-b

          ftms-f-preserves-below-setup : ∀ slot → slot < suc backup-slot →
            readLoc (proj₁ (exec-trace f-trace s-after-setup alloc-after-setup)) (OnStack frame slot) ≡
            readLoc s-after-setup (OnStack frame slot)
          ftms-f-preserves-below-setup slot slot<suc-b =
            let frame-eq : current-frame alloc-after-setup ≡ frame
                frame-eq = exec-trace-preserves-frame setup-trace s alloc
                preserved : readLoc (proj₁ (exec-trace f-trace s-after-setup alloc-after-setup))
                              (OnStack (current-frame alloc-after-setup) slot) ≡
                            readLoc s-after-setup (OnStack (current-frame alloc-after-setup) slot)
                preserved = exec-trace-preserves-slot-below f-trace s-after-setup alloc-after-setup (suc backup-slot) slot
                              f-writes-above f-tnsi slot<suc-b
            in subst (λ f' → readLoc (proj₁ (exec-trace f-trace s-after-setup alloc-after-setup)) (OnStack f' slot) ≡
                            readLoc s-after-setup (OnStack f' slot)) frame-eq preserved

          -- Main case analysis: slot k in [0, reclaim-f)
          ftms-stack-current : ∀ k → frame ≡ frame → k < reclaim-f →
            OnStack frame k ≢ OnStack frame backup-slot →
            readLoc s₁ (OnStack frame k) ≡ readLoc s-after-f (OnStack frame k)
          ftms-stack-current k _ k<rf k≢backup with suc backup-slot ≤? k
          ... | yes suc-b≤k =
            -- k is in write region [suc backup-slot, reclaim-f)
            -- Use exec-trace-mem-deterministic with same allocator (pair doesn't change frame)
            let mem-det-raw : readLoc (proj₁ (exec-trace f-trace s alloc-after-backup)) (OnStack frame k) ≡
                              readLoc (proj₁ (exec-trace f-trace s-after-setup alloc-after-backup)) (OnStack frame k)
                mem-det-raw = exec-trace-mem-deterministic f-trace s s-after-setup
                                alloc-after-backup alloc-after-backup (suc backup-slot) reclaim-f
                                not-halted not-halted-after-setup
                                refl  -- same allocator, frame equality is refl
                                (sym input-preserved-setup)
                                f-reads-above f-reads-below f-writes-above f-writes-below f-tnsi
                                ftms-mem-agree
                                k suc-b≤k k<rf
                -- Connect alloc-after-backup execution to alloc-after-setup execution (same frame)
                frame-eq : current-frame alloc-after-backup ≡ current-frame alloc-after-setup
                frame-eq = sym (exec-trace-preserves-frame setup-trace s alloc)
                state-eq : proj₁ (exec-trace f-trace s-after-setup alloc-after-backup) ≡ s-after-f
                state-eq = exec-trace-same-frame f-trace s-after-setup alloc-after-backup alloc-after-setup frame-eq
                mem-det : readLoc (proj₁ (exec-trace f-trace s alloc-after-backup)) (OnStack frame k) ≡
                          readLoc s-after-f (OnStack frame k)
                mem-det = trans mem-det-raw (cong (λ st → readLoc st (OnStack frame k)) state-eq)
                s1-eq : readLoc s₁ (OnStack frame k) ≡
                        readLoc (proj₁ (exec-trace f-trace s alloc-after-backup)) (OnStack frame k)
                s1-eq = cong (λ st → readLoc st (OnStack frame k)) ftms-s1-eq
            in trans s1-eq mem-det
          ... | no suc-b≰k =
            -- k < suc backup-slot, and k ≠ backup-slot (from k≢backup), so k < backup-slot
            let k<suc-b' : k < suc backup-slot
                k<suc-b' = ≰⇒> suc-b≰k
                -- k < suc backup-slot means k ≤ backup-slot
                k≤backup : k ≤ backup-slot
                k≤backup = m<1+n⇒m≤n k<suc-b'
                -- Extract k ≢ backup-slot from loc inequality
                k≢backup-slot : k ≢ backup-slot
                k≢backup-slot k≡b = k≢backup (cong (OnStack frame) k≡b)
                -- Use ≤∧≢⇒< to get k < backup-slot
                k<backup : k < backup-slot
                k<backup = ≤∧≢⇒< k≤backup k≢backup-slot
                -- f-trace preserves k in both executions
                f-preserves-s : readLoc (proj₁ (exec-trace f-trace s alloc-after-backup)) (OnStack frame k) ≡
                                readLoc s (OnStack frame k)
                f-preserves-s = ftms-f-preserves-below k k<suc-b'
                f-preserves-setup : readLoc s-after-f (OnStack frame k) ≡
                                    readLoc s-after-setup (OnStack frame k)
                f-preserves-setup = ftms-f-preserves-below-setup k k<suc-b'
                -- setup preserves k (k < backup-slot)
                setup-preserves : readLoc s-after-setup (OnStack frame k) ≡ readLoc s (OnStack frame k)
                setup-preserves = ftms-setup-preserves-below k k<backup
                -- Combine: s₁ → s → s-after-setup → s-after-f
                s1-eq : readLoc s₁ (OnStack frame k) ≡
                        readLoc (proj₁ (exec-trace f-trace s alloc-after-backup)) (OnStack frame k)
                s1-eq = cong (λ st → readLoc st (OnStack frame k)) ftms-s1-eq
            in trans s1-eq (trans f-preserves-s (trans (sym setup-preserves) (sym f-preserves-setup)))

      f-trace-mem-same (OnStack f' k) (stack-ancestor cf≺f' _) loc'≢backup =
        -- f' is an ancestor frame, f-trace doesn't write to ancestor frames
        -- Uses exec-trace-preserves-ancestor with frame ordering ≺
        -- cf≺f' : current-frame alloc₁-reclaimed ≺ f'
        -- All allocators have the same current-frame (= frame), need subst for alloc-after-setup
        let -- s₁ = exec f-trace s alloc-after-backup
            -- current-frame alloc₁-reclaimed = current-frame alloc = current-frame alloc-after-backup = frame
            -- So cf≺f' also proves current-frame alloc-after-backup ≺ f'
            s1-eq-s : readLoc s₁ (OnStack f' k) ≡ readLoc s (OnStack f' k)
            s1-eq-s = trans (cong (λ st → readLoc st (OnStack f' k))
                                  (sym (IRResultAWF.trace-correct result-f)))
                            (exec-trace-preserves-ancestor f-trace s alloc-after-backup f' k cf≺f' f-tnsi)
            -- setup-trace preserves ancestors (current-frame alloc = frame, and cf≺f' : frame ≺ f')
            setup-preserves : readLoc s-after-setup (OnStack f' k) ≡ readLoc s (OnStack f' k)
            setup-preserves = exec-trace-preserves-ancestor setup-trace s alloc f' k cf≺f' setup-tnsi
            -- f-trace preserves ancestors from s-after-setup
            -- Need subst because current-frame alloc-after-setup ≡ frame (by exec-trace-preserves-frame)
            frame-eq-setup : current-frame alloc-after-setup ≡ frame
            frame-eq-setup = exec-trace-preserves-frame setup-trace s alloc
            cf-after-setup≺f' : current-frame alloc-after-setup ≺ f'
            cf-after-setup≺f' = subst (λ f → f ≺ f') (sym frame-eq-setup) cf≺f'
            f-preserves-setup : readLoc s-after-f (OnStack f' k) ≡ readLoc s-after-setup (OnStack f' k)
            f-preserves-setup = exec-trace-preserves-ancestor f-trace s-after-setup alloc-after-setup f' k
                                  cf-after-setup≺f' f-tnsi
        in trans s1-eq-s (trans (sym setup-preserves) (sym f-preserves-setup))

      f-trace-mem-same (OnHeap hl) (heap-before _) loc'≢backup =
        -- f-trace doesn't write to heap (TraceNoStoreIndirect)
        let f-preserves-s : readLoc (proj₁ (exec-trace f-trace s alloc-after-backup)) (OnHeap hl) ≡
                            readLoc s (OnHeap hl)
            f-preserves-s = exec-trace-preserves-heap-loc f-trace s alloc-after-backup hl f-tnsi
            -- f-trace preserves heap from s-after-setup
            f-preserves-setup : readLoc s-after-f (OnHeap hl) ≡ readLoc s-after-setup (OnHeap hl)
            f-preserves-setup = exec-trace-preserves-heap-loc f-trace s-after-setup alloc-after-setup hl f-tnsi
            -- setup-trace preserves heap
            setup-preserves : readLoc s-after-setup (OnHeap hl) ≡ readLoc s (OnHeap hl)
            setup-preserves = exec-trace-preserves-heap-loc setup-trace s alloc hl setup-tnsi
            s1-eq : readLoc s₁ (OnHeap hl) ≡
                    readLoc (proj₁ (exec-trace f-trace s alloc-after-backup)) (OnHeap hl)
            s1-eq = cong (λ st → readLoc st (OnHeap hl)) (sym (IRResultAWF.trace-correct result-f))
        in trans s1-eq (trans f-preserves-s (trans (sym setup-preserves) (sym f-preserves-setup)))

      -- Step 1-2: Get validity at s₁ with alloc₁-reclaimed
      valid-s1-reclaimed : ValidAtWF mF alloc₁-reclaimed (eval primSem f x) fst-loc s₁
      valid-s1-reclaimed = IRResultAWF.reclaim-preserves-validity result-f reclaim-f-fits

      -- Step 3: Transfer validity from s₁ to s-after-f
      valid-at-s-after-f : ValidAtWF mF alloc₁-reclaimed (eval primSem f x) fst-loc s-after-f
      valid-at-s-after-f = validityWF-mem-preserved-excluding alloc₁-reclaimed
                             (eval primSem f x) fst-loc frame backup-slot s₁ s-after-f
                             fst-loc-before-reclaimed f-trace-mem-same valid-s1-reclaimed

      fst-valid : ValidAtWF mF alloc₃ (eval primSem f x) fst-loc s-final
      fst-valid =
        let -- Step 4: Apply validityWF-trace-preserves for rest-trace
            -- rest-trace writes above reclaim-f, and fst-loc is before reclaim-f frontier
            valid-at-s-final : ValidAtWF mF alloc₁-reclaimed (eval primSem f x) fst-loc
                                 (proj₁ (exec-trace rest-trace-after-f s-after-f alloc₁-reclaimed))
            valid-at-s-final = validityWF-trace-preserves alloc₁-reclaimed
                                 rest-trace-after-f (eval primSem f x) fst-loc s-after-f
                                 fst-loc-before-reclaimed valid-at-s-after-f
                                 rest-trace-writes-above rest-trace-tnsi

            -- Step 5: Connect the trace execution to s-final
            -- s-final = proj₁ (exec-trace (f-trace ++ rest-trace-after-f) s-after-setup alloc-after-setup)
            -- We need: s-final ≡ proj₁ (exec-trace rest-trace-after-f s-after-f alloc₁-reclaimed)
            -- But alloc differs! We have alloc-after-f vs alloc₁-reclaimed
            -- Key: exec-trace-same-frame shows result is same when frames equal
            s-final-eq-rest : proj₁ (exec-trace rest-trace-after-f s-after-f alloc-after-f) ≡
                              proj₁ (exec-trace rest-trace-after-f s-after-f alloc₁-reclaimed)
            s-final-eq-rest = exec-trace-same-frame rest-trace-after-f s-after-f alloc-after-f alloc₁-reclaimed
                                (trans (exec-trace-preserves-frame f-trace s-after-setup alloc-after-setup)
                                       (exec-trace-preserves-frame setup-trace s alloc))

            -- s-final connects to rest-trace execution
            -- s-final = s-after-final = proj₁ (exec-trace final-trace s-after-g alloc-after-g)
            -- And we have s-final-eq : s-final ≡ s-after-final
            -- Need to show this equals exec-trace rest-trace-after-f s-after-f ...

            -- Actually, let's use the trace decomposition more directly
            rest-eq : exec-trace rest-trace-after-f s-after-f alloc-after-f ≡
                      exec-trace final-trace s-after-g alloc-after-g
            rest-eq = trans (exec-trace-append middle-trace (g-trace ++ final-trace) s-after-f alloc-after-f)
                      (exec-trace-append g-trace final-trace s-after-middle alloc-after-middle)

            -- Transfer validity using state equality
            valid-alloc-after-f : ValidAtWF mF alloc₁-reclaimed (eval primSem f x) fst-loc
                                    (proj₁ (exec-trace rest-trace-after-f s-after-f alloc-after-f))
            valid-alloc-after-f = subst (λ s' → ValidAtWF mF alloc₁-reclaimed (eval primSem f x) fst-loc s')
                                    (sym s-final-eq-rest) valid-at-s-final

            -- Connect to s-final via s-final-eq and trace decomposition
            valid-s-after-final : ValidAtWF mF alloc₁-reclaimed (eval primSem f x) fst-loc s-after-final
            valid-s-after-final = subst (λ s' → ValidAtWF mF alloc₁-reclaimed (eval primSem f x) fst-loc s')
                                    (cong proj₁ rest-eq) valid-alloc-after-f

            valid-s-final : ValidAtWF mF alloc₁-reclaimed (eval primSem f x) fst-loc s-final
            valid-s-final = subst (λ s' → ValidAtWF mF alloc₁-reclaimed (eval primSem f x) fst-loc s')
                              (sym s-final-eq) valid-s-after-final

            -- Step 6: Advance frontier from alloc₁-reclaimed to alloc₃
            valid-alloc₃ : ValidAtWF mF alloc₃ (eval primSem f x) fst-loc s-final
            valid-alloc₃ = validityWF-frontier-advance (eval primSem f x) fst-loc s-final
                             refl
                             (≤-trans (IRResultAWF.reclaim-monotone result-g) (m≤m+n reclaim-g ps))
                             ≤-refl
                             valid-s-final

        in valid-alloc₃

      ----------------------------------------------------------------------
      -- snd-valid: Validity of g's result at snd-loc in s-final
      --
      -- Strategy (similar to fst-valid):
      -- 1. result-g gives validity at s₂ with final-alloc result-g
      -- 2. Use reclaim-preserves-validity to get validity at alloc with next-slot = reclaim-g
      -- 3. Transfer validity from s₂ to s-after-g using validityWF-mem-preserved-excluding
      --    (memory differs at backup-slot and fst-slot, neither is a sub-location of snd-loc)
      -- 4. Apply validityWF-trace-preserves for final-trace to reach s-final
      -- 5. Adjust alloc to alloc₃ (frontier monotone)
      ----------------------------------------------------------------------

      -- Alloc state after g's reclaim: next-slot = reclaim-g
      alloc-reclaim-g : AllocState {FS}
      alloc-reclaim-g = record alloc { next-slot = reclaim-g }

      -- snd-loc is before frontier at alloc-reclaim-g
      snd-loc-before-reclaim-g : BeforeFrontier alloc-reclaim-g snd-loc
      snd-loc-before-reclaim-g = IRResultAWF.reclaim-preserves-result result-g reclaim-g-fits

      -- Get validity at s₂ with alloc-reclaim-g
      valid-s2-reclaimed : ValidAtWF mG alloc-reclaim-g (eval primSem g x) snd-loc s₂
      valid-s2-reclaimed = IRResultAWF.reclaim-preserves-validity result-g reclaim-g-fits

      -- Memory at BeforeFrontier locations (except backup-slot and fst-slot) is same in s₂ and s-after-g
      -- snd-loc's sub-locations are:
      --   - Input locations from x: at slots < backup-slot
      --   - Fresh allocations by g: at slots [reclaim-f, reclaim-g)
      -- Neither backup-slot nor fst-slot (= reclaim-g) are sub-locations.
      g-trace-mem-same : ∀ (loc' : ValueLocation FS) →
        BeforeFrontier alloc-reclaim-g loc' →
        loc' ≢ OnStack frame backup-slot →
        loc' ≢ OnStack frame fst-slot →
        readLoc s₂ loc' ≡ readLoc s-after-g loc'
      g-trace-mem-same (OnStack f' k) (stack-before f'-eq k<reclaim-g) loc'≢backup loc'≢fst =
        -- f' = frame, k < reclaim-g
        let f'≡frame : f' ≡ frame
            f'≡frame = f'-eq
            loc'≢backup' : OnStack frame k ≢ OnStack frame backup-slot
            loc'≢backup' = subst (λ f → OnStack f k ≢ OnStack frame backup-slot) f'≡frame loc'≢backup
            result-with-frame : readLoc s₂ (OnStack frame k) ≡ readLoc s-after-g (OnStack frame k)
            result-with-frame = gtms-stack-current k k<reclaim-g loc'≢backup'
        in subst (λ f → readLoc s₂ (OnStack f k) ≡ readLoc s-after-g (OnStack f k))
                 (sym f'≡frame) result-with-frame
        where
          gtms-s2-eq : s₂ ≡ proj₁ (exec-trace g-trace s₁' alloc₁-reclaimed)
          gtms-s2-eq = sym (IRResultAWF.trace-correct result-g)

          -- Memory agreement for exec-trace-mem-deterministic
          -- g reads in [reclaim-f, reclaim-g), so we only need agreement there
          gtms-mem-agree : ∀ slot → reclaim-f ≤ slot → slot < reclaim-g →
            readLoc s₁' (OnStack (current-frame alloc₁-reclaimed) slot) ≡
            readLoc s-after-middle (OnStack (current-frame alloc₁-reclaimed) slot)
          gtms-mem-agree slot rf≤slot slot<rg =
            -- mem-preserved-for-g gives: s₁' (alloc₁-reclaimed frame) ≡ s-after-middle (alloc-after-middle frame)
            -- We need: s₁' (alloc₁-reclaimed frame) ≡ s-after-middle (alloc₁-reclaimed frame)
            -- frame-eq-g : alloc₁-reclaimed frame ≡ alloc-after-middle frame
            -- So subst with sym frame-eq-g converts alloc-after-middle to alloc₁-reclaimed
            subst (λ f → readLoc s₁' (OnStack (current-frame alloc₁-reclaimed) slot) ≡
                        readLoc s-after-middle (OnStack f slot))
                  (sym frame-eq-g) (mem-preserved-for-g slot rf≤slot slot<rg)

          -- g preserves slots < reclaim-f (g writes above reclaim-f)
          gtms-g-preserves-below-rf : ∀ slot → slot < reclaim-f →
            readLoc (proj₁ (exec-trace g-trace s₁' alloc₁-reclaimed)) (OnStack frame slot) ≡
            readLoc s₁' (OnStack frame slot)
          gtms-g-preserves-below-rf slot slot<rf =
            exec-trace-preserves-slot-below g-trace s₁' alloc₁-reclaimed reclaim-f slot
              g-writes-above g-tnsi slot<rf

          gtms-g-preserves-below-rf-path2 : ∀ slot → slot < reclaim-f →
            readLoc (proj₁ (exec-trace g-trace s-after-middle alloc-after-middle)) (OnStack frame slot) ≡
            readLoc s-after-middle (OnStack frame slot)
          gtms-g-preserves-below-rf-path2 slot slot<rf =
            let preserved : readLoc (proj₁ (exec-trace g-trace s-after-middle alloc-after-middle))
                              (OnStack (current-frame alloc-after-middle) slot) ≡
                            readLoc s-after-middle (OnStack (current-frame alloc-after-middle) slot)
                preserved = exec-trace-preserves-slot-below g-trace s-after-middle alloc-after-middle reclaim-f slot
                              g-writes-above g-tnsi slot<rf
            in subst (λ f' → readLoc (proj₁ (exec-trace g-trace s-after-middle alloc-after-middle)) (OnStack f' slot) ≡
                            readLoc s-after-middle (OnStack f' slot)) frame-after-middle preserved

          -- Main case analysis
          gtms-stack-current : ∀ k → k < reclaim-g →
            OnStack frame k ≢ OnStack frame backup-slot →
            readLoc s₂ (OnStack frame k) ≡ readLoc s-after-g (OnStack frame k)
          gtms-stack-current k k<rg k≢backup with reclaim-f ≤? k
          ... | yes rf≤k =
            -- k is in write region [reclaim-f, reclaim-g)
            let mem-det-raw : readLoc (proj₁ (exec-trace g-trace s₁' alloc₁-reclaimed)) (OnStack frame k) ≡
                              readLoc (proj₁ (exec-trace g-trace s-after-middle alloc₁-reclaimed)) (OnStack frame k)
                mem-det-raw = exec-trace-mem-deterministic g-trace s₁' s-after-middle
                                alloc₁-reclaimed alloc₁-reclaimed reclaim-f reclaim-g
                                not-halted-s1' not-halted-after-middle
                                refl  -- same allocator
                                (trans rdi-eq₁ (sym input-after-middle))
                                g-reads-above g-reads-below g-writes-above g-writes-below g-tnsi
                                gtms-mem-agree
                                k rf≤k k<rg
                state-eq : proj₁ (exec-trace g-trace s-after-middle alloc₁-reclaimed) ≡ s-after-g
                state-eq = exec-trace-same-frame g-trace s-after-middle alloc₁-reclaimed alloc-after-middle frame-eq-g
                mem-det : readLoc (proj₁ (exec-trace g-trace s₁' alloc₁-reclaimed)) (OnStack frame k) ≡
                          readLoc s-after-g (OnStack frame k)
                mem-det = trans mem-det-raw (cong (λ st → readLoc st (OnStack frame k)) state-eq)
                s2-eq : readLoc s₂ (OnStack frame k) ≡
                        readLoc (proj₁ (exec-trace g-trace s₁' alloc₁-reclaimed)) (OnStack frame k)
                s2-eq = cong (λ st → readLoc st (OnStack frame k)) gtms-s2-eq
            in trans s2-eq mem-det
          ... | no rf≰k =
            -- k < reclaim-f, g preserves this slot
            let k<rf : k < reclaim-f
                k<rf = ≰⇒> rf≰k
                g-preserves-s1' : readLoc (proj₁ (exec-trace g-trace s₁' alloc₁-reclaimed)) (OnStack frame k) ≡
                                  readLoc s₁' (OnStack frame k)
                g-preserves-s1' = gtms-g-preserves-below-rf k k<rf
                g-preserves-middle : readLoc s-after-g (OnStack frame k) ≡
                                     readLoc s-after-middle (OnStack frame k)
                g-preserves-middle = gtms-g-preserves-below-rf-path2 k k<rf
                -- For k < reclaim-f, memory at s₁' and s-after-middle is same
                -- Use f-trace-mem-same which already proved this for f-trace
                -- and extend to middle-trace which doesn't write at k < reclaim-f
                s1'-middle-agree : readLoc s₁' (OnStack frame k) ≡ readLoc s-after-middle (OnStack frame k)
                s1'-middle-agree =
                  let -- s₁' has same memory as s₁ (only regs differ)
                      s1'-eq-s1 : readLoc s₁' (OnStack frame k) ≡ readLoc s₁ (OnStack frame k)
                      s1'-eq-s1 = refl
                      -- For k < reclaim-f, use f-trace-mem-same to show s₁ agrees with s-after-f
                      -- alloc₁-reclaimed has next-slot = reclaim-f, so k < reclaim-f is what we need
                      bf-k : BeforeFrontier alloc₁-reclaimed (OnStack frame k)
                      bf-k = stack-before refl k<rf
                      -- f-trace-mem-same gives: s₁ at k = s-after-f at k
                      s1-eq-saf : readLoc s₁ (OnStack frame k) ≡ readLoc s-after-f (OnStack frame k)
                      s1-eq-saf = f-trace-mem-same (OnStack frame k) bf-k k≢backup
                      -- middle-trace preserves k (middle writes at fst-slot = reclaim-g > k)
                      reclaim-f≤reclaim-g : reclaim-f ≤ reclaim-g
                      reclaim-f≤reclaim-g = IRResultAWF.reclaim-monotone result-g
                      middle-writes-above : SMP.TraceWritesAbove reclaim-g middle-trace
                      middle-writes-above = ≤-refl , tt
                      middle-tnsi : SMP.TraceNoStoreIndirect middle-trace
                      middle-tnsi = tt , tt , tt
                      k<rg : k < reclaim-g
                      k<rg = <-≤-trans k<rf reclaim-f≤reclaim-g
                      middle-preserves : readLoc s-after-middle (OnStack frame k) ≡
                                         readLoc s-after-f (OnStack frame k)
                      middle-preserves =
                        let preserved : readLoc (proj₁ (exec-trace middle-trace s-after-f alloc-after-f))
                                          (OnStack (current-frame alloc-after-f) k) ≡
                                        readLoc s-after-f (OnStack (current-frame alloc-after-f) k)
                            preserved = exec-trace-preserves-slot-below middle-trace s-after-f alloc-after-f reclaim-g k
                                          middle-writes-above middle-tnsi k<rg
                        in subst (λ f' → readLoc s-after-middle (OnStack f' k) ≡ readLoc s-after-f (OnStack f' k))
                                 frame-at-f preserved
                  in trans s1'-eq-s1 (trans s1-eq-saf (sym middle-preserves))
                s2-eq : readLoc s₂ (OnStack frame k) ≡
                        readLoc (proj₁ (exec-trace g-trace s₁' alloc₁-reclaimed)) (OnStack frame k)
                s2-eq = cong (λ st → readLoc st (OnStack frame k)) gtms-s2-eq
            in trans s2-eq (trans g-preserves-s1' (trans s1'-middle-agree (sym g-preserves-middle)))

      g-trace-mem-same (OnStack f' k) (stack-ancestor cf≺f' _) loc'≢backup loc'≢fst =
        -- f' is ancestor frame, g doesn't write there
        -- Uses exec-trace-preserves-ancestor with frame ordering ≺
        -- cf≺f' : current-frame alloc-reclaim-g ≺ f'
        -- current-frame alloc-reclaim-g = frame (definitionally), so frame ≺ f'
        let -- g-trace preserves ancestor from s₁' with alloc₁-reclaimed
            -- current-frame alloc₁-reclaimed = frame (definitionally), so cf≺f' works
            g-preserves-s1' : readLoc (proj₁ (exec-trace g-trace s₁' alloc₁-reclaimed)) (OnStack f' k) ≡
                              readLoc s₁' (OnStack f' k)
            g-preserves-s1' = exec-trace-preserves-ancestor g-trace s₁' alloc₁-reclaimed f' k cf≺f' g-tnsi
            -- g-trace preserves ancestor from s-after-middle with alloc-after-middle
            -- current-frame alloc-after-middle ≡ frame (via frame-eq-g)
            frame-eq-middle : current-frame alloc-after-middle ≡ frame
            frame-eq-middle = sym frame-eq-g  -- frame-eq-g : frame ≡ current-frame alloc-after-middle
            cf-after-middle≺f' : current-frame alloc-after-middle ≺ f'
            cf-after-middle≺f' = subst (λ f → f ≺ f') (sym frame-eq-middle) cf≺f'
            g-preserves-middle : readLoc s-after-g (OnStack f' k) ≡ readLoc s-after-middle (OnStack f' k)
            g-preserves-middle = exec-trace-preserves-ancestor g-trace s-after-middle alloc-after-middle f' k
                                   cf-after-middle≺f' g-tnsi
            -- Chain s₁' → s-after-middle through ancestors (analogous to heap case)
            -- s₁' (f' k) ≡ s₁ (f' k)
            s1'-eq-s1 : readLoc s₁' (OnStack f' k) ≡ readLoc s₁ (OnStack f' k)
            s1'-eq-s1 = refl
            -- s₁ = exec f-trace s alloc-after-backup, f-trace preserves ancestor
            -- current-frame alloc-after-backup = frame (definitionally)
            s1-eq-s : readLoc s₁ (OnStack f' k) ≡ readLoc s (OnStack f' k)
            s1-eq-s = trans (cong (λ st → readLoc st (OnStack f' k))
                                  (sym (IRResultAWF.trace-correct result-f)))
                            (exec-trace-preserves-ancestor f-trace s alloc-after-backup f' k cf≺f' f-tnsi)
            -- setup-trace preserves ancestor (current-frame alloc = frame)
            setup-preserves : readLoc s-after-setup (OnStack f' k) ≡ readLoc s (OnStack f' k)
            setup-preserves = exec-trace-preserves-ancestor setup-trace s alloc f' k cf≺f' setup-tnsi
            -- f-trace preserves ancestor from s-after-setup with alloc-after-setup
            frame-eq-setup : current-frame alloc-after-setup ≡ frame
            frame-eq-setup = exec-trace-preserves-frame setup-trace s alloc
            cf-after-setup≺f' : current-frame alloc-after-setup ≺ f'
            cf-after-setup≺f' = subst (λ f → f ≺ f') (sym frame-eq-setup) cf≺f'
            f-preserves-setup : readLoc s-after-f (OnStack f' k) ≡ readLoc s-after-setup (OnStack f' k)
            f-preserves-setup = exec-trace-preserves-ancestor f-trace s-after-setup alloc-after-setup f' k
                                  cf-after-setup≺f' f-tnsi
            -- middle-trace preserves ancestor
            frame-eq-f : current-frame alloc-after-f ≡ frame
            frame-eq-f = trans (exec-trace-preserves-frame f-trace s-after-setup alloc-after-setup)
                               frame-eq-setup
            cf-after-f≺f' : current-frame alloc-after-f ≺ f'
            cf-after-f≺f' = subst (λ f → f ≺ f') (sym frame-eq-f) cf≺f'
            middle-tnsi : SMP.TraceNoStoreIndirect middle-trace
            middle-tnsi = tt , tt , tt
            middle-preserves : readLoc s-after-middle (OnStack f' k) ≡ readLoc s-after-f (OnStack f' k)
            middle-preserves = exec-trace-preserves-ancestor middle-trace s-after-f alloc-after-f f' k
                                 cf-after-f≺f' middle-tnsi
            -- Chain: s₁' → s₁ → s ← s-after-setup ← s-after-f ← s-after-middle
            s1'-middle : readLoc s₁' (OnStack f' k) ≡ readLoc s-after-middle (OnStack f' k)
            s1'-middle = trans s1'-eq-s1 (trans s1-eq-s (trans (sym setup-preserves)
                           (trans (sym f-preserves-setup) (sym middle-preserves))))
            -- s₂ ≡ exec g-trace s₁' alloc₁-reclaimed
            s2-eq : readLoc s₂ (OnStack f' k) ≡
                    readLoc (proj₁ (exec-trace g-trace s₁' alloc₁-reclaimed)) (OnStack f' k)
            s2-eq = cong (λ st → readLoc st (OnStack f' k)) (sym (IRResultAWF.trace-correct result-g))
        in trans s2-eq (trans g-preserves-s1' (trans s1'-middle (sym g-preserves-middle)))

      g-trace-mem-same (OnHeap hl) (heap-before _) loc'≢backup loc'≢fst =
        let g-preserves-s1' : readLoc (proj₁ (exec-trace g-trace s₁' alloc₁-reclaimed)) (OnHeap hl) ≡
                              readLoc s₁' (OnHeap hl)
            g-preserves-s1' = exec-trace-preserves-heap-loc g-trace s₁' alloc₁-reclaimed hl g-tnsi
            g-preserves-middle : readLoc s-after-g (OnHeap hl) ≡
                                 readLoc s-after-middle (OnHeap hl)
            g-preserves-middle = exec-trace-preserves-heap-loc g-trace s-after-middle alloc-after-middle hl g-tnsi
            -- s₁' and s-after-middle have same heap (no heap writes in any trace)
            -- Chain: s₁' → s₁ → s ← s-after-setup ← s-after-f ← s-after-middle
            s1'-middle-heap : readLoc s₁' (OnHeap hl) ≡ readLoc s-after-middle (OnHeap hl)
            s1'-middle-heap =
              let -- s₁' has same memory as s₁
                  s1'-eq-s1 : readLoc s₁' (OnHeap hl) ≡ readLoc s₁ (OnHeap hl)
                  s1'-eq-s1 = refl
                  -- f-trace preserves heap (no store-indirect)
                  s1-eq-s : readLoc s₁ (OnHeap hl) ≡ readLoc s (OnHeap hl)
                  s1-eq-s = trans (cong (λ st → readLoc st (OnHeap hl))
                                        (sym (IRResultAWF.trace-correct result-f)))
                                  (exec-trace-preserves-heap-loc f-trace s alloc-after-backup hl f-tnsi)
                  -- setup preserves heap
                  setup-preserves : readLoc s-after-setup (OnHeap hl) ≡ readLoc s (OnHeap hl)
                  setup-preserves = exec-trace-preserves-heap-loc setup-trace s alloc hl setup-tnsi
                  -- f-trace preserves heap in path 2
                  f-preserves-heap : readLoc s-after-f (OnHeap hl) ≡ readLoc s-after-setup (OnHeap hl)
                  f-preserves-heap = exec-trace-preserves-heap-loc f-trace s-after-setup alloc-after-setup hl f-tnsi
                  -- middle preserves heap
                  middle-preserves : readLoc s-after-middle (OnHeap hl) ≡ readLoc s-after-f (OnHeap hl)
                  middle-preserves = exec-trace-preserves-heap-loc middle-trace s-after-f alloc-after-f hl (tt , tt , tt)
              in trans s1'-eq-s1 (trans s1-eq-s (trans (sym setup-preserves)
                   (trans (sym f-preserves-heap) (sym middle-preserves))))
            s2-eq : readLoc s₂ (OnHeap hl) ≡
                    readLoc (proj₁ (exec-trace g-trace s₁' alloc₁-reclaimed)) (OnHeap hl)
            s2-eq = cong (λ st → readLoc st (OnHeap hl)) (sym (IRResultAWF.trace-correct result-g))
        in trans s2-eq (trans g-preserves-s1' (trans s1'-middle-heap (sym g-preserves-middle)))

      -- Helper: BeforeFrontier at alloc-reclaim-g implies loc ≠ OnStack frame fst-slot
      -- because fst-slot = reclaim-g = next-slot, so it's NOT before frontier
      bf-implies-not-fst : ∀ (loc' : ValueLocation FS) →
        BeforeFrontier alloc-reclaim-g loc' →
        loc' ≢ OnStack frame fst-slot
      bf-implies-not-fst (OnStack f' k) (stack-before frame-eq k<reclaim-g) eq =
        let k≡fst : k ≡ fst-slot
            k≡fst = stack-slot-injective eq
        in <⇒≢ k<reclaim-g k≡fst
      bf-implies-not-fst (OnStack f' k) (stack-ancestor cf≺f' _) eq =
        -- eq : OnStack f' k ≡ OnStack frame fst-slot
        -- cf≺f' : current-frame alloc-reclaim-g ≺ f'
        -- From eq: f' ≡ frame
        -- current-frame alloc-reclaim-g = frame (by definition)
        -- So we'd have frame ≺ frame, contradiction
        let f'≡frame : f' ≡ frame
            f'≡frame = stack-frame-injective eq
            cf≡frame : current-frame alloc-reclaim-g ≡ frame
            cf≡frame = refl  -- alloc-reclaim-g has same frame as alloc
            cf≡f' : current-frame alloc-reclaim-g ≡ f'
            cf≡f' = trans cf≡frame (sym f'≡frame)
        in ≺⇒≢ cf≺f' cf≡f'
      bf-implies-not-fst (OnHeap _) (heap-before _) ()

      -- Memory at BeforeFrontier locations (except backup) is same in s₂ and s-after-g
      g-trace-mem-same-backup : ∀ (loc' : ValueLocation FS) →
        BeforeFrontier alloc-reclaim-g loc' →
        loc' ≢ OnStack frame backup-slot →
        readLoc s₂ loc' ≡ readLoc s-after-g loc'
      g-trace-mem-same-backup loc' bf loc'≢backup =
        g-trace-mem-same loc' bf loc'≢backup (bf-implies-not-fst loc' bf)

      -- Transfer validity from s₂ to s-after-g
      valid-at-s-after-g : ValidAtWF mG alloc-reclaim-g (eval primSem g x) snd-loc s-after-g
      valid-at-s-after-g =
        -- snd-loc's sub-locations don't include backup-slot or fst-slot
        -- So we can transfer validity even though memory differs at those slots
        -- Use validityWF-mem-preserved-excluding with backup-slot
        -- (fst-slot = reclaim-g is at the frontier, not before it)
        validityWF-mem-preserved-excluding alloc-reclaim-g
          (eval primSem g x) snd-loc frame backup-slot s₂ s-after-g
          snd-loc-before-reclaim-g
          g-trace-mem-same-backup
          valid-s2-reclaimed

      -- final-trace writes above reclaim-g
      final-trace-writes-above : SMP.TraceWritesAbove reclaim-g final-trace
      final-trace-writes-above = n≤1+n reclaim-g , tt  -- snd-slot = suc reclaim-g ≥ reclaim-g

      -- final-trace has no store-indirect
      final-trace-tnsi : SMP.TraceNoStoreIndirect final-trace
      final-trace-tnsi = tt , tt , tt

      -- Apply validityWF-trace-preserves for final-trace
      valid-at-s-after-final-g : ValidAtWF mG alloc-reclaim-g (eval primSem g x) snd-loc
                                   (proj₁ (exec-trace final-trace s-after-g alloc-reclaim-g))
      valid-at-s-after-final-g = validityWF-trace-preserves alloc-reclaim-g
                                   final-trace (eval primSem g x) snd-loc s-after-g
                                   snd-loc-before-reclaim-g valid-at-s-after-g
                                   final-trace-writes-above final-trace-tnsi

      -- Connect final-trace execution to s-final via state equalities
      -- s-after-final = proj₁ (exec-trace final-trace s-after-g alloc-after-g) by definition
      -- Need: proj₁ (exec-trace final-trace s-after-g alloc-reclaim-g) ≡ s-after-final
      final-trace-same-frame : proj₁ (exec-trace final-trace s-after-g alloc-reclaim-g) ≡
                               proj₁ (exec-trace final-trace s-after-g alloc-after-g)
      final-trace-same-frame = exec-trace-same-frame final-trace s-after-g alloc-reclaim-g alloc-after-g
                                 (sym (trans (exec-trace-preserves-frame g-trace s-after-middle alloc-after-middle)
                                   (trans (exec-trace-preserves-frame middle-trace s-after-f alloc-after-f)
                                     (trans (exec-trace-preserves-frame f-trace s-after-setup alloc-after-setup)
                                       (exec-trace-preserves-frame setup-trace s alloc)))))

      valid-at-s-after-final : ValidAtWF mG alloc-reclaim-g (eval primSem g x) snd-loc s-after-final
      valid-at-s-after-final = subst (λ s' → ValidAtWF mG alloc-reclaim-g (eval primSem g x) snd-loc s')
                                 final-trace-same-frame valid-at-s-after-final-g

      valid-snd-s-final : ValidAtWF mG alloc-reclaim-g (eval primSem g x) snd-loc s-final
      valid-snd-s-final = subst (λ s' → ValidAtWF mG alloc-reclaim-g (eval primSem g x) snd-loc s')
                            (sym s-final-eq) valid-at-s-after-final

      snd-valid : ValidAtWF mG alloc₃ (eval primSem g x) snd-loc s-final
      snd-valid =
        -- Advance frontier from alloc-reclaim-g to alloc₃
        validityWF-frontier-advance (eval primSem g x) snd-loc s-final
          refl
          (m≤m+n reclaim-g ps)
          ≤-refl
          valid-snd-s-final

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
