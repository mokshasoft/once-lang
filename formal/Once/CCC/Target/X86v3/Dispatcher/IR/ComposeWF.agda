------------------------------------------------------------------------
-- Once.CCC.Target.X86v3.IR.ComposeWF
--
-- Compose IR implementation with clean trace-based structure.
-- Final state defined by exec-trace, making trace-correct = refl.
------------------------------------------------------------------------

module Once.CCC.Target.X86v3.Dispatcher.IR.ComposeWF where

open import Data.Nat using (ℕ; suc; _<_; _≤_; s≤s; z≤n) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; +-monoˡ-≤; +-monoʳ-≤; +-assoc; +-comm; m+n≤o⇒m≤o; m≤m+n)
open import Data.Bool using (false)
open import Data.Unit using (tt)
open import Data.Maybe using (just)
open import Data.List using ([]; _∷_; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; cong; cong₂)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.SMCore hiding (AllocMode; Stack; Heap)
open import Once.CCC.Target.X86v3.Types
open import Once.CCC.IR
open import Once.CCC.Eval using (PrimSem; eval)
open import Once.CCC.IR.Size
open import Once.CCC.IR.Stack
open import Once.CCC.Target.X86v3.Dispatcher.Allocation hiding (AllocMode)

-- Import SMPrimitives for memory reasoning
import Once.CCC.SMPrimitives as SMP

------------------------------------------------------------------------
-- Compose implementation
------------------------------------------------------------------------

module ComposeWFImpl {FS : FrameSemantics} (program-bound : ℕ) (primSem : PrimSem) where
  open FrontierInvariant {FS}
  open MemOps {FS}
  open WriteOps {FS}
  open AbstractExec {FS}
  open TraceComposition {FS}
  open FrameSemantics FS

  -- Open SMPrimitives modules
  open SMP.MemoryOps {FS}
  open SMP.InstrPrimitives {FS}
  open SMP.TracePrimitives {FS}
  open SMP.TraceComposition {FS}

  open import Once.CCC.Target.X86v3.Dispatcher.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound primSem
    using (ValidAtWF; IRResultAWF; RecDispatcherWF; validityWF-mem-only;
           validityWF-frontier-advance; validityWF-mem-preserved)

  open import Once.CCC.Target.X86v3.Dispatcher.FrontierLemma
  open FrontierLemmas {FS}
    using (frontier-same-heap)
  open ExecLemmas {FS}

  ------------------------------------------------------------------------
  -- Proof obligations for compose trace reasoning
  ------------------------------------------------------------------------

  -- Compose trace produces same state as sequential f; mov; g execution
  exec-trace-compose-eq : ∀ (f-trace g-trace : AbstractTrace)
    (s : LocState FS) (alloc : AllocState {FS})
    (s₁ : LocState FS)
    (s₁' : LocState FS) (alloc-g : AllocState {FS})
    (s₂ : LocState FS) →
    -- f produces s₁
    proj₁ (exec-trace f-trace s alloc) ≡ s₁ →
    halted s₁ ≡ false →
    -- s₁' is s₁ with Input := Output
    s₁' ≡ record s₁ { regs = writeReg (regs s₁) Input (readReg (regs s₁) Output) } →
    -- g produces s₂ from s₁' (alloc-g has same current-frame as alloc)
    current-frame alloc-g ≡ current-frame alloc →
    proj₁ (exec-trace g-trace s₁' alloc-g) ≡ s₂ →
    -- Composed trace produces s₂
    proj₁ (exec-trace (f-trace ++ mov-to-input ∷ g-trace) s alloc) ≡ s₂
  exec-trace-compose-eq = SMP.!!

  -- Frontier stability for compose trace
  trustMe-compose-frontier : ∀ (slot : ℕ) (trace : AbstractTrace) (s' : LocState FS)
    (input-loc' : ValueLocation FS) (alloc' : AllocState {FS}) →
    readLoc s' (OnStack (current-frame alloc') slot) ≡ just input-loc' →
    readLoc (proj₁ (exec-trace trace s' alloc'))
            (OnStack (current-frame alloc') slot) ≡ just input-loc'
  trustMe-compose-frontier = SMP.!!

  ------------------------------------------------------------------------
  -- Compose: run f, then run g with f's output
  --
  -- Uses ir-stack-requirement for capacity: req(g ∘ f) = req(f) + req(g)
  ------------------------------------------------------------------------

  run-compose : ∀ {A B C} (mIn : AllocMode) (f : IR A B) (g : IR B C)
    (rec-wf : RecDispatcherWF (ir-size (g ∘ f)))
    (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input ≡ input-loc →
    next-slot alloc +ℕ ir-stack-requirement (g ∘ f) ≤ frame-capacity alloc →
    ∃[ mOut ] IRResultAWF mOut (g ∘ f) x s alloc
  run-compose mIn f g rec-wf x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap =
    mOut , record
      { result-loc = result-loc-g
      ; final-state = s-final
      ; final-alloc = alloc₂
      ; trace = compose-trace
      ; trace-correct = refl  -- s-final DEFINED by trace
      ; result-valid-wf = result-valid-final
      ; result-before = result-before-g
      ; rax-is-result = rax-eq-final
      ; not-halted = not-halted-final
      ; frame-preserved = IRResultAWF.frame-preserved result-g
      ; slot-monotone = slot-mono
      ; heap-monotone = heap-mono
      ; heap-preserved = IRResultAWF.heap-preserved result-g
      ; capacity-preserved = IRResultAWF.capacity-preserved result-g
      ; mem-preserved-before = mem-preserved-compose
      ; reclaimable-slot = compose-reclaim
      ; reclaim-monotone = compose-reclaim-monotone
      ; reclaim-bounded = compose-reclaim-bounded
      ; reclaim-preserves-result = compose-reclaim-preserves-result
      ; reclaim-preserves-validity = compose-reclaim-preserves-validity
      ; reclaim-size-bound = compose-reclaim-size-bound
      ; frontier-slot-stable = compose-frontier-stable
      ; trace-writes-above = compose-trace-writes-above
      ; trace-slot-reads-above = compose-trace-slot-reads-above
      ; trace-writes-below = compose-trace-writes-below
      ; trace-slot-reads-below = compose-trace-slot-reads-below
      ; trace-preserves-capacity = compose-trace-preserves-capacity
      ; trace-no-heap-writes = compose-trace-no-heap-writes
      ; trace-preserves-halted = compose-trace-preserves-halted
      }
    where
      -- Stack requirement abbreviations
      rf = ir-stack-requirement f
      rg = ir-stack-requirement g
      req-compose = ir-stack-requirement (g ∘ f)

      ------------------------------------------------------------------------
      -- Capacity derivations
      ------------------------------------------------------------------------
      combined-cap-expanded : next-slot alloc +ℕ (rf +ℕ rg) ≤ frame-capacity alloc
      combined-cap-expanded = subst (λ n → next-slot alloc +ℕ n ≤ frame-capacity alloc)
                                    (∘-stack-req f g) combined-cap

      combined-cap-f : next-slot alloc +ℕ rf ≤ frame-capacity alloc
      combined-cap-f = m+n≤o⇒m≤o (next-slot alloc +ℕ rf)
                         (subst (_≤ frame-capacity alloc) (sym (+-assoc (next-slot alloc) rf rg)) combined-cap-expanded)

      ------------------------------------------------------------------------
      -- Run f via recursive dispatch
      ------------------------------------------------------------------------
      f-result-pair = rec-wf mIn f (∘-f-smaller f g) x input-loc s alloc
                        input-valid-wf input-before not-halted rdi-eq combined-cap-f
      mMid = proj₁ f-result-pair
      result-f = proj₂ f-result-pair
      s₁ = IRResultAWF.final-state result-f
      alloc₁ = IRResultAWF.final-alloc result-f
      inter-loc = IRResultAWF.result-loc result-f
      f-trace = IRResultAWF.trace result-f
      not-halted₁ = IRResultAWF.not-halted result-f

      ------------------------------------------------------------------------
      -- Reclaim after f
      ------------------------------------------------------------------------
      reclaim-f = IRResultAWF.reclaimable-slot result-f

      reclaim-f-bound : reclaim-f ≤ next-slot alloc +ℕ rf
      reclaim-f-bound = IRResultAWF.reclaim-size-bound result-f

      reclaim-f-fits : reclaim-f ≤ frame-capacity alloc
      reclaim-f-fits = ≤-trans reclaim-f-bound
                         (≤-trans (+-monoʳ-≤ (next-slot alloc) (m≤m+n rf rg))
                           combined-cap-expanded)

      alloc₁-reclaimed : AllocState {FS}
      alloc₁-reclaimed = record alloc { next-slot = reclaim-f }

      ------------------------------------------------------------------------
      -- Capacity for g
      ------------------------------------------------------------------------
      combined-cap-g : reclaim-f +ℕ rg ≤ frame-capacity alloc
      combined-cap-g = ≤-trans (+-monoˡ-≤ rg reclaim-f-bound)
                         (subst (_≤ frame-capacity alloc) (sym (+-assoc (next-slot alloc) rf rg)) combined-cap-expanded)

      ------------------------------------------------------------------------
      -- Setup intermediate state for g
      ------------------------------------------------------------------------
      inter-before-reclaimed : BeforeFrontier alloc₁-reclaimed inter-loc
      inter-before-reclaimed = IRResultAWF.reclaim-preserves-result result-f reclaim-f-fits

      inter-valid-reclaimed : ValidAtWF mMid alloc₁-reclaimed (eval primSem f x) inter-loc s₁
      inter-valid-reclaimed = IRResultAWF.reclaim-preserves-validity result-f reclaim-f-fits

      s₁' = record s₁ { regs = writeReg (regs s₁) Input inter-loc }

      rdi-eq₁ : readReg (regs s₁') Input ≡ inter-loc
      rdi-eq₁ = writeReg-same (regs s₁) Input inter-loc

      inter-valid-wf' : ValidAtWF mMid alloc₁-reclaimed (eval primSem f x) inter-loc s₁'
      inter-valid-wf' = validityWF-mem-only (eval primSem f x) inter-loc s₁ s₁' refl refl inter-valid-reclaimed

      ------------------------------------------------------------------------
      -- Run g via recursive dispatch
      ------------------------------------------------------------------------
      g-result-pair = rec-wf mMid g (∘-g-smaller f g) (eval primSem f x) inter-loc s₁' alloc₁-reclaimed
                        inter-valid-wf' inter-before-reclaimed not-halted₁ rdi-eq₁ combined-cap-g
      mOut = proj₁ g-result-pair
      result-g = proj₂ g-result-pair
      s₂ = IRResultAWF.final-state result-g
      alloc₂ = IRResultAWF.final-alloc result-g
      result-loc-g = IRResultAWF.result-loc result-g
      g-trace = IRResultAWF.trace result-g
      result-before-g = IRResultAWF.result-before result-g

      ------------------------------------------------------------------------
      -- Compose trace and final state DEFINED by trace execution
      ------------------------------------------------------------------------
      compose-trace : AbstractTrace
      compose-trace = f-trace ++ mov-to-input ∷ g-trace

      s-final : LocState FS
      s-final = proj₁ (exec-trace compose-trace s alloc)

      -- Prove s-final ≡ s₂ using the compose equation
      -- s₁' = record s₁ { regs = writeReg (regs s₁) Input inter-loc }
      -- By rax-is-result: readReg (regs s₁) Output ≡ inter-loc
      -- So s₁' ≡ record s₁ { regs = writeReg (regs s₁) Input (readReg (regs s₁) Output) }
      s₁'-eq-output : s₁' ≡ record s₁ { regs = writeReg (regs s₁) Input (readReg (regs s₁) Output) }
      s₁'-eq-output = cong (λ v → record s₁ { regs = writeReg (regs s₁) Input v })
                           (sym (IRResultAWF.rax-is-result result-f))

      s-final-eq : s-final ≡ s₂
      s-final-eq = exec-trace-compose-eq f-trace g-trace s alloc s₁ s₁' alloc₁-reclaimed s₂
                     (IRResultAWF.trace-correct result-f)
                     not-halted₁
                     s₁'-eq-output
                     refl
                     (IRResultAWF.trace-correct result-g)

      ------------------------------------------------------------------------
      -- Transport proofs from s₂ to s-final
      ------------------------------------------------------------------------
      result-valid-final : ValidAtWF mOut alloc₂ (eval primSem (g ∘ f) x) result-loc-g s-final
      result-valid-final = subst (λ st → ValidAtWF mOut alloc₂ (eval primSem (g ∘ f) x) result-loc-g st)
                             (sym s-final-eq) (IRResultAWF.result-valid-wf result-g)

      rax-eq-final : readReg (regs s-final) Output ≡ result-loc-g
      rax-eq-final = trans (cong (λ st → readReg (regs st) Output) s-final-eq)
                           (IRResultAWF.rax-is-result result-g)

      not-halted-final : halted s-final ≡ false
      not-halted-final = subst (λ st → halted st ≡ false) (sym s-final-eq)
                           (IRResultAWF.not-halted result-g)

      slot-mono : next-slot alloc ≤ next-slot alloc₂
      slot-mono = ≤-trans (IRResultAWF.reclaim-monotone result-f)
                          (IRResultAWF.slot-monotone result-g)

      heap-mono : next-heap-ref alloc ≤ next-heap-ref alloc₂
      heap-mono = IRResultAWF.heap-monotone result-g

      ------------------------------------------------------------------------
      -- Memory preservation
      ------------------------------------------------------------------------
      mem-preserved-compose : ∀ loc → BeforeFrontier alloc loc → readLoc s-final loc ≡ readLoc s loc
      mem-preserved-compose loc bf =
        let bf-reclaimed : BeforeFrontier alloc₁-reclaimed loc
            bf-reclaimed = frontier-monotone alloc alloc₁-reclaimed refl
                             (IRResultAWF.reclaim-monotone result-f) ≤-refl loc bf
            step-g = IRResultAWF.mem-preserved-before result-g loc bf-reclaimed
            step-reg = readLoc-stackMem-eq s₁' s₁ loc refl refl
            step-f = IRResultAWF.mem-preserved-before result-f loc bf
        in trans (cong (λ st → readLoc st loc) s-final-eq)
                 (trans step-g (trans step-reg step-f))

      ------------------------------------------------------------------------
      -- Reclamation
      ------------------------------------------------------------------------
      reclaim-g = IRResultAWF.reclaimable-slot result-g
      compose-reclaim = reclaim-g

      compose-reclaim-monotone : next-slot alloc ≤ compose-reclaim
      compose-reclaim-monotone = ≤-trans (IRResultAWF.reclaim-monotone result-f)
                                         (IRResultAWF.reclaim-monotone result-g)

      compose-reclaim-bounded : compose-reclaim ≤ next-slot alloc₂
      compose-reclaim-bounded = IRResultAWF.reclaim-bounded result-g

      compose-reclaim-preserves-result : ∀ (fits : compose-reclaim ≤ frame-capacity alloc) →
        BeforeFrontier (record alloc { next-slot = compose-reclaim }) result-loc-g
      compose-reclaim-preserves-result fits =
        frontier-same-heap
          (record alloc { next-slot = reclaim-g })
          (record alloc { next-slot = compose-reclaim })
          refl refl refl result-loc-g
          (IRResultAWF.reclaim-preserves-result result-g fits)

      compose-reclaim-preserves-validity : ∀ (fits : compose-reclaim ≤ frame-capacity alloc) →
        ValidAtWF mOut (record alloc { next-slot = compose-reclaim })
                  (eval primSem (g ∘ f) x) result-loc-g s-final
      compose-reclaim-preserves-validity fits =
        subst (λ st → ValidAtWF mOut (record alloc { next-slot = compose-reclaim })
                        (eval primSem (g ∘ f) x) result-loc-g st)
              (sym s-final-eq)
              (IRResultAWF.reclaim-preserves-validity result-g fits)

      reclaim-g-bound : reclaim-g ≤ reclaim-f +ℕ rg
      reclaim-g-bound = IRResultAWF.reclaim-size-bound result-g

      compose-reclaim-size-bound : compose-reclaim ≤ next-slot alloc +ℕ req-compose
      compose-reclaim-size-bound = ≤-trans reclaim-g-bound
                                     (subst (reclaim-f +ℕ rg ≤_)
                                       (trans (cong (next-slot alloc +ℕ_) (sym (∘-stack-req f g))) refl)
                                       (≤-trans (+-monoˡ-≤ rg reclaim-f-bound)
                                         (≤-reflexive (+-assoc (next-slot alloc) rf rg))))

      ------------------------------------------------------------------------
      -- Trace predicates
      ------------------------------------------------------------------------
      f-tpc : TracePreservesCapacity f-trace
      f-tpc = IRResultAWF.trace-preserves-capacity result-f
      g-tpc : TracePreservesCapacity g-trace
      g-tpc = IRResultAWF.trace-preserves-capacity result-g
      compose-trace-preserves-capacity : TracePreservesCapacity compose-trace
      compose-trace-preserves-capacity = tpc-++ f-tpc (tpc-∷ ipc-mov-to-input g-tpc)

      f-nhw : SMP.TraceNoHeapWrites f-trace
      f-nhw = IRResultAWF.trace-no-heap-writes result-f
      g-nhw : SMP.TraceNoHeapWrites g-trace
      g-nhw = IRResultAWF.trace-no-heap-writes result-g
      compose-trace-no-heap-writes : SMP.TraceNoHeapWrites compose-trace
      compose-trace-no-heap-writes =
        SMP.trace-no-heap-writes-append f-trace (mov-to-input ∷ g-trace) f-nhw g-nhw

      f-tph : TracePreservesHaltedP f-trace
      f-tph = IRResultAWF.trace-preserves-halted result-f
      g-tph : TracePreservesHaltedP g-trace
      g-tph = IRResultAWF.trace-preserves-halted result-g
      compose-trace-preserves-halted : TracePreservesHaltedP compose-trace
      compose-trace-preserves-halted = tph-++ f-tph (tph-∷ iph-mov-to-input g-tph)

      ------------------------------------------------------------------------
      -- Frontier slot stability
      ------------------------------------------------------------------------
      compose-frontier-stable : ∀ (s' : LocState FS) (input-loc' : ValueLocation FS) →
        halted s' ≡ false →
        readReg (regs s') Input ≡ input-loc' →
        readLoc s' (OnStack (current-frame alloc) (next-slot alloc)) ≡ just input-loc' →
        readLoc (proj₁ (exec-trace compose-trace s' alloc))
                (OnStack (current-frame alloc) (next-slot alloc)) ≡ just input-loc'
      compose-frontier-stable s' input-loc' _ _ slot-eq' =
        trustMe-compose-frontier (next-slot alloc) compose-trace s' input-loc' alloc slot-eq'

      ------------------------------------------------------------------------
      -- Trace write/read bounds
      ------------------------------------------------------------------------
      compose-trace-writes-above : TraceWritesAbove (next-slot alloc) compose-trace
      compose-trace-writes-above =
        let n = next-slot alloc
            f-tw : TraceWritesAbove n f-trace
            f-tw = IRResultAWF.trace-writes-above result-f
            g-tw-at-reclaim : TraceWritesAbove reclaim-f g-trace
            g-tw-at-reclaim = IRResultAWF.trace-writes-above result-g
            g-tw : TraceWritesAbove n g-trace
            g-tw = trace-writes-above-mono n reclaim-f g-trace
                     (IRResultAWF.reclaim-monotone result-f) g-tw-at-reclaim
            mov-g-tw : TraceWritesAbove n (mov-to-input ∷ g-trace)
            mov-g-tw = g-tw
        in trace-writes-above-append n f-trace (mov-to-input ∷ g-trace) f-tw mov-g-tw

      compose-trace-slot-reads-above : TraceSlotReadsAbove (next-slot alloc) compose-trace
      compose-trace-slot-reads-above =
        let n = next-slot alloc
            f-ra : TraceSlotReadsAbove n f-trace
            f-ra = IRResultAWF.trace-slot-reads-above result-f
            g-ra-at-reclaim : TraceSlotReadsAbove reclaim-f g-trace
            g-ra-at-reclaim = IRResultAWF.trace-slot-reads-above result-g
            g-ra : TraceSlotReadsAbove n g-trace
            g-ra = trace-slot-reads-above-mono n reclaim-f g-trace
                     (IRResultAWF.reclaim-monotone result-f) g-ra-at-reclaim
            mov-g-ra : TraceSlotReadsAbove n (mov-to-input ∷ g-trace)
            mov-g-ra = g-ra
        in trace-slot-reads-above-append n f-trace (mov-to-input ∷ g-trace) f-ra mov-g-ra

      compose-trace-writes-below : TraceWritesBelow compose-reclaim compose-trace
      compose-trace-writes-below =
        let f-wb-at-reclaim-f : TraceWritesBelow reclaim-f f-trace
            f-wb-at-reclaim-f = IRResultAWF.trace-writes-below result-f
            f-wb : TraceWritesBelow reclaim-g f-trace
            f-wb = trace-writes-below-mono reclaim-f reclaim-g f-trace
                     (IRResultAWF.reclaim-monotone result-g) f-wb-at-reclaim-f
            g-wb : TraceWritesBelow reclaim-g g-trace
            g-wb = IRResultAWF.trace-writes-below result-g
            mov-g-wb : TraceWritesBelow reclaim-g (mov-to-input ∷ g-trace)
            mov-g-wb = g-wb
        in trace-writes-below-append reclaim-g f-trace (mov-to-input ∷ g-trace) f-wb mov-g-wb

      compose-trace-slot-reads-below : TraceSlotReadsBelow compose-reclaim compose-trace
      compose-trace-slot-reads-below =
        let f-rb-at-reclaim-f : TraceSlotReadsBelow reclaim-f f-trace
            f-rb-at-reclaim-f = IRResultAWF.trace-slot-reads-below result-f
            f-rb : TraceSlotReadsBelow reclaim-g f-trace
            f-rb = trace-slot-reads-below-mono reclaim-f reclaim-g f-trace
                     (IRResultAWF.reclaim-monotone result-g) f-rb-at-reclaim-f
            g-rb : TraceSlotReadsBelow reclaim-g g-trace
            g-rb = IRResultAWF.trace-slot-reads-below result-g
            mov-g-rb : TraceSlotReadsBelow reclaim-g (mov-to-input ∷ g-trace)
            mov-g-rb = g-rb
        in trace-slot-reads-below-append reclaim-g f-trace (mov-to-input ∷ g-trace) f-rb mov-g-rb
