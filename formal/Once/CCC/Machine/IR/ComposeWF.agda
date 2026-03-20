------------------------------------------------------------------------
-- Once.CCC.Target.X86-64.IR.ComposeWF
--
-- Compose IR implementation with clean trace-based structure.
-- Final state defined by exec-trace, making trace-correct = refl.
------------------------------------------------------------------------

module Once.CCC.Machine.IR.ComposeWF where

open import Data.Nat using (ℕ; suc; _<_; _≤_; s≤s; z≤n; _≟_) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; +-monoˡ-≤; +-monoʳ-≤; +-assoc; +-comm; m+n≤o⇒m≤o; m≤m+n; m≤n⇒m<n∨m≡n)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Data.Bool using (false)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (just)
open import Data.List using ([]; _∷_; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; cong; cong₂)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore hiding (AllocMode; Stack; Heap)
open import Once.CCC.Target.X86-64.Types
open import Once.CCC.IR
open import Once.CCC.Eval using (PrimSem; eval)
open import Once.CCC.IR.Size
open import Once.CCC.IR.Stack
open import Once.CCC.Machine.Allocation hiding (AllocMode)

-- Import SMPrimitives for memory reasoning
import Once.CCC.Machine.SMPrimitives as SMP

-- Import proof obligation marker
import Once.ProofObligation as PO

------------------------------------------------------------------------
-- Compose implementation
------------------------------------------------------------------------

module ComposeWFImpl {FS : FrameSemantics} (program-bound : ℕ) (primSem : PrimSem) where
  open FrontierInvariant {FS}
  open MemOps {FS}
  open WriteOps {FS}
  open AbstractExec {FS}
  open FrameSemantics FS

  -- Open SMPrimitives modules
  open SMP.MemoryOps {FS}
  open SMP.InstrPrimitives {FS}
  open SMP.TracePrimitives {FS}
  open SMP.TraceComposition {FS}

  open import Once.CCC.Machine.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound primSem
    using (ValidAtWF; IRResultAWF; RecDispatcherWF; validityWF-mem-only;
           validityWF-frontier-advance; validityWF-mem-preserved)

  open import Once.CCC.Machine.FrontierLemma
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
  -- Helper: mov-to-input execution unfolds when halted = false
  -- Match equality proof first to force s₁.halted = false unification
  private
    exec-mov-to-input : ∀ (g-trace : AbstractTrace) (s₁ : LocState FS)
      (alloc₁ : AllocState {FS}) →
      halted s₁ ≡ false →
      proj₁ (exec-trace (mov-to-input ∷ g-trace) s₁ alloc₁) ≡
      proj₁ (exec-trace g-trace
        (proj₁ (exec-abstract mov-to-input s₁ alloc₁))
        (proj₂ (exec-abstract mov-to-input s₁ alloc₁)))
    exec-mov-to-input g-trace s₁ alloc₁ refl = refl

  exec-trace-compose-eq f-trace g-trace s alloc s₁ s₁' alloc-g s₂
    f-eq halted₁ s₁'-eq frame-eq g-eq = result
    where
      alloc₁ = proj₂ (exec-trace f-trace s alloc)

      -- Step 1: Split by exec-trace-append-state
      split-eq : proj₁ (exec-trace (f-trace ++ mov-to-input ∷ g-trace) s alloc) ≡
                 proj₁ (exec-trace (mov-to-input ∷ g-trace)
                         (proj₁ (exec-trace f-trace s alloc)) alloc₁)
      split-eq = exec-trace-append-state f-trace (mov-to-input ∷ g-trace) s alloc

      -- Step 2: mov-to-input unfolds when halted s₁ = false
      mov-step : proj₁ (exec-trace (mov-to-input ∷ g-trace) s₁ alloc₁) ≡
                 proj₁ (exec-trace g-trace
                   (proj₁ (exec-abstract mov-to-input s₁ alloc₁))
                   (proj₂ (exec-abstract mov-to-input s₁ alloc₁)))
      mov-step = exec-mov-to-input g-trace s₁ alloc₁ halted₁

      -- exec-abstract mov-to-input s₁ alloc₁ produces s₁'
      mov-produces-s₁' : proj₁ (exec-abstract mov-to-input s₁ alloc₁) ≡ s₁'
      mov-produces-s₁' = sym s₁'-eq

      -- Step 3: Use frame equivalence
      frame-alloc₁ : current-frame alloc₁ ≡ current-frame alloc
      frame-alloc₁ = exec-trace-preserves-frame f-trace s alloc

      frame-match : current-frame alloc₁ ≡ current-frame alloc-g
      frame-match = trans frame-alloc₁ (sym frame-eq)

      frame-equiv : proj₁ (exec-trace g-trace s₁' alloc₁) ≡
                    proj₁ (exec-trace g-trace s₁' alloc-g)
      frame-equiv = exec-trace-same-frame g-trace s₁' alloc₁ alloc-g frame-match

      -- Combine the steps
      step2' : proj₁ (exec-trace (mov-to-input ∷ g-trace) s₁ alloc₁) ≡
               proj₁ (exec-trace g-trace s₁' alloc₁)
      step2' = trans mov-step (cong (λ st → proj₁ (exec-trace g-trace st alloc₁))
                                    mov-produces-s₁')

      final : proj₁ (exec-trace g-trace s₁' alloc₁) ≡ s₂
      final = trans frame-equiv g-eq

      result = trans split-eq
                 (trans (cong (λ st → proj₁ (exec-trace (mov-to-input ∷ g-trace) st alloc₁)) f-eq)
                        (trans step2' final))

  -- Compose frontier stability is proven inline using:
  --   1. f's frontier-slot-stable for f-trace
  --   2. mov-to-input preserves memory (exec-abstract-preserves-stack-slot = refl)
  --   3. g-trace writes at slots ≥ reclaim-f > next-slot alloc (by strict inequality)

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
      --
      -- Returns a sum type:
      --   inj₁: compose doesn't allocate (next-slot = compose-reclaim)
      --   inj₂: slot is preserved
      --
      -- Proof strategy using trace bounds directly:
      --   1. f-trace preserves slot (by f's frontier-slot-stable or trace bounds)
      --   2. mov-to-input doesn't write memory (preserves slot)
      --   3. g-trace writes at slots in [reclaim-f, reclaim-g):
      --      - Case A: next-slot alloc < reclaim-f → inj₂ (preserved by trace bounds)
      --      - Case B1: next-slot = reclaim-f < reclaim-g → inj₂ (inj₂ tt) (uncertain)
      --      - Case B2: next-slot = reclaim-f = reclaim-g → inj₁ (no allocation)
      ------------------------------------------------------------------------
      compose-frontier-stable : ∀ (s' : LocState FS) (input-loc' : ValueLocation FS) →
        halted s' ≡ false →
        readReg (regs s') Input ≡ input-loc' →
        readLoc s' (OnStack (current-frame alloc) (next-slot alloc)) ≡ just input-loc' →
        (next-slot alloc ≡ compose-reclaim) ⊎
        ((readLoc (proj₁ (exec-trace compose-trace s' alloc))
                 (OnStack (current-frame alloc) (next-slot alloc)) ≡ just input-loc') ⊎ ⊤)
      compose-frontier-stable s' input-loc' not-halted' rdi-eq' slot-eq' = result
        where
          -- Step 1: Decompose trace using exec-trace-append-state
          s-after-f = proj₁ (exec-trace f-trace s' alloc)
          alloc-after-f = proj₂ (exec-trace f-trace s' alloc)

          -- f's trace bounds for slot preservation when f doesn't allocate
          f-twa : TraceWritesAbove (next-slot alloc) f-trace
          f-twa = IRResultAWF.trace-writes-above result-f

          f-twb : TraceWritesBelow reclaim-f f-trace
          f-twb = IRResultAWF.trace-writes-below result-f

          f-tnhw : TraceNoHeapWrites f-trace
          f-tnhw = IRResultAWF.trace-no-heap-writes result-f

          -- Step 2: mov-to-input preserves memory (only modifies registers)
          not-halted-after-f : halted s-after-f ≡ false
          not-halted-after-f = exec-trace-preserves-halted f-trace s' alloc not-halted'
                                 (IRResultAWF.trace-preserves-halted result-f)

          s-after-mov = proj₁ (exec-abstract mov-to-input s-after-f alloc-after-f)
          alloc-after-mov = proj₂ (exec-abstract mov-to-input s-after-f alloc-after-f)

          -- g-trace bounds
          g-twa : TraceWritesAbove reclaim-f g-trace
          g-twa = IRResultAWF.trace-writes-above result-g

          g-twb : TraceWritesBelow reclaim-g g-trace
          g-twb = IRResultAWF.trace-writes-below result-g

          g-tnhw : TraceNoHeapWrites g-trace
          g-tnhw = IRResultAWF.trace-no-heap-writes result-g

          -- We have: next-slot alloc ≤ reclaim-f (by f's reclaim-monotone)
          reclaim-f-mono : next-slot alloc ≤ reclaim-f
          reclaim-f-mono = IRResultAWF.reclaim-monotone result-f

          -- Frame equivalence
          frame-after-mov : current-frame alloc-after-mov ≡ current-frame alloc
          frame-after-mov = trans (exec-abstract-preserves-frame mov-to-input s-after-f alloc-after-f)
                                  (exec-trace-preserves-frame f-trace s' alloc)

          frame-equiv : current-frame alloc-after-mov ≡ current-frame alloc₁-reclaimed
          frame-equiv = frame-after-mov

          -- Step 3: Case analysis based on f's frontier-slot-stable result
          -- New 3-way return: inj₁ (no-alloc) | inj₂ (inj₁ preserved) | inj₂ (inj₂ tt) (uncertain)
          result : (next-slot alloc ≡ compose-reclaim) ⊎
                   ((readLoc (proj₁ (exec-trace compose-trace s' alloc))
                            (OnStack (current-frame alloc) (next-slot alloc)) ≡ just input-loc') ⊎ ⊤)
          result with IRResultAWF.frontier-slot-stable result-f s' input-loc' not-halted' rdi-eq' slot-eq'
          -- If f is uncertain, compose is also uncertain
          ... | inj₂ (inj₂ tt) = inj₂ (inj₂ tt)
          -- If f preserves the slot
          ... | inj₂ (inj₁ f-preserved) = result-with-slot-after-f f-preserved
            where
              slot-after-f : readLoc s-after-f (OnStack (current-frame alloc) (next-slot alloc)) ≡ just input-loc'
              slot-after-f = f-preserved

              slot-after-mov : readLoc s-after-mov (OnStack (current-frame alloc) (next-slot alloc)) ≡ just input-loc'
              slot-after-mov = trans (sym (exec-abstract-preserves-stack-slot mov-to-input s-after-f alloc-after-f
                                             (current-frame alloc) (next-slot alloc) nhw-mov-to-input refl))
                                     slot-after-f

              -- Case A: f allocates, use trace bounds for g
              slot-after-g : next-slot alloc < reclaim-f →
                             readLoc (proj₁ (exec-trace g-trace s-after-mov alloc₁-reclaimed))
                                     (OnStack (current-frame alloc) (next-slot alloc)) ≡ just input-loc'
              slot-after-g slot<reclaim-f =
                let preserved = exec-trace-preserves-slot-below g-trace s-after-mov alloc₁-reclaimed
                                  reclaim-f (next-slot alloc) g-twa g-tnhw slot<reclaim-f
                in trans preserved slot-after-mov

              split1 : proj₁ (exec-trace compose-trace s' alloc) ≡
                       proj₁ (exec-trace (mov-to-input ∷ g-trace) s-after-f alloc-after-f)
              split1 = exec-trace-append-state f-trace (mov-to-input ∷ g-trace) s' alloc

              split2 : exec-trace (mov-to-input ∷ g-trace) s-after-f alloc-after-f ≡
                       exec-trace g-trace s-after-mov alloc-after-mov
              split2 = exec-trace-cons mov-to-input g-trace s-after-f alloc-after-f not-halted-after-f

              frame-g-result : proj₁ (exec-trace g-trace s-after-mov alloc-after-mov) ≡
                               proj₁ (exec-trace g-trace s-after-mov alloc₁-reclaimed)
              frame-g-result = exec-trace-same-frame g-trace s-after-mov alloc-after-mov alloc₁-reclaimed frame-equiv

              build-preserved : next-slot alloc < reclaim-f →
                                readLoc (proj₁ (exec-trace compose-trace s' alloc))
                                        (OnStack (current-frame alloc) (next-slot alloc)) ≡ just input-loc'
              build-preserved slot<reclaim-f =
                trans (cong (λ st → readLoc st (OnStack (current-frame alloc) (next-slot alloc)))
                            (trans split1 (trans (cong proj₁ split2) frame-g-result)))
                      (slot-after-g slot<reclaim-f)

              result-with-slot-after-f : readLoc s-after-f (OnStack (current-frame alloc) (next-slot alloc)) ≡ just input-loc' →
                                         (next-slot alloc ≡ compose-reclaim) ⊎
                                         ((readLoc (proj₁ (exec-trace compose-trace s' alloc))
                                                  (OnStack (current-frame alloc) (next-slot alloc)) ≡ just input-loc') ⊎ ⊤)
              result-with-slot-after-f _ with m≤n⇒m<n∨m≡n reclaim-f-mono
              -- Case A: f allocates (next-slot < reclaim-f)
              ... | inj₁ slot<reclaim-f = inj₂ (inj₁ (build-preserved slot<reclaim-f))
              -- Case B: f doesn't allocate (next-slot = reclaim-f), but f returned inj₂ (inj₁ preserved)
              -- This shouldn't happen for well-behaved IRs, but handle it anyway
              ... | inj₂ slot≡reclaim-f with m≤n⇒m<n∨m≡n (IRResultAWF.reclaim-monotone result-g)
              -- B1: g allocates - uncertain (f preserved but might be overwritten by g)
              ... | inj₁ reclaim-f<reclaim-g = inj₂ (inj₂ tt)
              -- B2: neither allocates
              ... | inj₂ reclaim-f≡reclaim-g = inj₁ (trans slot≡reclaim-f reclaim-f≡reclaim-g)

          -- If f doesn't allocate (inj₁)
          ... | inj₁ f-no-alloc = result-f-no-alloc
            where
              -- f doesn't allocate: trace writes at [next-slot, reclaim-f) = [next-slot, next-slot) = ∅
              slot-after-f : readLoc s-after-f (OnStack (current-frame alloc) (next-slot alloc)) ≡ just input-loc'
              slot-after-f =
                let m≤slot : reclaim-f ≤ next-slot alloc
                    m≤slot = ≤-reflexive (sym f-no-alloc)
                    preserved = exec-trace-preserves-slot-above f-trace s' alloc
                                  reclaim-f (next-slot alloc) f-twb f-tnhw m≤slot
                in trans preserved slot-eq'

              slot-after-mov : readLoc s-after-mov (OnStack (current-frame alloc) (next-slot alloc)) ≡ just input-loc'
              slot-after-mov = trans (sym (exec-abstract-preserves-stack-slot mov-to-input s-after-f alloc-after-f
                                             (current-frame alloc) (next-slot alloc) nhw-mov-to-input refl))
                                     slot-after-f

              -- Since f-no-alloc: next-slot = reclaim-f, case analysis on g's allocation
              result-f-no-alloc : (next-slot alloc ≡ compose-reclaim) ⊎
                                  ((readLoc (proj₁ (exec-trace compose-trace s' alloc))
                                           (OnStack (current-frame alloc) (next-slot alloc)) ≡ just input-loc') ⊎ ⊤)
              result-f-no-alloc with m≤n⇒m<n∨m≡n (IRResultAWF.reclaim-monotone result-g)
              -- Case B1: g allocates at frontier - uncertain
              -- g writes to [reclaim-f, reclaim-g) which includes next-slot = reclaim-f
              -- g writes f's result (not original input) to the slot
              ... | inj₁ reclaim-f<reclaim-g = inj₂ (inj₂ tt)
              -- Case B2: neither allocates
              ... | inj₂ reclaim-f≡reclaim-g = inj₁ (trans f-no-alloc reclaim-f≡reclaim-g)

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
