------------------------------------------------------------------------
-- Once.CCC.Target.X86v3.IR.ComposeWF
--
-- Compose IR implementation with ValidAtWF.
-- Extracted from Dispatcher.agda to minimize the mutual block.
--
-- Takes RecDispatcherWF as parameter for recursive dispatch to f and g.
--
-- Uses ir-stack-requirement for capacity accounting
------------------------------------------------------------------------

module Once.CCC.Target.X86v3.Dispatcher.IR.ComposeWF where

open import Data.Nat using (ℕ; suc; _<_; _≤_; s≤s; z≤n) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; +-monoˡ-≤; +-monoʳ-≤; +-assoc; +-comm; m+n≤o⇒m≤o; m≤m+n)
open import Data.Bool using (false)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; cong)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.SlotMachine
open import Once.CCC.Target.X86v3.Types
open import Once.CCC.IR
open import Once.CCC.Target.X86v3.Dispatcher.Allocation hiding (AllocMode)

------------------------------------------------------------------------
-- Compose implementation
------------------------------------------------------------------------

module ComposeWFImpl {FS : FrameSemantics} (program-bound : ℕ) (primSem : PrimSem) where
  open FrontierInvariant {FS}
  open MemOps {FS}
  open WriteOps {FS}
  open FrameSemantics FS

  open import Once.CCC.Target.X86v3.Dispatcher.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound primSem
    using (ValidAtWF; IRResultAWF; RecDispatcherWF; validityWF-mem-only;
           validityWF-frontier-advance; validityWF-mem-preserved)

  open import Once.CCC.Target.X86v3.Dispatcher.FrontierLemma
  open FrontierLemmas {FS}
    using (frontier-same-heap)
  open ExecLemmas {FS}


  ------------------------------------------------------------------------
  -- Compose: run f, then run g with f's output
  --
  -- Takes RecDispatcherWF as parameter instead of constructing it internally.
  -- The caller (Dispatcher.run-ir-wf) passes make-rec-wf ir<bound rs.
  --
  -- Uses ir-stack-requirement for capacity: req(g ∘ f) = req(f) + req(g)
  --
  -- Key derivation for f's capacity:
  --   slot + req(g ∘ f) ≤ capacity
  --   slot + req(f) + req(g) ≤ capacity
  --   slot + req(f) ≤ capacity (by m+n≤o⇒m≤o)
  --
  -- Key derivation for g's capacity:
  --   reclaim-f ≤ slot + req(f)
  --   reclaim-f + req(g) ≤ slot + req(f) + req(g) = slot + req(g ∘ f) ≤ capacity
  ------------------------------------------------------------------------

  run-compose : ∀ {A B C} (mIn : AllocMode) (f : IR A B) (g : IR B C)
    (rec-wf : RecDispatcherWF (ir-size (g ∘ f)))
    (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    -- Capacity using ir-stack-requirement
    next-slot alloc +ℕ ir-stack-requirement (g ∘ f) ≤ frame-capacity alloc →
    ∃[ mOut ] IRResultAWF mOut (g ∘ f) x s alloc
  run-compose mIn f g rec-wf x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap =
    let -- Stack requirement abbreviations
        rf = ir-stack-requirement f
        rg = ir-stack-requirement g
        req-compose = ir-stack-requirement (g ∘ f)  -- = rf + rg by ∘-stack-req

        ------------------------------------------------------------------------
        -- Derive capacity for f:
        -- Have: slot + req(g ∘ f) ≤ capacity
        -- Want: slot + req(f) ≤ capacity
        -- By ∘-stack-req: req(g ∘ f) = rf + rg
        -- So slot + rf + rg ≤ capacity → slot + rf ≤ capacity (by m+n≤o⇒m≤o)
        ------------------------------------------------------------------------
        combined-cap-expanded : next-slot alloc +ℕ (rf +ℕ rg) ≤ frame-capacity alloc
        combined-cap-expanded = subst (λ n → next-slot alloc +ℕ n ≤ frame-capacity alloc)
                                      (∘-stack-req f g) combined-cap

        combined-cap-f : next-slot alloc +ℕ rf ≤ frame-capacity alloc
        combined-cap-f = m+n≤o⇒m≤o (next-slot alloc +ℕ rf)
                           (subst (_≤ frame-capacity alloc) (sym (+-assoc (next-slot alloc) rf rg)) combined-cap-expanded)

        -- Run f via recursive dispatch
        -- rec-wf returns ∃[ mMid ] IRResultAWF mMid f x s alloc
        (mMid , result-f) = rec-wf mIn f (∘-f-smaller f g) x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap-f
        s₁ = IRResultAWF.final-state result-f
        alloc₁ = IRResultAWF.final-alloc result-f
        inter-loc = IRResultAWF.result-loc result-f
        inter-valid-wf = IRResultAWF.result-valid-wf result-f

        ------------------------------------------------------------------------
        -- Reclaim after f: Reset slot to reclaimable-slot
        ------------------------------------------------------------------------
        reclaim-f = IRResultAWF.reclaimable-slot result-f

        -- reclaim-f is bounded by f's stack requirement
        reclaim-f-bound : reclaim-f ≤ next-slot alloc +ℕ rf
        reclaim-f-bound = IRResultAWF.reclaim-size-bound result-f

        -- Derive that reclaim fits in capacity
        -- reclaim-f ≤ slot + rf ≤ slot + rf + rg = slot + req(g ∘ f) ≤ capacity
        reclaim-f-fits : reclaim-f ≤ frame-capacity alloc
        reclaim-f-fits = ≤-trans reclaim-f-bound
                           (≤-trans (+-monoʳ-≤ (next-slot alloc) (m≤m+n rf rg))
                             combined-cap-expanded)

        -- Create reclaimed allocation
        alloc₁-reclaimed : AllocState {FS}
        alloc₁-reclaimed = record alloc
          { next-slot = reclaim-f
          ; slots-available = reclaim-f-fits
          }

        ------------------------------------------------------------------------
        -- Derive capacity for g (using reclaim-f-bound)
        -- reclaim-f + rg ≤ slot + rf + rg = slot + req(g ∘ f) ≤ capacity
        ------------------------------------------------------------------------
        combined-cap-g : reclaim-f +ℕ rg ≤ frame-capacity alloc
        combined-cap-g = ≤-trans (+-monoˡ-≤ rg reclaim-f-bound)
                           (subst (_≤ frame-capacity alloc) (sym (+-assoc (next-slot alloc) rf rg)) combined-cap-expanded)

        -- Run g via recursive dispatch WITH RECLAIMED ALLOCATION
        inter-before = IRResultAWF.result-before result-f
        not-halted₁ = IRResultAWF.not-halted result-f

        inter-before-reclaimed : BeforeFrontier alloc₁-reclaimed inter-loc
        inter-before-reclaimed = IRResultAWF.reclaim-preserves-result result-f reclaim-f-fits

        -- Use reclaim-preserves-validity for validity at reclaimed allocation
        inter-valid-reclaimed : ValidAtWF mMid alloc₁-reclaimed (eval primSem f x) inter-loc s₁
        inter-valid-reclaimed = IRResultAWF.reclaim-preserves-validity result-f reclaim-f-fits

        -- Set up RDI for g's input
        s₁' = record s₁ { regs = writeReg (regs s₁) RDI inter-loc }
        rdi-eq₁ : readReg (regs s₁') RDI ≡ inter-loc
        rdi-eq₁ = writeReg-same (regs s₁) RDI inter-loc

        inter-valid-wf' : ValidAtWF mMid alloc₁-reclaimed (eval primSem f x) inter-loc s₁'
        inter-valid-wf' = validityWF-mem-only (eval primSem f x) inter-loc s₁ s₁' refl refl inter-valid-reclaimed

        -- Run g via recursive dispatch WITH RECLAIMED ALLOCATION
        (mOut , result-g) = rec-wf mMid g (∘-g-smaller f g) (eval primSem f x) inter-loc s₁' alloc₁-reclaimed inter-valid-wf' inter-before-reclaimed not-halted₁ rdi-eq₁ combined-cap-g

        -- Final state and alloc
        s₂ = IRResultAWF.final-state result-g
        alloc₂ = IRResultAWF.final-alloc result-g

        ------------------------------------------------------------------------
        -- Memory preservation for locations before initial frontier
        ------------------------------------------------------------------------
        mem-preserved-compose : ∀ loc → BeforeFrontier alloc loc →
          readLoc s₂ loc ≡ readLoc s loc
        mem-preserved-compose loc bf =
          let bf-reclaimed : BeforeFrontier alloc₁-reclaimed loc
              bf-reclaimed = frontier-monotone alloc alloc₁-reclaimed
                               refl
                               (IRResultAWF.reclaim-monotone result-f)
                               ≤-refl
                               loc bf
              step-g = IRResultAWF.mem-preserved-before result-g loc bf-reclaimed
              step-reg = readLoc-stackMem-eq s₁' s₁ loc refl refl
              step-f = IRResultAWF.mem-preserved-before result-f loc bf
          in trans step-g (trans step-reg step-f)

        ------------------------------------------------------------------------
        -- Reclamation: Use g's reclaimable-slot as the compose reclaim point
        --
        -- Chain:
        --   reclaim-g ≤ reclaim-f + rg  (from g's reclaim-size-bound)
        --   reclaim-f ≤ slot + rf       (from f's reclaim-size-bound)
        --   reclaim-g ≤ slot + rf + rg = slot + req(g ∘ f)
        ------------------------------------------------------------------------
        reclaim-g = IRResultAWF.reclaimable-slot result-g
        compose-reclaim = reclaim-g

        compose-reclaim-monotone : next-slot alloc ≤ compose-reclaim
        compose-reclaim-monotone = ≤-trans (IRResultAWF.reclaim-monotone result-f)
                                           (IRResultAWF.reclaim-monotone result-g)

        compose-reclaim-bounded : compose-reclaim ≤ next-slot alloc₂
        compose-reclaim-bounded = IRResultAWF.reclaim-bounded result-g

        compose-reclaim-preserves-result : ∀ (fits : compose-reclaim ≤ frame-capacity alloc) →
          BeforeFrontier (record alloc { next-slot = compose-reclaim ; slots-available = fits })
                         (IRResultAWF.result-loc result-g)
        compose-reclaim-preserves-result fits =
          let fits-reclaimed : reclaim-g ≤ frame-capacity alloc
              fits-reclaimed = fits
              g-preserves = IRResultAWF.reclaim-preserves-result result-g fits-reclaimed
          in frontier-same-heap
               (record alloc { next-slot = reclaim-g ; slots-available = fits-reclaimed })
               (record alloc { next-slot = compose-reclaim ; slots-available = fits })
               refl refl refl
               (IRResultAWF.result-loc result-g)
               g-preserves

        compose-reclaim-preserves-validity : ∀ (fits : compose-reclaim ≤ frame-capacity alloc) →
          ValidAtWF mOut (record alloc { next-slot = compose-reclaim ; slots-available = fits })
                    (eval primSem(g ∘ f) x) (IRResultAWF.result-loc result-g) s₂
        compose-reclaim-preserves-validity fits = IRResultAWF.reclaim-preserves-validity result-g fits

        -- reclaim-size-bound: compose-reclaim ≤ slot + req(g ∘ f)
        reclaim-g-bound : reclaim-g ≤ reclaim-f +ℕ rg
        reclaim-g-bound = IRResultAWF.reclaim-size-bound result-g

        compose-reclaim-size-bound : compose-reclaim ≤ next-slot alloc +ℕ req-compose
        compose-reclaim-size-bound = ≤-trans reclaim-g-bound
                                       (subst (reclaim-f +ℕ rg ≤_)
                                         (trans (cong (next-slot alloc +ℕ_) (sym (∘-stack-req f g)))
                                                refl)
                                         (≤-trans (+-monoˡ-≤ rg reclaim-f-bound)
                                           (≤-reflexive (+-assoc (next-slot alloc) rf rg))))

    in mOut , record
      { result-loc = IRResultAWF.result-loc result-g
      ; final-state = s₂
      ; final-alloc = alloc₂
      ; result-valid-wf = IRResultAWF.result-valid-wf result-g
      ; result-before = IRResultAWF.result-before result-g
      ; rax-is-result = IRResultAWF.rax-is-result result-g
      ; not-halted = IRResultAWF.not-halted result-g
      ; frame-preserved = IRResultAWF.frame-preserved result-g
      ; slot-monotone = ≤-trans (IRResultAWF.reclaim-monotone result-f)
                                (IRResultAWF.slot-monotone result-g)
      ; heap-monotone = IRResultAWF.heap-monotone result-g
      ; heap-preserved = IRResultAWF.heap-preserved result-g
      ; capacity-preserved = IRResultAWF.capacity-preserved result-g
      ; mem-preserved-before = mem-preserved-compose
      ; reclaimable-slot = compose-reclaim
      ; reclaim-monotone = compose-reclaim-monotone
      ; reclaim-bounded = compose-reclaim-bounded
      ; reclaim-preserves-result = compose-reclaim-preserves-result
      ; reclaim-preserves-validity = compose-reclaim-preserves-validity
      ; reclaim-size-bound = compose-reclaim-size-bound
      }
