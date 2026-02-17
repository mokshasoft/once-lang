------------------------------------------------------------------------
-- Once.Backend.X86v3.IR.ComposeWF
--
-- Compose IR implementation with ValidAtWF.
-- Extracted from Dispatcher.agda to minimize the mutual block.
--
-- Takes RecDispatcherWF as parameter for recursive dispatch to f and g.
--
-- Uses LINEAR capacity formula: pair-slots * ir-size
------------------------------------------------------------------------

module Once.Backend.X86v3.IR.ComposeWF where

open import Data.Nat using (ℕ; suc; _<_; _+_; _≤_; s≤s; z≤n) renaming (_*_ to _*ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; +-monoˡ-≤; +-monoʳ-≤; +-assoc; +-comm; m+n≤o⇒m≤o; *-monoʳ-≤; m≤m+n; m≤n+m; *-distribˡ-+; *-suc; n≤1+n)
open import Data.Bool using (false)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; cong)

open import Once.Backend.Common.FrameSemantics using (FrameSemantics)
open import Once.Backend.Common.SlotMachine
open import Once.Backend.X86v3.Types
open import Once.Backend.X86v3.IR
open import Once.Backend.X86v3.Allocation

------------------------------------------------------------------------
-- Compose implementation
------------------------------------------------------------------------

module ComposeWFImpl {FS : FrameSemantics} (program-bound : ℕ) where
  open import Once.Backend.X86v3.Validity
  open ValidityDef {FS} program-bound
  open FrontierInvariant {FS}
  open MemOps {FS}
  open WriteOps {FS}
  open FrameSemantics FS

  -- Import IRResultAWF and ValidAtWF
  open import Once.Backend.X86v3.IRResult
  open DispatcherResult {FS} program-bound

  open import Once.Backend.X86v3.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound
    using (ValidAtWF; IRResultAWF; RecDispatcherWF; validityWF-mem-only;
           validityWF-frontier-advance; validityWF-mem-preserved)

  -- NOTE: Global capacity invariants removed - using dynamic capacity threading instead

  -- Import arithmetic lemmas
  open import Once.Backend.X86v3.DispatcherArithmeticLemma
    using (compose-f-cap; compose-g-cap)
  open import Once.Backend.X86v3.FrontierLemma
  open FrontierLemmas {FS}
    using (frontier-same-heap)
  open ExecLemmas {FS}


  ------------------------------------------------------------------------
  -- Compose: run f, then run g with f's output
  --
  -- Takes RecDispatcherWF as parameter instead of constructing it internally.
  -- The caller (Dispatcher.run-ir-wf) passes make-rec-wf ir<bound rs.
  --
  -- Uses LINEAR capacity: pair-slots * ir-size covers ir-req + recursion
  --
  -- Key derivation for f's capacity:
  --   slot + pair-slots * sf ≤ slot + pair-slots * size (since sf < size)
  --
  -- Key derivation for g's capacity:
  --   slot₁ ≤ slot + pair-slots * sf (by slot-bounded + ir-stack-req-bounded)
  --   slot₁ + pair-slots * sg ≤ slot + pair-slots * (sf + sg) ≤ slot + pair-slots * size
  ------------------------------------------------------------------------

  run-compose : ∀ {A B C} (f : IR A B) (g : IR B C)
    (rec-wf : RecDispatcherWF (ir-size (g ∘ f)))
    (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    -- LINEAR capacity: pair-slots * size covers ir-req + recursion
    -- This is the ONLY capacity constraint needed (no global invariants)
    next-slot alloc + pair-slots *ℕ ir-size (g ∘ f) ≤ frame-capacity alloc →
    IRResultAWF (g ∘ f) x s alloc
  run-compose f g rec-wf x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap =
    let -- Size abbreviations
        sf = ir-size f
        sg = ir-size g
        size = ir-size (g ∘ f)  -- = suc (sg + sf)

        ------------------------------------------------------------------------
        -- Derive capacity for f:
        -- Need: slot + pair-slots * sf ≤ capacity
        -- Have: slot + pair-slots * size ≤ capacity (combined-cap)
        -- size = suc (sg + sf), and sf ≤ suc (sf + sg) = suc (sg + sf) by +-comm
        ------------------------------------------------------------------------
        sf+sg≡sg+sf : suc (sf + sg) ≡ suc (sg + sf)
        sf+sg≡sg+sf = cong suc (+-comm sf sg)

        -- Use compose-f-cap lemma (with sf+sg ordering, then convert to sg+sf = size)
        combined-cap-converted : next-slot alloc + pair-slots *ℕ suc (sf + sg) ≤ frame-capacity alloc
        combined-cap-converted = subst (λ n → next-slot alloc + pair-slots *ℕ n ≤ frame-capacity alloc)
                                       (sym sf+sg≡sg+sf) combined-cap

        combined-cap-f : next-slot alloc + pair-slots *ℕ sf ≤ frame-capacity alloc
        combined-cap-f = compose-f-cap (next-slot alloc) pair-slots sf sg (frame-capacity alloc) combined-cap-converted

        -- Run f via recursive dispatch (with linear capacity only)
        result-f = rec-wf f (∘-f-smaller f g) x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap-f
        s₁ = IRResultAWF.final-state result-f
        alloc₁ = IRResultAWF.final-alloc result-f
        inter-loc = IRResultAWF.result-loc result-f
        inter-valid-wf = IRResultAWF.result-valid-wf result-f

        ------------------------------------------------------------------------
        -- Reclaim after f: Reset slot to reclaimable-slot
        -- This is key to eliminating slot-bounded
        ------------------------------------------------------------------------
        reclaim-f = IRResultAWF.reclaimable-slot result-f

        -- reclaim-f is bounded by f's size
        reclaim-f-bound : reclaim-f ≤ next-slot alloc + pair-slots *ℕ sf
        reclaim-f-bound = IRResultAWF.reclaim-size-bound result-f

        -- capacity₁ = capacity (frame-capacity preserved)
        capacity₁-eq : frame-capacity alloc₁ ≡ frame-capacity alloc
        capacity₁-eq = IRResultAWF.capacity-preserved result-f

        -- Derive that reclaim fits in capacity for creating reclaimed alloc
        -- Chain: reclaim-f ≤ slot + ps*sf ≤ slot + ps*(sf+sg) ≤ slot + ps*suc(sf+sg) ≤ cap
        reclaim-f-fits : reclaim-f ≤ frame-capacity alloc
        reclaim-f-fits = ≤-trans reclaim-f-bound
                           (≤-trans (+-monoʳ-≤ (next-slot alloc) (*-monoʳ-≤ pair-slots (m≤m+n sf sg)))
                             (≤-trans (+-monoʳ-≤ (next-slot alloc) (*-monoʳ-≤ pair-slots (n≤1+n (sf + sg))))
                               combined-cap-converted))

        -- Create reclaimed allocation
        alloc₁-reclaimed : AllocState {FS}
        alloc₁-reclaimed = record alloc
          { next-slot = reclaim-f
          ; slots-available = reclaim-f-fits
          }

        ------------------------------------------------------------------------
        -- Derive capacity for g (using reclaim-f-bound)
        -- reclaim-f + ps*sg ≤ slot + ps*sf + ps*sg = slot + ps*(sf+sg) < slot + ps*suc(sf+sg) ≤ cap
        ------------------------------------------------------------------------
        combined-cap-g : reclaim-f + pair-slots *ℕ sg ≤ frame-capacity alloc
        combined-cap-g = compose-g-cap (next-slot alloc) reclaim-f pair-slots sf sg
                           (frame-capacity alloc) reclaim-f-bound combined-cap-converted

        -- Run g via recursive dispatch WITH RECLAIMED ALLOCATION
        -- inter-loc is BeforeFrontier in reclaimed allocation since reclaim-f ≥ next-slot alloc₁
        inter-before = IRResultAWF.result-before result-f
        not-halted₁ = IRResultAWF.not-halted result-f

        inter-before-reclaimed : BeforeFrontier alloc₁-reclaimed inter-loc
        inter-before-reclaimed = IRResultAWF.reclaim-preserves-result result-f reclaim-f-fits

        -- Use reclaim-preserves-validity directly to get validity at reclaimed allocation
        -- This handles the "backwards" direction of reclamation (slot decreases)
        inter-valid-reclaimed : ValidAtWF alloc₁-reclaimed (eval f x) inter-loc s₁
        inter-valid-reclaimed = IRResultAWF.reclaim-preserves-validity result-f reclaim-f-fits

        -- Set up RDI for g's input
        s₁' = record s₁ { regs = writeReg (regs s₁) RDI inter-loc }
        rdi-eq₁ : readReg (regs s₁') RDI ≡ inter-loc
        rdi-eq₁ = writeReg-same (regs s₁) RDI inter-loc

        inter-valid-wf' : ValidAtWF alloc₁-reclaimed (eval f x) inter-loc s₁'
        inter-valid-wf' = validityWF-mem-only (eval f x) inter-loc s₁ s₁' refl refl inter-valid-reclaimed

        result-g = rec-wf g (∘-g-smaller f g) (eval f x) inter-loc s₁' alloc₁-reclaimed inter-valid-wf' inter-before-reclaimed not-halted₁ rdi-eq₁ combined-cap-g

        -- Final state and alloc
        s₂ = IRResultAWF.final-state result-g
        alloc₂ = IRResultAWF.final-alloc result-g

        ------------------------------------------------------------------------
        -- Memory preservation for locations before initial frontier
        ------------------------------------------------------------------------
        mem-preserved-compose : ∀ loc → BeforeFrontier alloc loc →
          readLoc s₂ loc ≡ readLoc s loc
        mem-preserved-compose loc bf =
          let -- Transfer bf to alloc₁-reclaimed
              bf-reclaimed : BeforeFrontier alloc₁-reclaimed loc
              bf-reclaimed = frontier-monotone alloc alloc₁-reclaimed
                               refl  -- frame preserved
                               (IRResultAWF.reclaim-monotone result-f)  -- slot ≤ reclaim-f
                               ≤-refl  -- heap same
                               loc bf
              step-g = IRResultAWF.mem-preserved-before result-g loc bf-reclaimed
              step-reg = readLoc-stackMem-eq s₁' s₁ loc refl refl
              step-f = IRResultAWF.mem-preserved-before result-f loc bf
          in trans step-g (trans step-reg step-f)

        ------------------------------------------------------------------------
        -- Reclamation: Use g's reclaimable-slot as the compose reclaim point
        -- Since compose's result is g's result, we use g's reclaim logic
        --
        -- Chain:
        --   reclaim-g ≤ reclaim-f + pair-slots * sg  (from g's reclaim-size-bound)
        --   reclaim-f ≤ slot + pair-slots * sf       (from f's reclaim-size-bound)
        --   reclaim-g ≤ slot + pair-slots * sf + pair-slots * sg
        --            = slot + pair-slots * (sf + sg)
        --            < slot + pair-slots * suc(sg + sf)
        --            = slot + pair-slots * size
        ------------------------------------------------------------------------
        reclaim-g = IRResultAWF.reclaimable-slot result-g

        compose-reclaim = reclaim-g

        -- reclaim-g ≥ reclaim-f ≥ next-slot alloc
        compose-reclaim-monotone : next-slot alloc ≤ compose-reclaim
        compose-reclaim-monotone = ≤-trans (IRResultAWF.reclaim-monotone result-f)
                                           (IRResultAWF.reclaim-monotone result-g)

        compose-reclaim-bounded : compose-reclaim ≤ next-slot alloc₂
        compose-reclaim-bounded = IRResultAWF.reclaim-bounded result-g

        compose-reclaim-preserves-result : ∀ (fits : compose-reclaim ≤ frame-capacity alloc) →
          BeforeFrontier (record alloc { next-slot = compose-reclaim ; slots-available = fits })
                         (IRResultAWF.result-loc result-g)
        compose-reclaim-preserves-result fits =
          let -- g was called with alloc₁-reclaimed, so use its frame-capacity
              -- frame-capacity alloc₁-reclaimed = frame-capacity alloc
              fits-reclaimed : reclaim-g ≤ frame-capacity alloc
              fits-reclaimed = fits
              g-preserves = IRResultAWF.reclaim-preserves-result result-g fits-reclaimed
              -- Now transfer to alloc with compose-reclaim
          in frontier-same-heap
               (record alloc { next-slot = reclaim-g ; slots-available = fits-reclaimed })
               (record alloc { next-slot = compose-reclaim ; slots-available = fits })
               refl
               refl
               refl
               (IRResultAWF.result-loc result-g)
               g-preserves

        -- Validity at reclaimed allocation - use g's reclaim-preserves-validity
        compose-reclaim-preserves-validity : ∀ (fits : compose-reclaim ≤ frame-capacity alloc) →
          ValidAtWF (record alloc { next-slot = compose-reclaim ; slots-available = fits })
                    (eval (g ∘ f) x) (IRResultAWF.result-loc result-g) s₂
        compose-reclaim-preserves-validity fits = IRResultAWF.reclaim-preserves-validity result-g fits

        -- reclaim-size-bound: compose-reclaim ≤ slot + pair-slots * size
        -- Chain through f and g's reclaim bounds
        reclaim-g-bound : reclaim-g ≤ reclaim-f + pair-slots *ℕ sg
        reclaim-g-bound = IRResultAWF.reclaim-size-bound result-g

        -- reclaim-g ≤ slot + ps*sf + ps*sg = slot + ps*(sf+sg)
        reclaim-from-slot : compose-reclaim ≤ next-slot alloc + pair-slots *ℕ (sf + sg)
        reclaim-from-slot = ≤-trans reclaim-g-bound
                              (≤-trans (+-monoˡ-≤ (pair-slots *ℕ sg) reclaim-f-bound)
                                (≤-reflexive (trans (+-assoc (next-slot alloc) (pair-slots *ℕ sf) (pair-slots *ℕ sg))
                                                    (cong (next-slot alloc +_) (sym (*-distribˡ-+ pair-slots sf sg))))))

        -- slot + ps*(sf+sg) ≤ slot + ps*suc(sg+sf) = slot + ps*size
        -- sf+sg ≤ suc(sf+sg), then subst to suc(sg+sf) = size
        compose-reclaim-size-bound : compose-reclaim ≤ next-slot alloc + pair-slots *ℕ size
        compose-reclaim-size-bound = ≤-trans reclaim-from-slot
                                       (+-monoʳ-≤ (next-slot alloc)
                                         (*-monoʳ-≤ pair-slots
                                           (subst (sf + sg ≤_) (cong suc (+-comm sf sg)) (n≤1+n (sf + sg)))))

    in record
      { result-loc = IRResultAWF.result-loc result-g
      ; final-state = s₂
      ; final-alloc = alloc₂
      ; result-valid-wf = IRResultAWF.result-valid-wf result-g
      ; result-before = IRResultAWF.result-before result-g
      ; rax-is-result = IRResultAWF.rax-is-result result-g
      ; not-halted = IRResultAWF.not-halted result-g
      -- g was run with alloc₁-reclaimed, which has current-frame = alloc.current-frame definitionally
      ; frame-preserved = IRResultAWF.frame-preserved result-g
      -- g was run with alloc₁-reclaimed, so chain through reclaim-monotone
      ; slot-monotone = ≤-trans (IRResultAWF.reclaim-monotone result-f)
                                (IRResultAWF.slot-monotone result-g)
      -- g was run with alloc₁-reclaimed which has same heap/capacity as alloc
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
