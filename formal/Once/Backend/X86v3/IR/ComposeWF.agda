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

open import Data.Nat using (ℕ; suc; _<_; _+_; _≤_) renaming (_*_ to _*ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; +-monoˡ-≤; +-monoʳ-≤; +-assoc; +-comm; m+n≤o⇒m≤o; *-monoʳ-≤; m≤m+n)
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
    using (ValidAtWF; IRResultAWF; RecDispatcherWF; validityWF-mem-only)

  -- NOTE: Global capacity invariants removed - using dynamic capacity threading instead

  -- Import arithmetic lemmas
  open import Once.Backend.X86v3.DispatcherArithmeticLemma
    using (compose-slot-bounded-lemma; compose-f-cap; compose-g-cap)
  open import Once.Backend.X86v3.FrontierLemma
  open FrontierLemmas {FS}
    using (frontier-same-heap)
  open ExecLemmas {FS}

  -- Import stack bound lemma
  open import Once.Backend.X86v3.StackBoundLemma
    using (ir-stack-req-bounded)

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
        -- Derive capacity for g:
        -- Need: slot₁ + pair-slots * sg ≤ capacity₁
        --
        -- Chain:
        --   slot₁ ≤ slot + req-f (from slot-bounded)
        --   req-f ≤ pair-slots * sf (from ir-stack-req-bounded)
        --   slot₁ ≤ slot + pair-slots * sf
        --   Use compose-g-cap lemma
        ------------------------------------------------------------------------

        -- slot₁ ≤ slot + pair-slots * sf
        slot₁-bound-step1 : next-slot alloc₁ ≤ next-slot alloc + ir-stack-requirement f
        slot₁-bound-step1 = IRResultAWF.slot-bounded result-f

        slot₁-bound-step2 : ir-stack-requirement f ≤ pair-slots *ℕ sf
        slot₁-bound-step2 = ir-stack-req-bounded f

        slot₁-bound : next-slot alloc₁ ≤ next-slot alloc + pair-slots *ℕ sf
        slot₁-bound = ≤-trans slot₁-bound-step1 (+-monoʳ-≤ (next-slot alloc) slot₁-bound-step2)

        -- capacity₁ = capacity (frame-capacity preserved)
        capacity₁-eq : frame-capacity alloc₁ ≡ frame-capacity alloc
        capacity₁-eq = IRResultAWF.capacity-preserved result-f

        combined-cap-g : next-slot alloc₁ + pair-slots *ℕ sg ≤ frame-capacity alloc₁
        combined-cap-g = subst (next-slot alloc₁ + pair-slots *ℕ sg ≤_) (sym capacity₁-eq)
                           (compose-g-cap (next-slot alloc) (next-slot alloc₁) pair-slots sf sg
                              (frame-capacity alloc) slot₁-bound combined-cap-converted)

        -- Run g via recursive dispatch
        inter-before = IRResultAWF.result-before result-f
        not-halted₁ = IRResultAWF.not-halted result-f

        -- Set up RDI for g's input
        s₁' = record s₁ { regs = writeReg (regs s₁) RDI inter-loc }
        rdi-eq₁ : readReg (regs s₁') RDI ≡ inter-loc
        rdi-eq₁ = writeReg-same (regs s₁) RDI inter-loc

        inter-valid-wf' : ValidAtWF alloc₁ (eval f x) inter-loc s₁'
        inter-valid-wf' = validityWF-mem-only (eval f x) inter-loc s₁ s₁' refl refl inter-valid-wf

        result-g = rec-wf g (∘-g-smaller f g) (eval f x) inter-loc s₁' alloc₁ inter-valid-wf' inter-before not-halted₁ rdi-eq₁ combined-cap-g

        -- Final state and alloc
        s₂ = IRResultAWF.final-state result-g
        alloc₂ = IRResultAWF.final-alloc result-g

        ------------------------------------------------------------------------
        -- Compose slot-bounded: final slot ≤ initial slot + ir-req compose
        ------------------------------------------------------------------------
        slot-bounded-compose : next-slot alloc₂ ≤ next-slot alloc + ir-stack-requirement (g ∘ f)
        slot-bounded-compose = compose-slot-bounded-lemma
                                 (next-slot alloc) (next-slot alloc₁) (next-slot alloc₂)
                                 (ir-stack-requirement f) (ir-stack-requirement g)
                                 (IRResultAWF.slot-bounded result-g)
                                 (IRResultAWF.slot-bounded result-f)

        ------------------------------------------------------------------------
        -- Memory preservation for locations before initial frontier
        ------------------------------------------------------------------------
        mem-preserved-compose : ∀ loc → BeforeFrontier alloc loc →
          readLoc s₂ loc ≡ readLoc s loc
        mem-preserved-compose loc bf =
          let bf₁ = frontier-monotone alloc alloc₁
                      (sym (IRResultAWF.frame-preserved result-f))
                      (IRResultAWF.slot-monotone result-f)
                      (IRResultAWF.heap-monotone result-f)
                      loc bf
              step-g = IRResultAWF.mem-preserved-before result-g loc bf₁
              step-reg = readLoc-stackMem-eq s₁' s₁ loc refl refl
              step-f = IRResultAWF.mem-preserved-before result-f loc bf
          in trans step-g (trans step-reg step-f)

        ------------------------------------------------------------------------
        -- Reclamation: Use g's reclaimable-slot as the compose reclaim point
        -- Since compose's result is g's result, we use g's reclaim logic
        ------------------------------------------------------------------------
        reclaim-g = IRResultAWF.reclaimable-slot result-g

        compose-reclaim = reclaim-g

        -- reclaim-g ≥ next-slot alloc₁ ≥ next-slot alloc
        compose-reclaim-monotone : next-slot alloc ≤ compose-reclaim
        compose-reclaim-monotone = ≤-trans (IRResultAWF.slot-monotone result-f)
                                           (IRResultAWF.reclaim-monotone result-g)

        compose-reclaim-bounded : compose-reclaim ≤ next-slot alloc₂
        compose-reclaim-bounded = IRResultAWF.reclaim-bounded result-g

        compose-reclaim-preserves-result : ∀ (fits : compose-reclaim ≤ frame-capacity alloc) →
          BeforeFrontier (record alloc { next-slot = compose-reclaim ; slots-available = fits })
                         (IRResultAWF.result-loc result-g)
        compose-reclaim-preserves-result fits =
          let -- Use g's reclaim-preserves-result
              -- g was called with alloc₁, and reclaim-g ≤ frame-capacity alloc₁ = frame-capacity alloc
              fits₁ : reclaim-g ≤ frame-capacity alloc₁
              fits₁ = subst (reclaim-g ≤_) (sym capacity₁-eq) fits
              g-preserves = IRResultAWF.reclaim-preserves-result result-g fits₁
              -- Now transfer to alloc with compose-reclaim
          in frontier-same-heap
               (record alloc₁ { next-slot = reclaim-g ; slots-available = fits₁ })
               (record alloc { next-slot = compose-reclaim ; slots-available = fits })
               (IRResultAWF.frame-preserved result-f)
               refl
               (IRResultAWF.heap-preserved result-f)
               (IRResultAWF.result-loc result-g)
               g-preserves

    in record
      { result-loc = IRResultAWF.result-loc result-g
      ; final-state = s₂
      ; final-alloc = alloc₂
      ; result-valid-wf = IRResultAWF.result-valid-wf result-g
      ; result-before = IRResultAWF.result-before result-g
      ; rax-is-result = IRResultAWF.rax-is-result result-g
      ; not-halted = IRResultAWF.not-halted result-g
      ; frame-preserved = trans (IRResultAWF.frame-preserved result-g)
                                (IRResultAWF.frame-preserved result-f)
      ; slot-monotone = ≤-trans (IRResultAWF.slot-monotone result-f)
                                (IRResultAWF.slot-monotone result-g)
      ; heap-monotone = ≤-trans (IRResultAWF.heap-monotone result-f)
                                (IRResultAWF.heap-monotone result-g)
      ; heap-preserved = trans (IRResultAWF.heap-preserved result-g)
                               (IRResultAWF.heap-preserved result-f)
      ; slot-bounded = slot-bounded-compose
      ; capacity-preserved = trans (IRResultAWF.capacity-preserved result-g)
                                   (IRResultAWF.capacity-preserved result-f)
      ; mem-preserved-before = mem-preserved-compose
      ; reclaimable-slot = compose-reclaim
      ; reclaim-monotone = compose-reclaim-monotone
      ; reclaim-bounded = compose-reclaim-bounded
      ; reclaim-preserves-result = compose-reclaim-preserves-result
      }
