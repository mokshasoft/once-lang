------------------------------------------------------------------------
-- Once.Backend.X86v3.IR.PairWF
--
-- Pair IR implementation with ValidAtWF.
-- Extracted from Dispatcher.agda to minimize the mutual block.
--
-- Takes RecDispatcherWF as parameter for recursive dispatch to f and g.
--
-- Uses LINEAR capacity formula: pair-slots * ir-size
------------------------------------------------------------------------

module Once.Backend.X86v3.IR.PairWF where

open import Data.Nat using (ℕ; suc; _<_; _≤_; s≤s; z≤n) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; m≤m+n; m≤n+m; m<m+n; +-monoˡ-≤; +-monoʳ-≤; +-assoc; +-comm; m+n≤o⇒m≤o; *-monoʳ-≤; m≤m*n; *-distribˡ-+; *-suc; n≤1+n)
open import Data.Bool using (false)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)

open import Once.Backend.Common.FrameSemantics using (FrameSemantics)
open import Once.Backend.Common.SlotMachine
open import Once.Backend.X86v3.Types
open import Once.Backend.X86v3.IR
open import Once.Backend.X86v3.Allocation hiding (AllocMode)

------------------------------------------------------------------------
-- Pair implementation
------------------------------------------------------------------------

module PairWFImpl {FS : FrameSemantics} (program-bound : ℕ) where
  open import Once.Backend.X86v3.Validity
  open ValidityDef {FS} program-bound
  open FrontierInvariant {FS}
  open MemOps {FS}
  open WriteOps {FS}
  open StackAllocation {FS}
  open FrameSemantics FS

  -- Import IRResultAWF and ValidAtWF
  open import Once.Backend.X86v3.IRResult
  open DispatcherResult {FS} program-bound

  open import Once.Backend.X86v3.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound
    using (ValidAtWF; IRResultAWF; RecDispatcherWF; valid-pair-wf;
           validityWF-mem-only; validityWF-mem-preserved;
           validityWF-frontier-advance; validityWF-alloc-advance;
           validityWF-write-at-frontier; validityWF-write-at-suc-frontier)

  -- NOTE: Global capacity invariants removed - using dynamic capacity threading instead

  -- Import lemmas
  open import Once.Backend.X86v3.DispatcherArithmeticLemma
    using (suc<+2; compose-f-cap; compose-g-cap)
  open import Once.Backend.X86v3.FrontierLemma
  open FrontierLemmas {FS}
    using (frontier-same-heap; at-frontier-before-pair)
  open ExecLemmas {FS}

  -- Import write operations
  open import Once.Backend.X86v3.WriteOps using (module WriteWithDisjoint)
  open WriteWithDisjoint {FS}

  -- Import validity write lemmas for frontier inequality helpers
  open import Once.Backend.X86v3.ValidityWriteLemma using (module ValidityWriteLemmas)
  open ValidityWriteLemmas {FS} program-bound
    using (at-frontier-neq-before; suc-frontier-neq-before)

  -- Import ApplyWF for bf-same-frame-slot and validityWF-with-bf-transfer
  open import Once.Backend.X86v3.IR.ApplyWF
  open ApplyWFImpl {FS} program-bound
    using (bf-same-frame-slot; validityWF-with-bf-transfer)

  ------------------------------------------------------------------------
  -- Pair: run f and g, combine results into pair
  --
  -- Uses LINEAR capacity: pair-slots * ir-size covers ir-req + recursion
  --
  -- Key derivations (same pattern as compose):
  --   slot + pair-slots * sf ≤ slot + pair-slots * size (since sf < size)
  --   slot₁ + pair-slots * sg ≤ slot + pair-slots * size (via slot-bounded)
  --   pair allocation fits since pair-slots ≤ pair-slots * size
  ------------------------------------------------------------------------

  run-pair : ∀ {A B C} (f : IR A B) (g : IR A C) {m : AllocMode}
    (rec-wf : RecDispatcherWF (ir-size (⟨ f , g ⟩ m)))
    (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    -- LINEAR capacity: pair-slots * size covers ir-req + recursion
    -- This is the ONLY capacity constraint needed (no global invariants)
    next-slot alloc +ℕ pair-slots *ℕ ir-size (⟨ f , g ⟩ m) ≤ frame-capacity alloc →
    IRResultAWF (⟨ f , g ⟩ m) x s alloc
  run-pair f g {m} rec-wf x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap =
    record
      { result-loc = pair-loc
      ; final-state = s-final
      ; final-alloc = alloc₃
      ; result-valid-wf = pair-valid-wf-final
      ; result-before = pair-before
      ; rax-is-result = rax-eq
      ; not-halted = not-halted-final
      ; frame-preserved = frame-preserved-pair
      ; slot-monotone = slot-monotone-pair
      ; heap-monotone = heap-monotone-pair
      ; heap-preserved = heap-preserved-pair
      ; capacity-preserved = capacity-preserved-pair
      ; mem-preserved-before = mem-preserved-pair
      ; reclaimable-slot = pair-reclaim
      ; reclaim-monotone = pair-reclaim-monotone
      ; reclaim-bounded = pair-reclaim-bounded
      ; reclaim-preserves-result = pair-reclaim-preserves
      ; reclaim-preserves-validity = pair-reclaim-preserves-validity
      ; reclaim-size-bound = pair-reclaim-size-bound
      }
    where
      -- Size abbreviations
      sf = ir-size f
      sg = ir-size g
      size = ir-size (⟨ f , g ⟩ m)  -- = suc (sf +ℕ sg)

      ------------------------------------------------------------------------
      -- Derive capacity for f (same as compose)
      ------------------------------------------------------------------------
      combined-cap-converted : next-slot alloc +ℕ pair-slots *ℕ suc (sf +ℕ sg) ≤ frame-capacity alloc
      combined-cap-converted = combined-cap  -- size = suc (sf +ℕ sg) directly for pair

      combined-cap-f : next-slot alloc +ℕ pair-slots *ℕ sf ≤ frame-capacity alloc
      combined-cap-f = compose-f-cap (next-slot alloc) pair-slots sf sg (frame-capacity alloc) combined-cap-converted

      -- Run f via recursive dispatch (with linear capacity only)
      result-f = rec-wf f (⟨,⟩-f-smaller f g {m}) x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap-f
      s₁ = IRResultAWF.final-state result-f
      alloc₁ = IRResultAWF.final-alloc result-f
      fst-loc = IRResultAWF.result-loc result-f
      fst-valid-wf = IRResultAWF.result-valid-wf result-f

      ------------------------------------------------------------------------
      -- Reclaim after f: Reset slot to reclaimable-slot
      -- This is key to eliminating slot-bounded
      ------------------------------------------------------------------------
      reclaim-f = IRResultAWF.reclaimable-slot result-f

      -- reclaim-f is bounded by f's size
      reclaim-f-bound : reclaim-f ≤ next-slot alloc +ℕ pair-slots *ℕ sf
      reclaim-f-bound = IRResultAWF.reclaim-size-bound result-f

      -- Derive that reclaim fits in capacity for creating reclaimed alloc
      -- Chain: reclaim-f ≤ slot + ps*sf ≤ slot + ps*(sf+sg) ≤ slot + ps*suc(sf+sg) ≤ cap
      reclaim-f-fits : reclaim-f ≤ frame-capacity alloc
      reclaim-f-fits = ≤-trans reclaim-f-bound
                         (≤-trans (+-monoʳ-≤ (next-slot alloc) (*-monoʳ-≤ pair-slots (m≤m+n sf sg)))
                           (≤-trans (+-monoʳ-≤ (next-slot alloc) (*-monoʳ-≤ pair-slots (n≤1+n (sf +ℕ sg))))
                             combined-cap-converted))

      -- Create reclaimed allocation
      alloc₁-reclaimed : AllocState {FS}
      alloc₁-reclaimed = record alloc
        { next-slot = reclaim-f
        ; slots-available = reclaim-f-fits
        }

      ------------------------------------------------------------------------
      -- Derive capacity for g (using reclaim-f-bound)
      ------------------------------------------------------------------------

      capacity₁-eq : frame-capacity alloc₁ ≡ frame-capacity alloc
      capacity₁-eq = IRResultAWF.capacity-preserved result-f

      -- Derive capacity for g using reclaimed allocation
      -- reclaim-f +ℕ ps*sg ≤ slot + ps*sf + ps*sg = slot + ps*(sf+sg) < slot + ps*suc(sf+sg) ≤ cap
      combined-cap-g : reclaim-f +ℕ pair-slots *ℕ sg ≤ frame-capacity alloc
      combined-cap-g = compose-g-cap (next-slot alloc) reclaim-f pair-slots sf sg
                         (frame-capacity alloc) reclaim-f-bound combined-cap-converted

      -- Run g via recursive dispatch WITH RECLAIMED ALLOCATION
      -- g needs same input as f, but input validity is preserved through f
      input-before₁-reclaimed : BeforeFrontier alloc₁-reclaimed input-loc
      input-before₁-reclaimed = frontier-monotone alloc alloc₁-reclaimed
                                  refl  -- frame preserved (same frame)
                                  (IRResultAWF.reclaim-monotone result-f)  -- slot ≤ reclaim-f
                                  ≤-refl  -- heap same
                                  input-loc input-before

      -- Input validity preserved through f's execution (memory at input-loc unchanged)
      -- Step 1: Memory preserved means validity preserved across state change (same alloc)
      input-valid-wf-s1 : ValidAtWF alloc x input-loc s₁
      input-valid-wf-s1 = validityWF-mem-preserved x input-loc s s₁
                            input-before
                            (λ loc bf → IRResultAWF.mem-preserved-before result-f loc bf)
                            input-valid-wf

      -- Step 2: Frontier advanced to reclaimed, so validity transfers (same state)
      input-valid-wf₁-reclaimed : ValidAtWF alloc₁-reclaimed x input-loc s₁
      input-valid-wf₁-reclaimed = validityWF-frontier-advance x input-loc s₁
                                    refl  -- frame preserved
                                    (IRResultAWF.reclaim-monotone result-f)  -- slot ≤ reclaim-f
                                    ≤-refl  -- heap same
                                    input-valid-wf-s1

      -- Set up RDI for g's input
      s₁' = record s₁ { regs = writeReg (regs s₁) RDI input-loc }
      rdi-eq₁ : readReg (regs s₁') RDI ≡ input-loc
      rdi-eq₁ = writeReg-same (regs s₁) RDI input-loc

      input-valid-wf₁' : ValidAtWF alloc₁-reclaimed x input-loc s₁'
      input-valid-wf₁' = validityWF-mem-only x input-loc s₁ s₁' refl refl input-valid-wf₁-reclaimed

      result-g = rec-wf g (⟨,⟩-g-smaller f g {m}) x input-loc s₁' alloc₁-reclaimed
                   input-valid-wf₁' input-before₁-reclaimed (IRResultAWF.not-halted result-f) rdi-eq₁ combined-cap-g

      s₂ = IRResultAWF.final-state result-g
      alloc₂ = IRResultAWF.final-alloc result-g
      snd-loc = IRResultAWF.result-loc result-g
      snd-valid-wf = IRResultAWF.result-valid-wf result-g

      ------------------------------------------------------------------------
      -- Pair allocation (using reclaimed allocations)
      --
      -- Key insight: allocate pair at RECLAIM-G position, not next-slot alloc₂
      -- This ensures we can prove reclaim-size-bound without postulates.
      --
      -- Chain:
      --   reclaim-g ≤ reclaim-f +ℕ pair-slots * sg  (from g's reclaim-size-bound)
      --   reclaim-f ≤ slot + pair-slots * sf       (from f's reclaim-size-bound)
      --   reclaim-g ≤ slot + pair-slots * (sf +ℕ sg)
      --   reclaim-g +ℕ pair-slots ≤ slot + pair-slots * suc(sf +ℕ sg) = slot + pair-slots * size ✓
      ------------------------------------------------------------------------
      reclaim-g = IRResultAWF.reclaimable-slot result-g

      reclaim-g-bound : reclaim-g ≤ reclaim-f +ℕ pair-slots *ℕ sg
      reclaim-g-bound = IRResultAWF.reclaim-size-bound result-g

      capacity₂-eq : frame-capacity alloc₂ ≡ frame-capacity alloc
      capacity₂-eq = IRResultAWF.capacity-preserved result-g

      -- reclaim-g ≤ slot + ps*(sf+sg)
      reclaim-g-from-slot : reclaim-g ≤ next-slot alloc +ℕ pair-slots *ℕ (sf +ℕ sg)
      reclaim-g-from-slot = ≤-trans reclaim-g-bound
                              (≤-trans (+-monoˡ-≤ (pair-slots *ℕ sg) reclaim-f-bound)
                                       (≤-reflexive (trans (+-assoc (next-slot alloc) (pair-slots *ℕ sf) (pair-slots *ℕ sg))
                                                           (cong (next-slot alloc +ℕ_) (sym (*-distribˡ-+ pair-slots sf sg))))))

      -- reclaim-g +ℕ ps ≤ (slot + ps*(sf+sg)) +ℕ ps
      step1 : reclaim-g +ℕ pair-slots ≤ (next-slot alloc +ℕ pair-slots *ℕ (sf +ℕ sg)) +ℕ pair-slots
      step1 = +-monoˡ-≤ pair-slots reclaim-g-from-slot

      -- (slot + ps*(sf+sg)) +ℕ ps = slot + (ps*(sf+sg) +ℕ ps)
      step2-eq : (next-slot alloc +ℕ pair-slots *ℕ (sf +ℕ sg)) +ℕ pair-slots ≡ next-slot alloc +ℕ (pair-slots *ℕ (sf +ℕ sg) +ℕ pair-slots)
      step2-eq = +-assoc (next-slot alloc) (pair-slots *ℕ (sf +ℕ sg)) pair-slots

      -- ps*(sf+sg) +ℕ ps = ps + ps*(sf+sg) = ps * suc(sf+sg)  (using *-suc: m * suc n = m + m * n)
      step3-eq : pair-slots *ℕ (sf +ℕ sg) +ℕ pair-slots ≡ pair-slots *ℕ suc (sf +ℕ sg)
      step3-eq = trans (+-comm (pair-slots *ℕ (sf +ℕ sg)) pair-slots)
                       (sym (*-suc pair-slots (sf +ℕ sg)))

      -- Combined: (slot + ps*(sf+sg)) +ℕ ps = slot + ps*suc(sf+sg)
      combined-eq : (next-slot alloc +ℕ pair-slots *ℕ (sf +ℕ sg)) +ℕ pair-slots ≡ next-slot alloc +ℕ pair-slots *ℕ suc (sf +ℕ sg)
      combined-eq = trans step2-eq (cong (next-slot alloc +ℕ_) step3-eq)

      -- reclaim-g +ℕ ps ≤ slot + ps*size ≤ capacity  (PROVEN!)
      reclaim-g-plus-pair-fits : reclaim-g +ℕ pair-slots ≤ frame-capacity alloc
      reclaim-g-plus-pair-fits = ≤-trans step1 (≤-trans (≤-reflexive combined-eq) combined-cap)

      -- Create reclaimed allocation for pair allocation at reclaim-g position
      alloc₂-reclaimed : AllocState {FS}
      alloc₂-reclaimed = record alloc
        { next-slot = reclaim-g
        ; slots-available = ≤-trans reclaim-g-from-slot
                              (≤-trans (+-monoʳ-≤ (next-slot alloc) (*-monoʳ-≤ pair-slots (n≤1+n (sf +ℕ sg))))
                                combined-cap)
        }

      -- Pair allocation fits at reclaim-g position
      pair-fits-at-reclaim : reclaim-g +ℕ pair-slots ≤ frame-capacity alloc
      pair-fits-at-reclaim = reclaim-g-plus-pair-fits

      -- Pair location at reclaim-g position (in alloc's frame)
      pair-loc = OnStack (current-frame alloc) reclaim-g

      alloc₃ : AllocState {FS}
      alloc₃ = record alloc
        { next-slot = reclaim-g +ℕ pair-slots
        ; slots-available = pair-fits-at-reclaim
        }

      -- Write fst and snd pointers to pair
      s₃ = write-loc s₂ pair-loc fst-loc
      s₄ = write-loc s₃ (sucLoc pair-loc) snd-loc
      s-final = record s₄ { regs = writeReg (regs s₄) RAX pair-loc }

      -- Pair before frontier (at reclaim-g, which is before alloc₃'s frontier)
      pair-before : BeforeFrontier alloc₃ pair-loc
      pair-before = stack-before refl (m<m+n reclaim-g {pair-slots} (s≤s z≤n))

      -- fst-loc is BeforeFrontier in alloc₃
      -- Chain: fst-loc before alloc₁ → before alloc₁-reclaimed → before alloc₂-reclaimed → before alloc₃
      fst-before₃ : BeforeFrontier alloc₃ fst-loc
      fst-before₃ = frontier-monotone alloc₁-reclaimed alloc₃
                      refl
                      (≤-trans (IRResultAWF.reclaim-monotone result-g) (m≤m+n reclaim-g pair-slots))
                      ≤-refl
                      fst-loc
                      (IRResultAWF.reclaim-preserves-result result-f reclaim-f-fits)

      -- snd-loc is BeforeFrontier in alloc₃
      snd-before₃ : BeforeFrontier alloc₃ snd-loc
      snd-before₃ = frontier-monotone alloc₂-reclaimed alloc₃
                      refl
                      (m≤m+n reclaim-g pair-slots)
                      ≤-refl
                      snd-loc
                      (IRResultAWF.reclaim-preserves-result result-g
                        (≤-trans reclaim-g-from-slot
                          (≤-trans (+-monoʳ-≤ (next-slot alloc) (*-monoʳ-≤ pair-slots (n≤1+n (sf +ℕ sg))))
                            combined-cap)))

      sucLoc-pair-before₃ : BeforeFrontier alloc₃ (sucLoc pair-loc)
      sucLoc-pair-before₃ = stack-before refl (suc<+2 reclaim-g)

      fst-ptr : readLoc s-final pair-loc ≡ just fst-loc
      fst-ptr = trans (readLoc-stackMem-eq s-final s₄ pair-loc refl refl)
                      (trans (write-preserves-disjoint s₃ (sucLoc pair-loc) snd-loc pair-loc
                               (sucLoc-neq pair-loc))
                             (write-read-same s₂ pair-loc fst-loc))

      snd-ptr : readLoc s-final (sucLoc pair-loc) ≡ just snd-loc
      snd-ptr = trans (readLoc-stackMem-eq s-final s₄ (sucLoc pair-loc) refl refl)
                      (write-read-same s₃ (sucLoc pair-loc) snd-loc)

      ------------------------------------------------------------------------
      -- Validity transfer for fst through write operations
      --
      -- fst-valid-wf : ValidAtWF alloc₁ (eval f x) fst-loc s₁
      -- We need: ValidAtWF alloc₃ (eval f x) fst-loc s-final
      --
      -- With reclaim-based allocation, we need to be careful:
      -- - pair-loc = OnStack (current-frame alloc) reclaim-g
      -- - fst-loc is BeforeFrontier alloc₁-reclaimed (from reclaim-preserves-result)
      -- - The writes at pair-loc and sucLoc pair-loc are disjoint from fst-loc
      ------------------------------------------------------------------------

      -- fst-loc is BeforeFrontier in alloc₁-reclaimed
      fst-before-reclaimed : BeforeFrontier alloc₁-reclaimed fst-loc
      fst-before-reclaimed = IRResultAWF.reclaim-preserves-result result-f reclaim-f-fits

      -- fst validity at s₁ with alloc₁-reclaimed
      -- Use reclaim-preserves-validity to handle reclamation (slot decreasing)
      fst-valid-s1-reclaimed : ValidAtWF alloc₁-reclaimed (eval f x) fst-loc s₁
      fst-valid-s1-reclaimed = IRResultAWF.reclaim-preserves-validity result-f reclaim-f-fits

      -- Step 1: s₁ → s₁' (register write only)
      fst-valid-s1' : ValidAtWF alloc₁-reclaimed (eval f x) fst-loc s₁'
      fst-valid-s1' = validityWF-mem-only (eval f x) fst-loc s₁ s₁' refl refl fst-valid-s1-reclaimed

      -- Step 2: s₁' → s₂ (g execution, memory preserved at BeforeFrontier alloc₁-reclaimed)
      fst-valid-s2-reclaimed : ValidAtWF alloc₁-reclaimed (eval f x) fst-loc s₂
      fst-valid-s2-reclaimed = validityWF-mem-preserved (eval f x) fst-loc s₁' s₂
                                 fst-before-reclaimed
                                 (λ loc bf → IRResultAWF.mem-preserved-before result-g loc bf)
                                 fst-valid-s1'

      -- Transfer fst validity to alloc₂-reclaimed
      fst-valid-s2-alloc2r : ValidAtWF alloc₂-reclaimed (eval f x) fst-loc s₂
      fst-valid-s2-alloc2r = validityWF-frontier-advance (eval f x) fst-loc s₂
                               refl
                               (IRResultAWF.reclaim-monotone result-g)
                               ≤-refl
                               fst-valid-s2-reclaimed

      -- fst-loc is before alloc₂-reclaimed's frontier (for write disjointness)
      fst-before-alloc2r : BeforeFrontier alloc₂-reclaimed fst-loc
      fst-before-alloc2r = frontier-monotone alloc₁-reclaimed alloc₂-reclaimed
                             refl
                             (IRResultAWF.reclaim-monotone result-g)
                             ≤-refl
                             fst-loc fst-before-reclaimed

      -- Step 3: s₂ → s₃ (write at pair-loc = frontier of alloc₂-reclaimed)
      fst-valid-s3 : ValidAtWF alloc₂-reclaimed (eval f x) fst-loc s₃
      fst-valid-s3 = validityWF-write-at-frontier (eval f x) fst-loc s₂ fst-loc
                       fst-before-alloc2r fst-valid-s2-alloc2r

      -- Step 4: s₃ → s₄ (write at sucLoc pair-loc = suc-frontier of alloc₂-reclaimed)
      fst-valid-s4 : ValidAtWF alloc₂-reclaimed (eval f x) fst-loc s₄
      fst-valid-s4 = validityWF-write-at-suc-frontier (eval f x) fst-loc s₃ snd-loc
                       fst-before-alloc2r fst-valid-s3

      -- Step 5: s₄ → s-final (register write)
      fst-valid-sfinal-alloc2r : ValidAtWF alloc₂-reclaimed (eval f x) fst-loc s-final
      fst-valid-sfinal-alloc2r = validityWF-mem-only (eval f x) fst-loc s₄ s-final refl refl fst-valid-s4

      -- Step 6: alloc₂-reclaimed → alloc₃ (pair-slots allocation)
      fst-valid-wf₃ : ValidAtWF alloc₃ (eval f x) fst-loc s-final
      fst-valid-wf₃ = validityWF-alloc-advance (eval f x) fst-loc s-final pair-slots pair-fits-at-reclaim
                        fst-valid-sfinal-alloc2r

      ------------------------------------------------------------------------
      -- Validity transfer for snd through write operations
      ------------------------------------------------------------------------

      -- snd-loc is BeforeFrontier in alloc₂-reclaimed
      snd-before-alloc2r : BeforeFrontier alloc₂-reclaimed snd-loc
      snd-before-alloc2r = IRResultAWF.reclaim-preserves-result result-g
                             (≤-trans reclaim-g-from-slot
                               (≤-trans (+-monoʳ-≤ (next-slot alloc) (*-monoʳ-≤ pair-slots (n≤1+n (sf +ℕ sg))))
                                 combined-cap))

      -- snd validity at s₂ with alloc₂-reclaimed
      -- Use reclaim-preserves-validity to handle reclamation (slot decreasing)
      snd-valid-s2-reclaimed : ValidAtWF alloc₂-reclaimed (eval g x) snd-loc s₂
      snd-valid-s2-reclaimed = IRResultAWF.reclaim-preserves-validity result-g
                                 (≤-trans reclaim-g-from-slot
                                   (≤-trans (+-monoʳ-≤ (next-slot alloc) (*-monoʳ-≤ pair-slots (n≤1+n (sf +ℕ sg))))
                                     combined-cap))

      snd-valid-wf₃ : ValidAtWF alloc₃ (eval g x) snd-loc s-final
      snd-valid-wf₃ = validityWF-alloc-advance (eval g x) snd-loc s-final pair-slots pair-fits-at-reclaim
                        (validityWF-mem-only (eval g x) snd-loc s₄ s-final refl refl
                          (validityWF-write-at-suc-frontier (eval g x) snd-loc s₃ snd-loc
                            snd-before-alloc2r
                            (validityWF-write-at-frontier (eval g x) snd-loc s₂ fst-loc
                              snd-before-alloc2r
                              snd-valid-s2-reclaimed)))

      pair-valid-wf-final : ValidAtWF alloc₃ (pair (eval f x) (eval g x)) pair-loc s-final
      pair-valid-wf-final = valid-pair-wf fst-ptr snd-ptr fst-before₃ snd-before₃ sucLoc-pair-before₃
                              fst-valid-wf₃ snd-valid-wf₃

      rax-eq : readReg (regs s-final) RAX ≡ pair-loc
      rax-eq = writeReg-same (regs s₄) RAX pair-loc

      not-halted-final : halted s-final ≡ false
      not-halted-final = IRResultAWF.not-halted result-g

      frame-preserved-pair : current-frame alloc₃ ≡ current-frame alloc
      frame-preserved-pair = refl  -- alloc₃ is based on alloc directly

      slot-monotone-pair : next-slot alloc ≤ next-slot alloc₃
      slot-monotone-pair = ≤-trans (IRResultAWF.reclaim-monotone result-f)
                                   (≤-trans (IRResultAWF.reclaim-monotone result-g)
                                            (m≤m+n reclaim-g pair-slots))

      heap-monotone-pair : next-heap-ref alloc ≤ next-heap-ref alloc₃
      heap-monotone-pair = ≤-refl  -- alloc₃ based on alloc, heap unchanged

      heap-preserved-pair : next-heap-ref alloc₃ ≡ next-heap-ref alloc
      heap-preserved-pair = refl  -- alloc₃ based on alloc

      capacity-preserved-pair : frame-capacity alloc₃ ≡ frame-capacity alloc
      capacity-preserved-pair = refl  -- alloc₃ based on alloc

      mem-preserved-pair : ∀ loc → BeforeFrontier alloc loc → readLoc s-final loc ≡ readLoc s loc
      mem-preserved-pair loc bf =
        let -- Transfer bf to alloc₁-reclaimed and alloc₂-reclaimed
            bf-reclaimed : BeforeFrontier alloc₁-reclaimed loc
            bf-reclaimed = frontier-monotone alloc alloc₁-reclaimed
                             refl
                             (IRResultAWF.reclaim-monotone result-f)
                             ≤-refl
                             loc bf
            bf-reclaimed2 : BeforeFrontier alloc₂-reclaimed loc
            bf-reclaimed2 = frontier-monotone alloc alloc₂-reclaimed
                              refl
                              (≤-trans (IRResultAWF.reclaim-monotone result-f) (IRResultAWF.reclaim-monotone result-g))
                              ≤-refl
                              loc bf
            step-g = IRResultAWF.mem-preserved-before result-g loc bf-reclaimed
            step-reg-g = readLoc-stackMem-eq s₁' s₁ loc refl refl
            step-f = IRResultAWF.mem-preserved-before result-f loc bf
        in trans (readLoc-stackMem-eq s-final s₄ loc refl refl)
                 (trans (write-preserves-disjoint s₃ (sucLoc pair-loc) snd-loc loc
                          (λ eq → suc-frontier-neq-before alloc₂-reclaimed loc bf-reclaimed2 eq))
                        (trans (write-preserves-disjoint s₂ pair-loc fst-loc loc
                                 (λ eq → at-frontier-neq-before alloc₂-reclaimed loc bf-reclaimed2 eq))
                               (trans step-g (trans step-reg-g step-f))))

      ------------------------------------------------------------------------
      -- Reclamation: pair-reclaim = reclaim-g +ℕ pair-slots
      --
      -- With reclaim-based allocation, we can prove reclaim-size-bound:
      --   reclaim-g ≤ slot + pair-slots * (sf +ℕ sg)
      --   reclaim-g +ℕ pair-slots ≤ slot + pair-slots * suc(sf +ℕ sg) = slot + pair-slots * size ✓
      ------------------------------------------------------------------------
      pair-reclaim = reclaim-g +ℕ pair-slots

      pair-reclaim-monotone : next-slot alloc ≤ pair-reclaim
      pair-reclaim-monotone = ≤-trans (IRResultAWF.reclaim-monotone result-f)
                                      (≤-trans (IRResultAWF.reclaim-monotone result-g)
                                               (m≤m+n reclaim-g pair-slots))

      pair-reclaim-bounded : pair-reclaim ≤ next-slot alloc₃
      pair-reclaim-bounded = ≤-refl  -- next-slot alloc₃ = reclaim-g +ℕ pair-slots

      pair-reclaim-preserves : ∀ (fits : pair-reclaim ≤ frame-capacity alloc) →
        BeforeFrontier (record alloc { next-slot = pair-reclaim ; slots-available = fits }) pair-loc
      pair-reclaim-preserves fits =
        frontier-same-heap alloc₃
          (record alloc { next-slot = pair-reclaim ; slots-available = fits })
          refl refl refl
          pair-loc pair-before

      -- Validity at reclaimed allocation - PROVEN via bf-same-frame-slot
      -- The two allocations have the same current-frame, next-slot, and next-heap-ref.
      -- Only slots-available differs (proof-irrelevant).
      pair-reclaim-preserves-validity : ∀ (fits : pair-reclaim ≤ frame-capacity alloc) →
        ValidAtWF (record alloc { next-slot = pair-reclaim ; slots-available = fits })
                  (pair (eval f x) (eval g x)) pair-loc s-final
      pair-reclaim-preserves-validity fits = validityWF-with-bf-transfer
        (pair (eval f x) (eval g x)) pair-loc s-final alloc₃
        (record alloc { next-slot = pair-reclaim ; slots-available = fits })
        (λ loc bf → bf-same-frame-slot alloc₃
          (record alloc { next-slot = pair-reclaim ; slots-available = fits })
          refl refl refl loc bf)
        pair-valid-wf-final

      -- reclaim-size-bound: FULLY PROVEN
      -- reclaim-g +ℕ pair-slots ≤ slot + pair-slots * size
      pair-reclaim-size-bound : pair-reclaim ≤ next-slot alloc +ℕ pair-slots *ℕ size
      pair-reclaim-size-bound = ≤-trans step1 (≤-reflexive combined-eq)

