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

open import Data.Nat using (ℕ; suc; _<_; _+_; _≤_; s≤s; z≤n) renaming (_*_ to _*ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; m≤m+n; m≤n+m; m<m+n; +-monoˡ-≤; +-monoʳ-≤; +-assoc; +-comm; m+n≤o⇒m≤o; *-monoʳ-≤; m≤m*n; *-distribˡ-+; *-suc)
open import Data.Bool using (false)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)

open import Once.Backend.Common.FrameSemantics using (FrameSemantics)
open import Once.Backend.Common.SlotMachine
open import Once.Backend.X86v3.Types
open import Once.Backend.X86v3.IR
open import Once.Backend.X86v3.Allocation

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
    using (pair-slot-bounded-lemma; suc<+2; compose-f-cap; compose-g-cap; pair-alloc-fits)

  -- Import stack bound lemma
  open import Once.Backend.X86v3.StackBoundLemma
    using (ir-stack-req-bounded)
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

  run-pair : ∀ {A B C} (f : IR A B) (g : IR A C)
    (rec-wf : RecDispatcherWF (ir-size ⟨ f , g ⟩))
    (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    -- LINEAR capacity: pair-slots * size covers ir-req + recursion
    -- This is the ONLY capacity constraint needed (no global invariants)
    next-slot alloc + pair-slots *ℕ ir-size ⟨ f , g ⟩ ≤ frame-capacity alloc →
    IRResultAWF ⟨ f , g ⟩ x s alloc
  run-pair f g rec-wf x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap =
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
      ; slot-bounded = slot-bounded-pair
      ; capacity-preserved = capacity-preserved-pair
      ; mem-preserved-before = mem-preserved-pair
      ; reclaimable-slot = pair-reclaim
      ; reclaim-monotone = pair-reclaim-monotone
      ; reclaim-bounded = pair-reclaim-bounded
      ; reclaim-preserves-result = pair-reclaim-preserves
      }
    where
      -- Size abbreviations
      sf = ir-size f
      sg = ir-size g
      size = ir-size ⟨ f , g ⟩  -- = suc (sf + sg)

      ------------------------------------------------------------------------
      -- Derive capacity for f (same as compose)
      ------------------------------------------------------------------------
      combined-cap-converted : next-slot alloc + pair-slots *ℕ suc (sf + sg) ≤ frame-capacity alloc
      combined-cap-converted = combined-cap  -- size = suc (sf + sg) directly for pair

      combined-cap-f : next-slot alloc + pair-slots *ℕ sf ≤ frame-capacity alloc
      combined-cap-f = compose-f-cap (next-slot alloc) pair-slots sf sg (frame-capacity alloc) combined-cap-converted

      -- Run f via recursive dispatch (with linear capacity only)
      result-f = rec-wf f (⟨,⟩-f-smaller f g) x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap-f
      s₁ = IRResultAWF.final-state result-f
      alloc₁ = IRResultAWF.final-alloc result-f
      fst-loc = IRResultAWF.result-loc result-f
      fst-valid-wf = IRResultAWF.result-valid-wf result-f

      ------------------------------------------------------------------------
      -- Derive capacity for g (same as compose)
      ------------------------------------------------------------------------
      slot₁-bound : next-slot alloc₁ ≤ next-slot alloc + pair-slots *ℕ sf
      slot₁-bound = ≤-trans (IRResultAWF.slot-bounded result-f)
                            (+-monoʳ-≤ (next-slot alloc) (ir-stack-req-bounded f))

      capacity₁-eq : frame-capacity alloc₁ ≡ frame-capacity alloc
      capacity₁-eq = IRResultAWF.capacity-preserved result-f

      combined-cap-g : next-slot alloc₁ + pair-slots *ℕ sg ≤ frame-capacity alloc₁
      combined-cap-g = subst (next-slot alloc₁ + pair-slots *ℕ sg ≤_) (sym capacity₁-eq)
                         (compose-g-cap (next-slot alloc) (next-slot alloc₁) pair-slots sf sg
                            (frame-capacity alloc) slot₁-bound combined-cap-converted)

      -- Run g via recursive dispatch
      -- g needs same input as f, but input validity is preserved through f
      input-before₁ : BeforeFrontier alloc₁ input-loc
      input-before₁ = frontier-monotone alloc alloc₁
                        (sym (IRResultAWF.frame-preserved result-f))
                        (IRResultAWF.slot-monotone result-f)
                        (IRResultAWF.heap-monotone result-f)
                        input-loc input-before

      -- Input validity preserved through f's execution (memory at input-loc unchanged)
      -- Step 1: Memory preserved means validity preserved across state change (same alloc)
      input-valid-wf-s1 : ValidAtWF alloc x input-loc s₁
      input-valid-wf-s1 = validityWF-mem-preserved x input-loc s s₁
                            input-before
                            (λ loc bf → IRResultAWF.mem-preserved-before result-f loc bf)
                            input-valid-wf

      -- Step 2: Frontier advanced, so validity transfers to alloc₁ (same state)
      input-valid-wf₁ : ValidAtWF alloc₁ x input-loc s₁
      input-valid-wf₁ = validityWF-frontier-advance x input-loc s₁
                          (IRResultAWF.frame-preserved result-f)
                          (IRResultAWF.slot-monotone result-f)
                          (IRResultAWF.heap-monotone result-f)
                          input-valid-wf-s1

      -- Set up RDI for g's input
      s₁' = record s₁ { regs = writeReg (regs s₁) RDI input-loc }
      rdi-eq₁ : readReg (regs s₁') RDI ≡ input-loc
      rdi-eq₁ = writeReg-same (regs s₁) RDI input-loc

      input-valid-wf₁' : ValidAtWF alloc₁ x input-loc s₁'
      input-valid-wf₁' = validityWF-mem-only x input-loc s₁ s₁' refl refl input-valid-wf₁

      result-g = rec-wf g (⟨,⟩-g-smaller f g) x input-loc s₁' alloc₁
                   input-valid-wf₁' input-before₁ (IRResultAWF.not-halted result-f) rdi-eq₁ combined-cap-g

      s₂ = IRResultAWF.final-state result-g
      alloc₂ = IRResultAWF.final-alloc result-g
      snd-loc = IRResultAWF.result-loc result-g
      snd-valid-wf = IRResultAWF.result-valid-wf result-g

      ------------------------------------------------------------------------
      -- Pair allocation
      ------------------------------------------------------------------------
      slot₂-bound : next-slot alloc₂ ≤ next-slot alloc₁ + pair-slots *ℕ sg
      slot₂-bound = ≤-trans (IRResultAWF.slot-bounded result-g)
                            (+-monoʳ-≤ (next-slot alloc₁) (ir-stack-req-bounded g))

      capacity₂-eq : frame-capacity alloc₂ ≡ frame-capacity alloc₁
      capacity₂-eq = IRResultAWF.capacity-preserved result-g

      -- pair-fits: next-slot alloc₂ + pair-slots ≤ capacity
      -- Chain: slot₂ ≤ slot₁ + ps*sg ≤ slot + ps*sf + ps*sg = slot + ps*(sf+sg)
      -- And slot₂ + ps ≤ slot + ps*(sf+sg) + ps = slot + (ps*(sf+sg) + ps) = slot + ps*suc(sf+sg)
      -- And slot + ps*suc(sf+sg) ≤ capacity (by combined-cap)

      -- slot₂ ≤ slot + ps*(sf+sg)
      slot₂-from-slot : next-slot alloc₂ ≤ next-slot alloc + pair-slots *ℕ (sf + sg)
      slot₂-from-slot = ≤-trans slot₂-bound
                          (≤-trans (+-monoˡ-≤ (pair-slots *ℕ sg) slot₁-bound)
                                   (≤-reflexive (trans (+-assoc (next-slot alloc) (pair-slots *ℕ sf) (pair-slots *ℕ sg))
                                                       (cong (next-slot alloc +_) (sym (*-distribˡ-+ pair-slots sf sg))))))

      -- slot₂ + ps ≤ (slot + ps*(sf+sg)) + ps
      step1 : next-slot alloc₂ + pair-slots ≤ (next-slot alloc + pair-slots *ℕ (sf + sg)) + pair-slots
      step1 = +-monoˡ-≤ pair-slots slot₂-from-slot

      -- (slot + ps*(sf+sg)) + ps = slot + (ps*(sf+sg) + ps)
      step2-eq : (next-slot alloc + pair-slots *ℕ (sf + sg)) + pair-slots ≡ next-slot alloc + (pair-slots *ℕ (sf + sg) + pair-slots)
      step2-eq = +-assoc (next-slot alloc) (pair-slots *ℕ (sf + sg)) pair-slots

      -- ps*(sf+sg) + ps = ps + ps*(sf+sg) = ps * suc(sf+sg)  (using *-suc: m * suc n = m + m * n)
      step3-eq : pair-slots *ℕ (sf + sg) + pair-slots ≡ pair-slots *ℕ suc (sf + sg)
      step3-eq = trans (+-comm (pair-slots *ℕ (sf + sg)) pair-slots)
                       (sym (*-suc pair-slots (sf + sg)))

      -- Combined: (slot + ps*(sf+sg)) + ps = slot + ps*suc(sf+sg)
      combined-eq : (next-slot alloc + pair-slots *ℕ (sf + sg)) + pair-slots ≡ next-slot alloc + pair-slots *ℕ suc (sf + sg)
      combined-eq = trans step2-eq (cong (next-slot alloc +_) step3-eq)

      -- slot₂ + ps ≤ slot + ps*suc(sf+sg) ≤ capacity
      pair-fits : next-slot alloc₂ + pair-slots ≤ frame-capacity alloc₂
      pair-fits = subst (next-slot alloc₂ + pair-slots ≤_)
                        (sym (trans capacity₂-eq capacity₁-eq))
                        (≤-trans (subst (next-slot alloc₂ + pair-slots ≤_) combined-eq step1)
                                 combined-cap)

      pair-loc = OnStack (current-frame alloc₂) (next-slot alloc₂)

      alloc₃ : AllocState {FS}
      alloc₃ = record alloc₂
        { next-slot = next-slot alloc₂ + pair-slots
        ; slots-available = pair-fits
        }

      -- Write fst and snd pointers to pair
      s₃ = write-loc s₂ pair-loc fst-loc
      s₄ = write-loc s₃ (sucLoc pair-loc) snd-loc
      s-final = record s₄ { regs = writeReg (regs s₄) RAX pair-loc }

      -- Pair before frontier (at frontier of alloc₂, which is before alloc₃'s frontier)
      pair-before : BeforeFrontier alloc₃ pair-loc
      pair-before = at-frontier-before-pair alloc₂ pair-fits

      -- Result validity for pair
      fst-before₃ : BeforeFrontier alloc₃ fst-loc
      fst-before₃ = frontier-monotone alloc₂ alloc₃
                      refl (m≤m+n (next-slot alloc₂) pair-slots) ≤-refl
                      fst-loc
                      (frontier-monotone alloc₁ alloc₂
                        (sym (IRResultAWF.frame-preserved result-g))
                        (IRResultAWF.slot-monotone result-g)
                        (IRResultAWF.heap-monotone result-g)
                        fst-loc
                        (IRResultAWF.result-before result-f))

      snd-before₃ : BeforeFrontier alloc₃ snd-loc
      snd-before₃ = frontier-monotone alloc₂ alloc₃
                      refl (m≤m+n (next-slot alloc₂) pair-slots) ≤-refl
                      snd-loc
                      (IRResultAWF.result-before result-g)

      sucLoc-pair-before₃ : BeforeFrontier alloc₃ (sucLoc pair-loc)
      sucLoc-pair-before₃ = stack-before refl (suc<+2 (next-slot alloc₂))

      fst-ptr : readLoc s-final pair-loc ≡ just fst-loc
      fst-ptr = trans (readLoc-stackMem-eq s-final s₄ pair-loc refl refl)
                      (trans (write-preserves-disjoint s₃ (sucLoc pair-loc) snd-loc pair-loc
                               (sucLoc-neq pair-loc))
                             (write-read-same s₂ pair-loc fst-loc))

      snd-ptr : readLoc s-final (sucLoc pair-loc) ≡ just snd-loc
      snd-ptr = trans (readLoc-stackMem-eq s-final s₄ (sucLoc pair-loc) refl refl)
                      (write-read-same s₃ (sucLoc pair-loc) snd-loc)

      -- Advance validity through writes and allocation
      -- fst-valid-wf : ValidAtWF alloc₁ (eval f x) fst-loc s₁

      -- Step 1: s₁ → s₁' (register write only)
      fst-valid-s1' : ValidAtWF alloc₁ (eval f x) fst-loc s₁'
      fst-valid-s1' = validityWF-mem-only (eval f x) fst-loc s₁ s₁' refl refl fst-valid-wf

      -- fst-loc is before alloc₁'s frontier (needed for mem-preserved)
      fst-before-alloc1 : BeforeFrontier alloc₁ fst-loc
      fst-before-alloc1 = IRResultAWF.result-before result-f

      -- Step 2a: s₁' → s₂ (g execution, memory preserved at BeforeFrontier alloc₁)
      fst-valid-s2-alloc1 : ValidAtWF alloc₁ (eval f x) fst-loc s₂
      fst-valid-s2-alloc1 = validityWF-mem-preserved (eval f x) fst-loc s₁' s₂
                              fst-before-alloc1
                              (λ loc bf → IRResultAWF.mem-preserved-before result-g loc bf)
                              fst-valid-s1'

      -- Step 2b: alloc₁ → alloc₂ (frontier advance)
      fst-valid-s2 : ValidAtWF alloc₂ (eval f x) fst-loc s₂
      fst-valid-s2 = validityWF-frontier-advance (eval f x) fst-loc s₂
                       (IRResultAWF.frame-preserved result-g)
                       (IRResultAWF.slot-monotone result-g)
                       (IRResultAWF.heap-monotone result-g)
                       fst-valid-s2-alloc1

      -- fst-loc is before alloc₂'s frontier (needed for write lemmas)
      fst-before-alloc2 : BeforeFrontier alloc₂ fst-loc
      fst-before-alloc2 = frontier-monotone alloc₁ alloc₂
                            (sym (IRResultAWF.frame-preserved result-g))
                            (IRResultAWF.slot-monotone result-g)
                            (IRResultAWF.heap-monotone result-g)
                            fst-loc fst-before-alloc1

      -- Step 3: s₂ → s₃ (write at pair-loc = frontier of alloc₂)
      fst-valid-s3 : ValidAtWF alloc₂ (eval f x) fst-loc s₃
      fst-valid-s3 = validityWF-write-at-frontier (eval f x) fst-loc s₂ fst-loc
                       fst-before-alloc2 fst-valid-s2

      -- Step 4: s₃ → s₄ (write at sucLoc pair-loc = suc-frontier of alloc₂)
      fst-valid-s4 : ValidAtWF alloc₂ (eval f x) fst-loc s₄
      fst-valid-s4 = validityWF-write-at-suc-frontier (eval f x) fst-loc s₃ snd-loc
                       fst-before-alloc2 fst-valid-s3

      -- Step 5: s₄ → s-final (register write)
      fst-valid-sfinal-alloc2 : ValidAtWF alloc₂ (eval f x) fst-loc s-final
      fst-valid-sfinal-alloc2 = validityWF-mem-only (eval f x) fst-loc s₄ s-final refl refl fst-valid-s4

      -- Step 6: alloc₂ → alloc₃ (pair-slots allocation)
      fst-valid-wf₃ : ValidAtWF alloc₃ (eval f x) fst-loc s-final
      fst-valid-wf₃ = validityWF-alloc-advance (eval f x) fst-loc s-final pair-slots pair-fits
                        fst-valid-sfinal-alloc2

      -- snd-loc is before alloc₂'s frontier
      snd-before-alloc2 : BeforeFrontier alloc₂ snd-loc
      snd-before-alloc2 = IRResultAWF.result-before result-g

      snd-valid-wf₃ : ValidAtWF alloc₃ (eval g x) snd-loc s-final
      snd-valid-wf₃ = validityWF-alloc-advance (eval g x) snd-loc s-final pair-slots pair-fits
                        (validityWF-mem-only (eval g x) snd-loc s₄ s-final refl refl
                          (validityWF-write-at-suc-frontier (eval g x) snd-loc s₃ snd-loc
                            snd-before-alloc2
                            (validityWF-write-at-frontier (eval g x) snd-loc s₂ fst-loc
                              snd-before-alloc2
                              snd-valid-wf)))

      pair-valid-wf-final : ValidAtWF alloc₃ (pair (eval f x) (eval g x)) pair-loc s-final
      pair-valid-wf-final = valid-pair-wf fst-ptr snd-ptr fst-before₃ snd-before₃ sucLoc-pair-before₃
                              fst-valid-wf₃ snd-valid-wf₃

      rax-eq : readReg (regs s-final) RAX ≡ pair-loc
      rax-eq = writeReg-same (regs s₄) RAX pair-loc

      not-halted-final : halted s-final ≡ false
      not-halted-final = IRResultAWF.not-halted result-g

      frame-preserved-pair : current-frame alloc₃ ≡ current-frame alloc
      frame-preserved-pair = trans (IRResultAWF.frame-preserved result-g)
                                   (IRResultAWF.frame-preserved result-f)

      slot-monotone-pair : next-slot alloc ≤ next-slot alloc₃
      slot-monotone-pair = ≤-trans (IRResultAWF.slot-monotone result-f)
                                   (≤-trans (IRResultAWF.slot-monotone result-g)
                                            (m≤m+n (next-slot alloc₂) pair-slots))

      heap-monotone-pair : next-heap-ref alloc ≤ next-heap-ref alloc₃
      heap-monotone-pair = ≤-trans (IRResultAWF.heap-monotone result-f)
                                   (IRResultAWF.heap-monotone result-g)

      heap-preserved-pair : next-heap-ref alloc₃ ≡ next-heap-ref alloc
      heap-preserved-pair = trans (IRResultAWF.heap-preserved result-g)
                                  (IRResultAWF.heap-preserved result-f)

      slot-bounded-pair : next-slot alloc₃ ≤ next-slot alloc + ir-stack-requirement ⟨ f , g ⟩
      slot-bounded-pair = pair-slot-bounded-lemma
                            (next-slot alloc) (next-slot alloc₁) (next-slot alloc₂)
                            (ir-stack-requirement f) (ir-stack-requirement g) pair-slots
                            (IRResultAWF.slot-bounded result-g)
                            (IRResultAWF.slot-bounded result-f)

      capacity-preserved-pair : frame-capacity alloc₃ ≡ frame-capacity alloc
      capacity-preserved-pair = trans capacity₂-eq capacity₁-eq

      mem-preserved-pair : ∀ loc → BeforeFrontier alloc loc → readLoc s-final loc ≡ readLoc s loc
      mem-preserved-pair loc bf =
        let bf₁ = frontier-monotone alloc alloc₁
                    (sym (IRResultAWF.frame-preserved result-f))
                    (IRResultAWF.slot-monotone result-f)
                    (IRResultAWF.heap-monotone result-f)
                    loc bf
            bf₂ = frontier-monotone alloc₁ alloc₂
                    (sym (IRResultAWF.frame-preserved result-g))
                    (IRResultAWF.slot-monotone result-g)
                    (IRResultAWF.heap-monotone result-g)
                    loc bf₁
            step-g = IRResultAWF.mem-preserved-before result-g loc bf₁
            step-reg-g = readLoc-stackMem-eq s₁' s₁ loc refl refl
            step-f = IRResultAWF.mem-preserved-before result-f loc bf
        in trans (readLoc-stackMem-eq s-final s₄ loc refl refl)
                 (trans (write-preserves-disjoint s₃ (sucLoc pair-loc) snd-loc loc
                          (λ eq → suc-frontier-neq-before alloc₂ loc bf₂ eq))
                        (trans (write-preserves-disjoint s₂ pair-loc fst-loc loc
                                 (λ eq → at-frontier-neq-before alloc₂ loc bf₂ eq))
                               (trans step-g (trans step-reg-g step-f))))

      -- Reclamation: use pair-loc's position (after all sub-IR results)
      pair-reclaim = next-slot alloc₂ + pair-slots

      pair-reclaim-monotone : next-slot alloc ≤ pair-reclaim
      pair-reclaim-monotone = slot-monotone-pair

      pair-reclaim-bounded : pair-reclaim ≤ next-slot alloc₃
      pair-reclaim-bounded = ≤-refl

      pair-reclaim-preserves : ∀ (fits : pair-reclaim ≤ frame-capacity alloc) →
        BeforeFrontier (record alloc { next-slot = pair-reclaim ; slots-available = fits }) pair-loc
      pair-reclaim-preserves fits =
        frontier-same-heap alloc₃
          (record alloc { next-slot = pair-reclaim ; slots-available = fits })
          frame-preserved-pair refl heap-preserved-pair
          pair-loc pair-before

