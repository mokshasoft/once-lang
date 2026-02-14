------------------------------------------------------------------------
-- Once.Backend.X86v3.IR.PairWF
--
-- Pair IR implementation with ValidAtWF.
-- Extracted from Dispatcher.agda to minimize the mutual block.
--
-- Takes RecDispatcherWF as parameter for recursive dispatch to f and g.
------------------------------------------------------------------------

module Once.Backend.X86v3.IR.PairWF where

open import Data.Nat using (ℕ; suc; _<_; _+_; _≤_; s≤s; z≤n) renaming (_*_ to _*ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; m≤m+n; m<m+n; +-monoˡ-≤; +-assoc; m+n≤o⇒m≤o)
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

  -- Import lemmas
  open import Once.Backend.X86v3.DispatcherArithmeticLemma
    using (pair-slot-bounded-lemma; suc<+2)
  open import Once.Backend.X86v3.FrontierLemma
  open FrontierLemmas {FS}
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
  -- Takes RecDispatcherWF as parameter instead of constructing it internally.
  -- The caller (Dispatcher.run-ir-wf) passes make-rec-wf ir<bound rs.
  ------------------------------------------------------------------------

  run-pair : ∀ {A B C} (f : IR A B) (g : IR A C)
    (rec-wf : RecDispatcherWF (ir-size ⟨ f , g ⟩))
    (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    next-slot alloc + ir-stack-requirement ⟨ f , g ⟩ ≤ frame-capacity alloc →
    next-slot alloc + pair-slots + pair-slots *ℕ program-bound ≤ frame-capacity alloc →  -- body-capacity
    IRResultAWF ⟨ f , g ⟩ x s alloc
  run-pair f g rec-wf x input-loc s alloc input-valid-wf input-before not-halted rdi-eq ir-cap body-cap =
    record
      { result-loc = pair-loc
      ; final-state = s-final
      ; final-alloc = alloc₃
      ; result-valid-wf = pair-valid-wf
      ; result-before = pair-before
      ; rax-is-result = rax-eq
      ; not-halted = IRResultAWF.not-halted result-g
      ; frame-preserved = trans (trans refl (IRResultAWF.frame-preserved result-g)) (IRResultAWF.frame-preserved result-f)
      ; slot-monotone = ≤-trans (≤-trans (IRResultAWF.slot-monotone result-f) (IRResultAWF.slot-monotone result-g)) (m≤m+n (next-slot alloc₂) pair-slots)
      ; heap-monotone = ≤-trans (IRResultAWF.heap-monotone result-f) (IRResultAWF.heap-monotone result-g)
      ; slot-bounded = pair-slot-bounded-lemma (next-slot alloc) (next-slot alloc₁) (next-slot alloc₂) (ir-stack-requirement f) (ir-stack-requirement g) pair-slots (IRResultAWF.slot-bounded result-g) (IRResultAWF.slot-bounded result-f)
      ; capacity-preserved = trans (IRResultAWF.capacity-preserved result-g) (IRResultAWF.capacity-preserved result-f)
      ; mem-preserved-before = mem-preserved-pair
      -- Reclamation: pair allocates pair-slots at alloc₂'s frontier
      ; reclaimable-slot = next-slot alloc₂ + pair-slots
      ; reclaim-monotone = ≤-trans (≤-trans (IRResultAWF.slot-monotone result-f) (IRResultAWF.slot-monotone result-g)) (m≤m+n (next-slot alloc₂) pair-slots)
      ; reclaim-bounded = ≤-refl
      ; reclaim-preserves-result = λ fits → pair-before
      }
    where
      -- PROVEN: ir-capacity for f from pair's ir-capacity
      ir-cap-f : next-slot alloc + ir-stack-requirement f ≤ frame-capacity alloc
      ir-cap-f = m+n≤o⇒m≤o (next-slot alloc + ir-stack-requirement f)
                   (subst (λ x → x ≤ frame-capacity alloc)
                          (trans (cong (next-slot alloc +_)
                                       (+-assoc (ir-stack-requirement f) (ir-stack-requirement g) pair-slots))
                                 (sym (+-assoc (next-slot alloc) (ir-stack-requirement f) (ir-stack-requirement g + pair-slots))))
                          ir-cap)

      -- Run f via dispatcher
      result-f = rec-wf f (⟨,⟩-f-smaller f g) x input-loc s alloc input-valid-wf input-before not-halted rdi-eq ir-cap-f body-cap
      s₁ = IRResultAWF.final-state result-f
      alloc₁ = IRResultAWF.final-alloc result-f
      s₁-rdi = record s₁ { regs = writeReg (regs s₁) RDI input-loc }
      input-before₁ = frontier-monotone alloc alloc₁
                        (sym (IRResultAWF.frame-preserved result-f))
                        (IRResultAWF.slot-monotone result-f)
                        (IRResultAWF.heap-monotone result-f)
                        input-loc input-before

      -- PROVEN: Input validity preserved through f's execution
      mem-eq-s-to-s₁-rdi : ∀ loc' → BeforeFrontier alloc loc' → readLoc s₁-rdi loc' ≡ readLoc s loc'
      mem-eq-s-to-s₁-rdi loc' bf =
        trans (readLoc-stackMem-eq s₁-rdi s₁ loc' refl refl)
              (IRResultAWF.mem-preserved-before result-f loc' bf)

      input-valid-wf-s₁-rdi : ValidAtWF alloc x input-loc s₁-rdi
      input-valid-wf-s₁-rdi = validityWF-mem-preserved x input-loc s s₁-rdi input-before mem-eq-s-to-s₁-rdi input-valid-wf

      input-valid-wf₁ : ValidAtWF alloc₁ x input-loc s₁-rdi
      input-valid-wf₁ = validityWF-frontier-advance x input-loc s₁-rdi
                          (IRResultAWF.frame-preserved result-f)
                          (IRResultAWF.slot-monotone result-f)
                          (IRResultAWF.heap-monotone result-f)
                          input-valid-wf-s₁-rdi

      -- PROVEN: ir-capacity for g from pair's ir-capacity
      ir-cap-g : next-slot alloc₁ + ir-stack-requirement g ≤ frame-capacity alloc₁
      ir-cap-g = subst (λ cap → next-slot alloc₁ + ir-stack-requirement g ≤ cap)
                   (sym (IRResultAWF.capacity-preserved result-f))
                   (≤-trans
                     (+-monoˡ-≤ (ir-stack-requirement g) (IRResultAWF.slot-bounded result-f))
                     (m+n≤o⇒m≤o (next-slot alloc + ir-stack-requirement f + ir-stack-requirement g)
                       (subst (λ x → x ≤ frame-capacity alloc)
                              (trans (sym (+-assoc (next-slot alloc) (ir-stack-requirement f + ir-stack-requirement g) pair-slots))
                                     (cong (_+ pair-slots) (sym (+-assoc (next-slot alloc) (ir-stack-requirement f) (ir-stack-requirement g)))))
                              ir-cap)))

      -- Body-capacity for g (postulate - architectural invariant)
      postulate
        body-cap-g : next-slot alloc₁ + pair-slots + pair-slots *ℕ program-bound ≤ frame-capacity alloc₁

      -- Run g via dispatcher
      result-g = rec-wf g (⟨,⟩-g-smaller f g) x input-loc s₁-rdi alloc₁
                   input-valid-wf₁
                   input-before₁
                   (IRResultAWF.not-halted result-f)
                   (writeReg-same (regs s₁) RDI input-loc)
                   ir-cap-g
                   body-cap-g

      fst-loc = IRResultAWF.result-loc result-f
      fst-before = IRResultAWF.result-before result-f
      fst-valid-wf = IRResultAWF.result-valid-wf result-f
      s₂ = IRResultAWF.final-state result-g
      alloc₂ = IRResultAWF.final-alloc result-g
      snd-loc = IRResultAWF.result-loc result-g
      snd-before = IRResultAWF.result-before result-g
      snd-valid-wf = IRResultAWF.result-valid-wf result-g
      pair-loc = OnStack (current-frame alloc₂) (next-slot alloc₂)

      -- PROVEN: pair-fits from ir-capacity
      pair-fits : next-slot alloc₂ + pair-slots ≤ frame-capacity alloc₂
      pair-fits = subst (λ cap → next-slot alloc₂ + pair-slots ≤ cap)
                    (sym (trans (IRResultAWF.capacity-preserved result-g)
                                (IRResultAWF.capacity-preserved result-f)))
                    (≤-trans
                      (subst (λ x → next-slot alloc₂ + pair-slots ≤ x)
                             (+-assoc (next-slot alloc) (ir-stack-requirement f + ir-stack-requirement g) pair-slots)
                             (+-monoˡ-≤ pair-slots slot₂-bound))
                      ir-cap)
        where
          slot₂-bound : next-slot alloc₂ ≤ next-slot alloc + (ir-stack-requirement f + ir-stack-requirement g)
          slot₂-bound = ≤-trans
                          (≤-trans (IRResultAWF.slot-bounded result-g)
                                   (+-monoˡ-≤ (ir-stack-requirement g) (IRResultAWF.slot-bounded result-f)))
                          (≤-reflexive (+-assoc (next-slot alloc) (ir-stack-requirement f) (ir-stack-requirement g)))

      alloc₃ : AllocState {FS}
      alloc₃ = record alloc₂
        { next-slot = next-slot alloc₂ + pair-slots
        ; slots-available = pair-fits
        }

      s₃ = write-loc s₂ pair-loc fst-loc
      s₄ = write-loc s₃ (sucLoc pair-loc) snd-loc
      s-final = record s₄ { regs = writeReg (regs s₄) RAX pair-loc }

      -- PROVEN: Memory at BeforeFrontier locations is preserved
      mem-preserved-pair : ∀ loc → BeforeFrontier alloc loc →
        readLoc s-final loc ≡ readLoc s loc
      mem-preserved-pair loc bf =
        let
          bf₁ : BeforeFrontier alloc₁ loc
          bf₁ = frontier-monotone alloc alloc₁
                  (sym (IRResultAWF.frame-preserved result-f))
                  (IRResultAWF.slot-monotone result-f)
                  (IRResultAWF.heap-monotone result-f)
                  loc bf

          bf₂ : BeforeFrontier alloc₂ loc
          bf₂ = frontier-monotone alloc₁ alloc₂
                  (sym (IRResultAWF.frame-preserved result-g))
                  (IRResultAWF.slot-monotone result-g)
                  (IRResultAWF.heap-monotone result-g)
                  loc bf₁

          step1 : readLoc s-final loc ≡ readLoc s₄ loc
          step1 = readLoc-stackMem-eq s-final s₄ loc refl refl

          step2 : readLoc s₄ loc ≡ readLoc s₃ loc
          step2 = write-preserves-disjoint s₃ (sucLoc pair-loc) snd-loc loc
                    (λ eq → suc-frontier-neq-before alloc₂ loc bf₂ eq)

          step3 : readLoc s₃ loc ≡ readLoc s₂ loc
          step3 = write-preserves-disjoint s₂ pair-loc fst-loc loc
                    (λ eq → at-frontier-neq-before alloc₂ loc bf₂ eq)

          step4 : readLoc s₂ loc ≡ readLoc s₁-rdi loc
          step4 = IRResultAWF.mem-preserved-before result-g loc bf₁

          step5 : readLoc s₁-rdi loc ≡ readLoc s₁ loc
          step5 = readLoc-stackMem-eq s₁-rdi s₁ loc refl refl

          step6 : readLoc s₁ loc ≡ readLoc s loc
          step6 = IRResultAWF.mem-preserved-before result-f loc bf

        in trans step1 (trans step2 (trans step3 (trans step4 (trans step5 step6))))

      pair-before : BeforeFrontier alloc₃ pair-loc
      pair-before = stack-before refl (m<m+n (next-slot alloc₂) (s≤s z≤n))

      sucLoc-pair-before : BeforeFrontier alloc₃ (sucLoc pair-loc)
      sucLoc-pair-before = stack-before refl (suc<+2 (next-slot alloc₂))

      pair-ptr : readLoc s-final pair-loc ≡ just fst-loc
      pair-ptr = trans refl (trans
                   (write-preserves-disjoint s₃ (sucLoc pair-loc) snd-loc pair-loc (sucLoc-neq pair-loc))
                   (write-read-same s₂ pair-loc fst-loc))

      snd-ptr : readLoc s-final (sucLoc pair-loc) ≡ just snd-loc
      snd-ptr = write-read-same s₃ (sucLoc pair-loc) snd-loc

      fst-before-alloc₂ : BeforeFrontier alloc₂ fst-loc
      fst-before-alloc₂ = frontier-monotone alloc₁ alloc₂
                            (sym (IRResultAWF.frame-preserved result-g))
                            (IRResultAWF.slot-monotone result-g)
                            (IRResultAWF.heap-monotone result-g)
                            fst-loc fst-before

      fst-before₃ : BeforeFrontier alloc₃ fst-loc
      fst-before₃ = stack-alloc-advances alloc₂ pair-slots pair-fits fst-loc fst-before-alloc₂

      snd-before₃ : BeforeFrontier alloc₃ snd-loc
      snd-before₃ = stack-alloc-advances alloc₂ pair-slots pair-fits snd-loc snd-before

      -- PROVEN: fst-valid-wf-final via chained validity lemmas
      fst-valid-wf-final : ValidAtWF alloc₃ (eval f x) fst-loc s-final
      fst-valid-wf-final =
        let
          fst-valid-s₁-rdi : ValidAtWF alloc₁ (eval f x) fst-loc s₁-rdi
          fst-valid-s₁-rdi = validityWF-mem-only (eval f x) fst-loc s₁ s₁-rdi refl refl fst-valid-wf

          mem-eq-g : ∀ loc' → BeforeFrontier alloc₁ loc' → readLoc s₂ loc' ≡ readLoc s₁-rdi loc'
          mem-eq-g = IRResultAWF.mem-preserved-before result-g

          fst-valid-s₂-alloc₁ : ValidAtWF alloc₁ (eval f x) fst-loc s₂
          fst-valid-s₂-alloc₁ = validityWF-mem-preserved (eval f x) fst-loc s₁-rdi s₂ fst-before mem-eq-g fst-valid-s₁-rdi

          fst-valid-s₂ : ValidAtWF alloc₂ (eval f x) fst-loc s₂
          fst-valid-s₂ = validityWF-frontier-advance (eval f x) fst-loc s₂
                           (IRResultAWF.frame-preserved result-g)
                           (IRResultAWF.slot-monotone result-g)
                           (IRResultAWF.heap-monotone result-g)
                           fst-valid-s₂-alloc₁

          fst-valid-s₃ : ValidAtWF alloc₂ (eval f x) fst-loc s₃
          fst-valid-s₃ = validityWF-write-at-frontier (eval f x) fst-loc s₂ fst-loc fst-before-alloc₂ fst-valid-s₂

          fst-valid-s₄ : ValidAtWF alloc₂ (eval f x) fst-loc s₄
          fst-valid-s₄ = validityWF-write-at-suc-frontier (eval f x) fst-loc s₃ snd-loc fst-before-alloc₂ fst-valid-s₃

          fst-valid-s-final-alloc₂ : ValidAtWF alloc₂ (eval f x) fst-loc s-final
          fst-valid-s-final-alloc₂ = validityWF-mem-only (eval f x) fst-loc s₄ s-final refl refl fst-valid-s₄

        in validityWF-alloc-advance (eval f x) fst-loc s-final pair-slots pair-fits fst-valid-s-final-alloc₂

      -- PROVEN: snd-valid-wf-final via chained validity lemmas
      snd-valid-wf-final : ValidAtWF alloc₃ (eval g x) snd-loc s-final
      snd-valid-wf-final =
        let
          snd-valid-s₃ : ValidAtWF alloc₂ (eval g x) snd-loc s₃
          snd-valid-s₃ = validityWF-write-at-frontier (eval g x) snd-loc s₂ fst-loc snd-before snd-valid-wf

          snd-valid-s₄ : ValidAtWF alloc₂ (eval g x) snd-loc s₄
          snd-valid-s₄ = validityWF-write-at-suc-frontier (eval g x) snd-loc s₃ snd-loc snd-before snd-valid-s₃

          snd-valid-s-final-alloc₂ : ValidAtWF alloc₂ (eval g x) snd-loc s-final
          snd-valid-s-final-alloc₂ = validityWF-mem-only (eval g x) snd-loc s₄ s-final refl refl snd-valid-s₄

        in validityWF-alloc-advance (eval g x) snd-loc s-final pair-slots pair-fits snd-valid-s-final-alloc₂

      pair-valid-wf : ValidAtWF alloc₃ (eval ⟨ f , g ⟩ x) pair-loc s-final
      pair-valid-wf = valid-pair-wf pair-ptr snd-ptr fst-before₃ snd-before₃ sucLoc-pair-before fst-valid-wf-final snd-valid-wf-final

      rax-eq : readReg (regs s-final) RAX ≡ pair-loc
      rax-eq = writeReg-same (regs s₄) RAX pair-loc
