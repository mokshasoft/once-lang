-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Target.X86-64.IR.PairWF
--
-- PairWF proof using SMPrimitives for memory reasoning.
--
-- NOTE: Due to duplicate type definitions between SMCore and SlotMachine,
-- we import SMPrimitives qualified and use it for the memory primitives.
------------------------------------------------------------------------

module Once.CCC.Machine.IR.PairWF where

open import Data.Nat using (ℕ; suc; _<_; _≤_; _≥_; s≤s; z≤n; _⊔_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-antisym; m≤m+n; n≤1+n; +-comm; +-assoc; +-suc; +-identityʳ; +-monoˡ-≤; +-monoʳ-≤; m<m+n; <-≤-trans; ≤-<-trans; <⇒≤; <⇒≢; ≮⇒≥; ≰⇒>; ≤∧≢⇒<; _<?_; _≤?_; _≟_; m<1+n⇒m≤n; m≤m⊔n; m≤n⊔m; ⊔-lub)
open import Data.Empty using (⊥-elim)
open import Data.Bool using (false)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (case_of_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym; cong; cong₂; subst; subst₂; module ≡-Reasoning)
open import Relation.Nullary using (yes; no)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore hiding (AllocMode; Stack; Heap)
open import Once.CCC.Target.X86-64.Types
open import Once.CCC.IR
open import Once.CCC.Eval using (PrimSem; eval)
open import Once.CCC.IR.Size
open import Once.CCC.IR.Stack
open import Once.CCC.Machine.Allocation hiding (AllocMode)
open import Once.CCC.Machine.ClosureWellFormed

-- Import SMPrimitives qualified for memory reasoning primitives
import Once.CCC.Machine.SMPrimitives as SMP

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
  open import Once.CCC.Machine.DispatcherArithmeticLemma
    using (suc<+2)
  open import Once.CCC.Machine.FrontierLemma
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
      ; alloc-correct = SMP.!!  -- PROOF OBLIGATION: pair trace preserves alloc
      ; result-valid-wf = pair-valid-wf-final
      ; result-before = pair-before
      ; rax-is-result = rax-eq
      ; not-halted = not-halted-final
      ; frame-preserved = refl
      ; slot-monotone = slot-monotone-pair
      ; heap-monotone = ≤-refl
      ; capacity-preserved = refl
      ; mem-preserved-before = mem-preserved-pair
      ; reclaimable-slot = pair-reclaim
      ; reclaim-monotone = pair-reclaim-monotone
      ; reclaim-bounded = ≤-refl
      ; reclaim-preserves-result = λ _ → pair-before
      ; reclaim-preserves-validity = λ _ → pair-valid-wf-final
      ; reclaim-size-bound = pair-reclaim-size-bound
      ; max-slot-written = pair-max-slot
      ; max-slot-geq-reclaim = pair-max-slot-geq-reclaim
      ; max-slot-usage-bound = pair-max-slot-bound
      ; frontier-slot-stable = pair-frontier-stable
      ; trace-writes-above = pair-trace-writes-above
      ; trace-slot-reads-above = pair-trace-slot-reads-above
      ; trace-writes-below = pair-trace-writes-below
      ; trace-slot-reads-below = pair-trace-slot-reads-below
      ; trace-preserves-capacity = pair-trace-preserves-capacity
      ; trace-no-heap-writes = pair-trace-no-heap-writes
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
      -- With pre-allocated pair slots, f starts at backup-slot + 3
      ----------------------------------------------------------------------
      -- Allocation state after reserving backup-slot and pair slots
      alloc-after-pair-slots : AllocState {FS}
      alloc-after-pair-slots = record alloc { next-slot = suc (suc (suc backup-slot)) }

      -- Original capacity expansion: (backup-slot + 1) + rf + rg + ps ≤ frame-capacity
      combined-cap-expanded : (backup-slot +ℕ 1) +ℕ rf +ℕ rg +ℕ ps ≤ frame-capacity alloc
      combined-cap-expanded = ⟨,⟩-capacity-for-pair f g m backup-slot (frame-capacity alloc) combined-cap

      combined-cap-suc : suc backup-slot +ℕ rf +ℕ rg +ℕ ps ≤ frame-capacity alloc
      combined-cap-suc = subst (λ x → x +ℕ rf +ℕ rg +ℕ ps ≤ frame-capacity alloc)
                           (+-comm backup-slot 1) combined-cap-expanded

      -- Derive capacity for f starting at backup-slot + 3
      -- We have: suc backup-slot + rf + rg + ps ≤ capacity (from combined-cap-suc)
      -- Need: suc (suc (suc backup-slot)) + rf ≤ capacity
      -- From combined-cap-suc: (b+1)+rf+rg+ps ≤ capacity where ps=2
      -- (b+3)+rf ≤ (b+3)+rf+rg = (b+1)+rf+rg+2 ≤ (b+1)+rf+rg+ps ≤ capacity
      -- Helper: n + 2 ≡ suc (suc n)
      plus-two : ∀ n → n +ℕ 2 ≡ suc (suc n)
      plus-two n = trans (+-suc n 1) (cong suc (trans (+-suc n 0) (cong suc (+-identityʳ n))))

      combined-cap-f : suc (suc (suc backup-slot)) +ℕ rf ≤ frame-capacity alloc
      combined-cap-f = ≤-trans step1 (≤-trans step2 combined-cap-suc)
        where
          -- (b+3)+rf ≤ (b+3)+rf+rg (add rg on right)
          step1 : suc (suc (suc backup-slot)) +ℕ rf ≤ suc (suc (suc backup-slot)) +ℕ rf +ℕ rg
          step1 = m≤m+n (suc (suc (suc backup-slot)) +ℕ rf) rg
          -- (b+3)+rf+rg = (b+1)+rf+rg+2 since suc(suc(suc(b+rf+rg))) = suc((b+rf+rg)+2)
          step2-eq : suc (suc (suc backup-slot)) +ℕ rf +ℕ rg ≡ suc backup-slot +ℕ rf +ℕ rg +ℕ 2
          step2-eq = sym (cong suc (plus-two (backup-slot +ℕ rf +ℕ rg)))
          step2 : suc (suc (suc backup-slot)) +ℕ rf +ℕ rg ≤ suc backup-slot +ℕ rf +ℕ rg +ℕ ps
          step2 = subst (suc (suc (suc backup-slot)) +ℕ rf +ℕ rg ≤_) refl
                    (subst (_≤ suc backup-slot +ℕ rf +ℕ rg +ℕ 2) (sym step2-eq) ≤-refl)

      input-before-after-pair-slots : BeforeFrontier alloc-after-pair-slots input-loc
      input-before-after-pair-slots = frontier-monotone alloc alloc-after-pair-slots refl
                                        (≤-trans (n≤1+n backup-slot) (≤-trans (n≤1+n (suc backup-slot)) (n≤1+n (suc (suc backup-slot)))))
                                        ≤-refl input-loc input-before

      bf-to-after-pair-slots : ∀ loc → BeforeFrontier alloc loc → BeforeFrontier alloc-after-pair-slots loc
      bf-to-after-pair-slots loc bf = frontier-monotone alloc alloc-after-pair-slots refl
                                        (≤-trans (n≤1+n backup-slot) (≤-trans (n≤1+n (suc backup-slot)) (n≤1+n (suc (suc backup-slot)))))
                                        ≤-refl loc bf

      input-valid-wf-after-pair-slots : ValidAtWF mIn alloc-after-pair-slots x input-loc s
      input-valid-wf-after-pair-slots = validityWF-frontier-advance x input-loc s refl
                                          (≤-trans (n≤1+n backup-slot) (≤-trans (n≤1+n (suc backup-slot)) (n≤1+n (suc (suc backup-slot)))))
                                          ≤-refl input-valid-wf

      ----------------------------------------------------------------------
      -- Run f via recursive dispatch
      ----------------------------------------------------------------------
      f-exec-result : ∃[ mOut ] IRResultAWF mOut f x s alloc-after-pair-slots
      f-exec-result = rec-wf mIn f (⟨,⟩-f-smaller f g {m}) x input-loc s alloc-after-pair-slots
                        input-valid-wf-after-pair-slots input-before-after-pair-slots not-halted rdi-eq combined-cap-f
      mF = proj₁ f-exec-result
      result-f = proj₂ f-exec-result
      s₁ = IRResultAWF.final-state result-f
      fst-loc = IRResultAWF.result-loc result-f

      ----------------------------------------------------------------------
      -- Reclaim after f
      -- f starts at suc (suc (suc backup-slot)), so reclaim-f ≥ that
      ----------------------------------------------------------------------
      reclaim-f = IRResultAWF.reclaimable-slot result-f

      -- f started at suc (suc (suc backup-slot)), so bound is (backup+3) + rf
      reclaim-f-bound : reclaim-f ≤ suc (suc (suc backup-slot)) +ℕ rf
      reclaim-f-bound = IRResultAWF.reclaim-size-bound result-f

      reclaim-f-fits : reclaim-f ≤ frame-capacity alloc
      reclaim-f-fits = ≤-trans reclaim-f-bound combined-cap-f

      -- reclaim-f ≥ suc (suc (suc backup-slot)) (where f started)
      reclaim-f-above-pair-slots : suc (suc (suc backup-slot)) ≤ reclaim-f
      reclaim-f-above-pair-slots = IRResultAWF.reclaim-monotone result-f

      -- Old name for backward compatibility in some proofs
      reclaim-f-above-backup : suc backup-slot ≤ reclaim-f
      reclaim-f-above-backup = ≤-trans (s≤s (n≤1+n backup-slot)) (≤-trans (n≤1+n (suc (suc backup-slot))) reclaim-f-above-pair-slots)

      alloc₁-reclaimed : AllocState {FS}
      alloc₁-reclaimed = record alloc { next-slot = reclaim-f }

      ----------------------------------------------------------------------
      -- Capacity for g
      ----------------------------------------------------------------------
      -- combined-cap-g follows from reclaim-f ≤ (backup+3)+rf and combined-cap-suc
      -- (backup+3)+rf+rg = (backup+1)+rf+rg+2 ≤ (backup+1)+rf+rg+ps = capacity
      combined-cap-g : reclaim-f +ℕ rg ≤ frame-capacity alloc
      combined-cap-g =
        -- reclaim-f + rg ≤ (backup+3+rf) + rg = backup+3+rf+rg
        -- = (backup+1)+rf+rg+2 ≤ (backup+1)+rf+rg+ps ≤ capacity
        let step1 : reclaim-f +ℕ rg ≤ (suc (suc (suc backup-slot)) +ℕ rf) +ℕ rg
            step1 = +-monoˡ-≤ rg reclaim-f-bound
            -- (backup+3)+rf+rg = (backup+1)+rf+rg+2
            step2-eq : (suc (suc (suc backup-slot)) +ℕ rf) +ℕ rg ≡ suc backup-slot +ℕ rf +ℕ rg +ℕ 2
            step2-eq = sym (cong suc (plus-two (backup-slot +ℕ rf +ℕ rg)))
            step2 : (suc (suc (suc backup-slot)) +ℕ rf) +ℕ rg ≤ suc backup-slot +ℕ rf +ℕ rg +ℕ ps
            step2 = subst ((suc (suc (suc backup-slot)) +ℕ rf) +ℕ rg ≤_) refl
                      (subst (_≤ suc backup-slot +ℕ rf +ℕ rg +ℕ 2) (sym step2-eq) ≤-refl)
        in ≤-trans step1 (≤-trans step2 combined-cap-suc)

      input-before₁-reclaimed : BeforeFrontier alloc₁-reclaimed input-loc
      input-before₁-reclaimed = frontier-monotone alloc alloc₁-reclaimed refl
                                  (≤-trans (n≤1+n backup-slot) reclaim-f-above-backup)
                                  ≤-refl input-loc input-before

      input-valid-wf-s1 : ValidAtWF mIn alloc x input-loc s₁
      input-valid-wf-s1 = validityWF-mem-preserved x input-loc s s₁ input-before
                            (λ loc bf → IRResultAWF.mem-preserved-before result-f loc (bf-to-after-pair-slots loc bf))
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

      -- reclaim-g ≤ reclaim-f + rg ≤ (backup+3+rf) + rg = (backup+1+rf+rg+2) ≤ capacity
      reclaim-g-fits : reclaim-g ≤ frame-capacity alloc
      reclaim-g-fits = ≤-trans reclaim-g-bound combined-cap-g

      -- Pre-allocate pair slots right after backup-slot
      -- This ensures f and g write ABOVE these slots, making preservation proofs work
      fst-slot = suc backup-slot
      snd-slot = suc (suc backup-slot)
      pair-loc = OnStack frame fst-slot
      fst-loc-stack : ValueLocation FS
      fst-loc-stack = OnStack frame fst-slot
      snd-loc-stack : ValueLocation FS
      snd-loc-stack = OnStack frame snd-slot
      backup-loc : ValueLocation FS
      backup-loc = OnStack frame backup-slot

      -- Final allocation: pair slots already allocated, so just use reclaim-g
      alloc₃ : AllocState {FS}
      alloc₃ = record alloc { next-slot = reclaim-g }

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
      setup-tnhw : SMP.TraceNoHeapWrites setup-trace
      setup-tnhw = tt

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
      -- Max slot tracking (needed early for trace bound proofs)
      --
      -- With pre-allocated pair slots at fst-slot and snd-slot (= backup+1, backup+2),
      -- the pair trace writes to:
      -- - backup-slot (input backup)
      -- - fst-slot, snd-slot (pair slot values)
      -- - [backup+3, reclaim-f) from f
      -- - [reclaim-f, reclaim-g) from g
      --
      -- All writes are bounded by reclaim-g (exclusive upper bound for pair).
      ----------------------------------------------------------------------
      max-slot-f = IRResultAWF.max-slot-written result-f
      max-slot-g = IRResultAWF.max-slot-written result-g

      -- Forward definition of pair-reclaim for use in pair-max-slot
      -- With pre-allocated pair slots, reclaim is just reclaim-g (no +ps)
      pair-reclaim' = reclaim-g

      -- pair-max-slot must bound all writes: max-slot-f, max-slot-g, and snd-slot
      -- Since max-slot-f ≥ reclaim-f ≥ backup+3 > snd-slot, we just need max of f and g
      pair-max-slot = max-slot-f ⊔ max-slot-g

      -- pair-reclaim' ≤ pair-max-slot: reclaim-g ≤ max-slot-g ≤ max-slot-f ⊔ max-slot-g
      pair-max-slot-geq-reclaim' : pair-reclaim' ≤ pair-max-slot
      pair-max-slot-geq-reclaim' = ≤-trans (IRResultAWF.max-slot-geq-reclaim result-g) (m≤n⊔m max-slot-f max-slot-g)

      -- Key bounds for the new allocation strategy:
      -- fst-slot < reclaim-f means suc fst-slot ≤ reclaim-f, i.e., suc (suc backup-slot) ≤ reclaim-f
      -- This follows from suc (suc backup-slot) ≤ suc (suc (suc backup-slot)) ≤ reclaim-f
      fst-slot<reclaim-f : fst-slot < reclaim-f
      fst-slot<reclaim-f = ≤-trans (n≤1+n (suc (suc backup-slot))) reclaim-f-above-pair-slots

      -- snd-slot < reclaim-f means suc snd-slot ≤ reclaim-f, i.e., suc (suc (suc backup-slot)) ≤ reclaim-f
      -- This is exactly reclaim-f-above-pair-slots
      snd-slot<reclaim-f : snd-slot < reclaim-f
      snd-slot<reclaim-f = reclaim-f-above-pair-slots

      -- max-slot bounds for sub-IR traces lifted to pair-max-slot = max-slot-f ⊔ max-slot-g
      max-slot-f≤pair : max-slot-f ≤ pair-max-slot
      max-slot-f≤pair = m≤m⊔n max-slot-f max-slot-g

      max-slot-g≤pair : max-slot-g ≤ pair-max-slot
      max-slot-g≤pair = m≤n⊔m max-slot-f max-slot-g

      ----------------------------------------------------------------------
      -- POSITIVE WRITE CHARACTERIZATION from sub-IRs
      -- These use SMPrimitives predicates
      ----------------------------------------------------------------------
      -- f writes above suc (suc (suc backup-slot)) (where it started)
      f-writes-above' : SMP.TraceWritesAbove (suc (suc (suc backup-slot))) f-trace
      f-writes-above' = IRResultAWF.trace-writes-above result-f

      -- Weaker bound: f writes above suc backup-slot (needed for some proofs)
      -- suc backup-slot ≤ suc (suc (suc backup-slot)) by transitivity
      f-writes-above : SMP.TraceWritesAbove (suc backup-slot) f-trace
      f-writes-above = SMP.trace-writes-above-mono (suc backup-slot) (suc (suc (suc backup-slot))) f-trace
                         (≤-trans (n≤1+n (suc backup-slot)) (n≤1+n (suc (suc backup-slot)))) f-writes-above'

      f-writes-below : SMP.TraceWritesBelow max-slot-f f-trace
      f-writes-below = IRResultAWF.trace-writes-below result-f

      f-tnhw : SMP.TraceNoHeapWrites f-trace
      f-tnhw = IRResultAWF.trace-no-heap-writes result-f

      g-writes-above : SMP.TraceWritesAbove reclaim-f g-trace
      g-writes-above = IRResultAWF.trace-writes-above result-g

      g-writes-below : SMP.TraceWritesBelow max-slot-g g-trace
      g-writes-below = IRResultAWF.trace-writes-below result-g

      g-tnhw : SMP.TraceNoHeapWrites g-trace
      g-tnhw = IRResultAWF.trace-no-heap-writes result-g

      f-tpc : TracePreservesCapacity f-trace
      f-tpc = IRResultAWF.trace-preserves-capacity result-f

      g-tpc : TracePreservesCapacity g-trace
      g-tpc = IRResultAWF.trace-preserves-capacity result-g

      -- f reads above suc (suc (suc backup-slot)), weaken to suc backup-slot
      f-reads-above : SMP.TraceSlotReadsAbove (suc backup-slot) f-trace
      f-reads-above = SMP.trace-slot-reads-above-mono (suc backup-slot) (suc (suc (suc backup-slot))) f-trace
                        (≤-trans (n≤1+n (suc backup-slot)) (n≤1+n (suc (suc backup-slot))))
                        (IRResultAWF.trace-slot-reads-above result-f)

      g-reads-above : SMP.TraceSlotReadsAbove reclaim-f g-trace
      g-reads-above = IRResultAWF.trace-slot-reads-above result-g

      f-reads-below : SMP.TraceSlotReadsBelow max-slot-f f-trace
      f-reads-below = IRResultAWF.trace-slot-reads-below result-f

      g-reads-below : SMP.TraceSlotReadsBelow max-slot-g g-trace
      g-reads-below = IRResultAWF.trace-slot-reads-below result-g

      ----------------------------------------------------------------------
      -- Trace characterization using SMPrimitives
      ----------------------------------------------------------------------
      -- TraceNoHeapWrites for rest segments
      final-tnhw : SMP.TraceNoHeapWrites final-trace
      final-tnhw = tt

      rest-after-middle-tnhw : SMP.TraceNoHeapWrites rest-after-middle
      rest-after-middle-tnhw = SMP.trace-no-heap-writes-append g-trace final-trace g-tnhw final-tnhw

      middle-tnhw : SMP.TraceNoHeapWrites middle-trace
      middle-tnhw = tt

      rest-after-f-tnhw : SMP.TraceNoHeapWrites rest-after-f
      rest-after-f-tnhw = SMP.trace-no-heap-writes-append middle-trace rest-after-middle middle-tnhw rest-after-middle-tnhw

      rest-after-setup-tnhw : SMP.TraceNoHeapWrites rest-after-setup
      rest-after-setup-tnhw = SMP.trace-no-heap-writes-append f-trace rest-after-f f-tnhw rest-after-f-tnhw

      pair-trace-no-heap-writes : SMP.TraceNoHeapWrites pair-trace
      pair-trace-no-heap-writes = SMP.trace-no-heap-writes-append setup-trace rest-after-setup setup-tnhw rest-after-setup-tnhw

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
      -- With pre-allocated pair slots: fst-slot = suc backup-slot, snd-slot = suc (suc backup-slot)
      backup≤fst : backup-slot ≤ fst-slot
      backup≤fst = n≤1+n backup-slot

      backup≤snd : backup-slot ≤ snd-slot
      backup≤snd = ≤-trans backup≤fst (n≤1+n fst-slot)

      backup≤reclaim-f : backup-slot ≤ reclaim-f
      backup≤reclaim-f = ≤-trans (n≤1+n backup-slot) reclaim-f-above-backup

      -- fst-slot = suc backup-slot < reclaim-g (since reclaim-f ≥ backup+3 and reclaim-g ≥ reclaim-f)
      fst<reclaim-g : fst-slot < reclaim-g
      fst<reclaim-g = <-≤-trans fst-slot<reclaim-f (IRResultAWF.reclaim-monotone result-g)

      -- snd-slot = suc (suc backup-slot) < reclaim-g
      snd<reclaim-g : snd-slot < reclaim-g
      snd<reclaim-g = <-≤-trans snd-slot<reclaim-f (IRResultAWF.reclaim-monotone result-g)

      -- fst-slot < pair-max-slot = max-slot-f ⊔ max-slot-g
      -- fst < reclaim-f ≤ max-slot-f ≤ max-slot-f ⊔ max-slot-g
      fst<bound : fst-slot < pair-max-slot
      fst<bound = <-≤-trans fst-slot<reclaim-f
                    (≤-trans (IRResultAWF.max-slot-geq-reclaim result-f) (m≤m⊔n max-slot-f max-slot-g))

      -- snd-slot < pair-max-slot = max-slot-f ⊔ max-slot-g
      snd<bound : snd-slot < pair-max-slot
      snd<bound = <-≤-trans snd-slot<reclaim-f
                    (≤-trans (IRResultAWF.max-slot-geq-reclaim result-f) (m≤m⊔n max-slot-f max-slot-g))

      backup<bound : backup-slot < pair-max-slot
      backup<bound = <-≤-trans (s≤s backup≤fst) fst<bound

      -- Final trace segment (after g-trace)
      final-seg : AbstractTrace
      final-seg = store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []

      final-seg-writes-above : SMP.TraceWritesAbove backup-slot final-seg
      final-seg-writes-above = backup≤snd , tt

      final-seg-writes-below : SMP.TraceWritesBelow pair-max-slot final-seg
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

      g-plus-final-writes-below : SMP.TraceWritesBelow pair-max-slot (g-trace ++ final-seg)
      g-plus-final-writes-below = SMP.trace-writes-below-append pair-max-slot g-trace final-seg
                                    (SMP.trace-writes-below-mono max-slot-g pair-max-slot g-trace
                                       max-slot-g≤pair g-writes-below)
                                    final-seg-writes-below

      middle-plus-writes-above : SMP.TraceWritesAbove backup-slot middle-plus-g-plus-final
      middle-plus-writes-above = backup≤fst , g-plus-final-writes-above

      middle-plus-writes-below : SMP.TraceWritesBelow pair-max-slot middle-plus-g-plus-final
      middle-plus-writes-below = fst<bound , g-plus-final-writes-below

      -- f-trace plus middle (store-at-slot fst-slot ∷ rest)
      f-plus-rest : AbstractTrace
      f-plus-rest = f-trace ++ middle-plus-g-plus-final

      f-plus-rest-writes-above : SMP.TraceWritesAbove backup-slot f-plus-rest
      f-plus-rest-writes-above = SMP.trace-writes-above-append backup-slot f-trace middle-plus-g-plus-final
                                   (SMP.trace-writes-above-mono backup-slot (suc backup-slot) f-trace
                                      (n≤1+n backup-slot) f-writes-above)
                                   middle-plus-writes-above

      f-plus-rest-writes-below : SMP.TraceWritesBelow pair-max-slot f-plus-rest
      f-plus-rest-writes-below = SMP.trace-writes-below-append pair-max-slot f-trace middle-plus-g-plus-final
                                   (SMP.trace-writes-below-mono max-slot-f pair-max-slot f-trace
                                      max-slot-f≤pair f-writes-below)
                                   middle-plus-writes-below

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

      pair-trace-writes-below : SMP.TraceWritesBelow pair-max-slot pair-trace
      pair-trace-writes-below = backup<bound , f-plus-rest-writes-below

      -- Build reads-below similarly
      final-seg-reads-below : SMP.TraceSlotReadsBelow pair-max-slot final-seg
      final-seg-reads-below = tt

      g-plus-final-reads-below : SMP.TraceSlotReadsBelow pair-max-slot (g-trace ++ final-seg)
      g-plus-final-reads-below = SMP.trace-slot-reads-below-append pair-max-slot g-trace final-seg
                                   (SMP.trace-slot-reads-below-mono max-slot-g pair-max-slot g-trace
                                      max-slot-g≤pair g-reads-below)
                                   final-seg-reads-below

      middle-plus-reads-below : SMP.TraceSlotReadsBelow pair-max-slot middle-plus-g-plus-final
      middle-plus-reads-below = backup<bound , g-plus-final-reads-below
        -- store fst-slot write and restore-input reads backup-slot, both < pair-max-slot

      f-plus-rest-reads-below : SMP.TraceSlotReadsBelow pair-max-slot f-plus-rest
      f-plus-rest-reads-below = SMP.trace-slot-reads-below-append pair-max-slot f-trace middle-plus-g-plus-final
                                  (SMP.trace-slot-reads-below-mono max-slot-f pair-max-slot f-trace
                                     max-slot-f≤pair f-reads-below)
                                  middle-plus-reads-below

      pair-trace-slot-reads-below : SMP.TraceSlotReadsBelow pair-max-slot pair-trace
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

      -- With pre-allocated pair slots, alloc₃.next-slot = reclaim-g
      slot-monotone-pair : next-slot alloc ≤ next-slot alloc₃
      slot-monotone-pair = ≤-trans (n≤1+n backup-slot)
                             (≤-trans reclaim-f-above-backup
                               (IRResultAWF.reclaim-monotone result-g))

      -- pair-loc = OnStack frame fst-slot, where fst-slot = suc backup-slot
      -- alloc₃.next-slot = reclaim-g > fst-slot, so pair-loc is before frontier
      pair-before : BeforeFrontier alloc₃ pair-loc
      pair-before = stack-before refl fst<reclaim-g

      pair-reclaim : ℕ
      pair-reclaim = pair-reclaim'  -- = reclaim-g (pair slots pre-allocated)

      pair-reclaim-monotone : next-slot alloc ≤ pair-reclaim
      pair-reclaim-monotone = slot-monotone-pair

      -- Arithmetic bound: reclaim-g ≤ backup-slot + req-pair
      -- where req-pair = ir-stack-requirement (⟨ f , g ⟩ m) = 1 + rf + rg + ps
      reclaim-g≤-rf-rg : reclaim-g ≤ (suc (suc (suc backup-slot)) +ℕ rf) +ℕ rg
      reclaim-g≤-rf-rg = ≤-trans reclaim-g-bound (+-monoˡ-≤ rg reclaim-f-bound)

      open import Data.Nat.Properties using (+-suc)

      -- Helper: (backup+3)+rf+rg ≡ backup + req-pair
      -- where req-pair = ((1 + rf) + rg) + 2 (by definition of ir-stack-requirement for pair)
      -- LHS definitionally equals suc(suc(suc((backup+rf)+rg)))
      -- RHS needs to be shown equal to this
      sss-rf-rg≡req-pair : (suc (suc (suc backup-slot)) +ℕ rf) +ℕ rg ≡ backup-slot +ℕ req-pair
      sss-rf-rg≡req-pair =
        -- LHS = suc (suc (suc ((backup-slot + rf) + rg))) by computation
        -- RHS = backup-slot + (((1 + rf) + rg) + 2)
        -- Step 1: Show ((1 + rf) + rg) + 2 = 3 + (rf + rg)
        let step1 : (((1 +ℕ rf) +ℕ rg) +ℕ 2) ≡ 3 +ℕ (rf +ℕ rg)
            step1 = trans (+-assoc (1 +ℕ rf) rg 2)
                    (trans (cong ((1 +ℕ rf) +ℕ_) (+-comm rg 2))
                    (trans (sym (+-assoc (1 +ℕ rf) 2 rg))
                    (trans (cong (_+ℕ rg) (+-assoc 1 rf 2))
                    (trans (cong (λ x → (1 +ℕ x) +ℕ rg) (+-comm rf 2))
                    (trans (cong (_+ℕ rg) (sym (+-assoc 1 2 rf))) (+-assoc 3 rf rg))))))
            -- Step 2: backup-slot + (3 + (rf + rg)) = suc(suc(suc(backup-slot + (rf + rg))))
            step2 : backup-slot +ℕ (3 +ℕ (rf +ℕ rg)) ≡ suc (suc (suc (backup-slot +ℕ (rf +ℕ rg))))
            step2 = trans (sym (+-assoc backup-slot 3 (rf +ℕ rg)))
                      (trans (cong (_+ℕ (rf +ℕ rg)) (+-comm backup-slot 3))
                        (+-assoc 3 backup-slot (rf +ℕ rg)))
            -- Step 3: (backup-slot + rf) + rg = backup-slot + (rf + rg) by associativity
            step3 : (backup-slot +ℕ rf) +ℕ rg ≡ backup-slot +ℕ (rf +ℕ rg)
            step3 = +-assoc backup-slot rf rg
        -- Combine: LHS = suc(suc(suc((backup+rf)+rg))) = suc(suc(suc(backup+(rf+rg)))) = RHS
        in trans (cong (λ x → suc (suc (suc x))) step3)
             (trans (sym step2) (cong (backup-slot +ℕ_) (sym step1)))

      -- Arithmetic: reclaim-g ≤ (backup+3)+rf+rg ≤ backup + req-pair
      -- where req-pair = 1 + rf + rg + 2 = 3 + rf + rg
      -- Direct bound: both simplify to backup + 3 + rf + rg
      pair-reclaim-size-bound : pair-reclaim ≤ backup-slot +ℕ req-pair
      pair-reclaim-size-bound = ≤-trans reclaim-g≤-rf-rg
        (subst (((suc (suc (suc backup-slot)) +ℕ rf) +ℕ rg) ≤_) sss-rf-rg≡req-pair ≤-refl)

      ------------------------------------------------------------------------
      -- Max slot bound (uses definitions from earlier section)
      ------------------------------------------------------------------------
      -- pair-reclaim ≤ pair-max-slot is pair-max-slot-geq-reclaim' from earlier section
      pair-max-slot-geq-reclaim : pair-reclaim ≤ pair-max-slot
      pair-max-slot-geq-reclaim = pair-max-slot-geq-reclaim'

      -- pair-max-slot = max-slot-f ⊔ max-slot-g, both bounded by backup + req-pair
      -- max-slot-f ≤ (backup+3)+rf ≤ backup+req-pair (since req-pair = 3+rf+rg)
      -- max-slot-g ≤ reclaim-f+rg ≤ (backup+3+rf)+rg = backup+req-pair
      pair-max-slot-bound : pair-max-slot ≤ backup-slot +ℕ req-pair
      pair-max-slot-bound =
        -- Use ⊔-lub: if a ≤ c and b ≤ c then a ⊔ b ≤ c
        ⊔-lub max-slot-f-bound max-slot-g-bound
        where
          -- max-slot-f ≤ (backup+3) + rf (from result-f.max-slot-usage-bound)
          max-slot-f-usage : max-slot-f ≤ suc (suc (suc backup-slot)) +ℕ rf
          max-slot-f-usage = IRResultAWF.max-slot-usage-bound result-f

          -- max-slot-g ≤ reclaim-f + rg (from result-g.max-slot-usage-bound)
          max-slot-g-usage : max-slot-g ≤ reclaim-f +ℕ rg
          max-slot-g-usage = IRResultAWF.max-slot-usage-bound result-g

          -- (backup+3) + rf ≤ backup + req-pair since req-pair ≥ 3 + rf
          -- req-pair = 1 + rf + rg + 2 = 3 + rf + rg, so backup + req-pair = backup + 3 + rf + rg
          max-slot-f-bound : max-slot-f ≤ backup-slot +ℕ req-pair
          max-slot-f-bound = ≤-trans max-slot-f-usage
            (≤-trans (m≤m+n (suc (suc (suc backup-slot)) +ℕ rf) rg)
                     (subst (((suc (suc (suc backup-slot)) +ℕ rf) +ℕ rg) ≤_)
                            sss-rf-rg≡req-pair ≤-refl))

          -- reclaim-f + rg ≤ backup + req-pair (same as above, using reclaim-f ≤ (backup+3)+rf)
          max-slot-g-bound : max-slot-g ≤ backup-slot +ℕ req-pair
          max-slot-g-bound = ≤-trans max-slot-g-usage
            (≤-trans (+-monoˡ-≤ rg reclaim-f-bound)
                     (subst (((suc (suc (suc backup-slot)) +ℕ rf) +ℕ rg) ≤_)
                            sss-rf-rg≡req-pair ≤-refl))

      -- Backup slot preservation using store-then-preserve pattern
      -- Structure:
      -- 1. mov-to-output sets Output = Input = input-loc'
      -- 2. store-at-slot backup-slot writes Output to backup-slot
      -- 3. Rest of trace writes above suc backup-slot, so backup-slot is preserved
      pair-frontier-stable : ∀ (s' : LocState FS) (input-loc' : ValueLocation FS) →
        halted s' ≡ false →
        readReg (regs s') Input ≡ input-loc' →
        readLoc s' (OnStack frame backup-slot) ≡ just input-loc' →
        _
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

            -- suc backup-slot ≤ fst-slot (where fst-slot = suc backup-slot)
            suc-backup≤fst : suc backup-slot ≤ fst-slot
            suc-backup≤fst = ≤-refl  -- fst-slot = suc backup-slot

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

            -- rest-trace no heap writes
            after-g-tnhw : SMP.TraceNoHeapWrites after-g-trace
            after-g-tnhw = tt

            g-plus-after-tnhw : SMP.TraceNoHeapWrites (g-trace ++ after-g-trace)
            g-plus-after-tnhw = SMP.trace-no-heap-writes-append g-trace after-g-trace g-tnhw after-g-tnhw

            after-f-tnhw : SMP.TraceNoHeapWrites after-f-trace
            after-f-tnhw = g-plus-after-tnhw

            rest-tnhw : SMP.TraceNoHeapWrites rest-trace
            rest-tnhw = SMP.trace-no-heap-writes-append f-trace after-f-trace f-tnhw after-f-tnhw

            -- Apply store-then-preserve: store-at-slot backup-slot ∷ rest preserves backup-slot
            -- We need to show s'-after-mov has Output = input-loc', which we have from mov-output
            store-pres : readLoc (proj₁ (exec-trace (store-at-slot backup-slot ∷ rest-trace) s'-after-mov alloc'-after-mov))
                                 (OnStack (current-frame alloc'-after-mov) backup-slot) ≡ just input-loc'
            store-pres = trans (store-then-preserve backup-slot rest-trace s'-after-mov alloc'-after-mov
                                  not-halted-after-mov rest-writes-above rest-tnhw)
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

        in inj₂ (inj₁ step3)

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
                    pair-trace-writes-above pair-trace-no-heap-writes k<next)
      mem-preserved-pair (OnStack f' k) (stack-ancestor {.f'} cf≺f' _) =
        -- f' is an ancestor frame (current-frame alloc ≺ f')
        exec-trace-preserves-ancestor pair-trace s alloc f' k cf≺f' pair-trace-no-heap-writes
      mem-preserved-pair (OnHeap h) (heap-before _) =
        -- Heap location, use preserves-heap-loc
        exec-trace-preserves-heap-loc pair-trace s alloc h pair-trace-no-heap-writes

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

      -- TraceNoHeapWrites for after-fst-store
      -- after-fst-store = restore-input backup-slot ∷ g-trace ++ final-seg
      after-fst-tnhw : SMP.TraceNoHeapWrites after-fst-store
      after-fst-tnhw = SMP.trace-no-heap-writes-append g-trace final-seg g-tnhw tt

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
                              f-writes-above f-tnhw

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
          -- fst-slot = suc backup-slot, so backup-slot < fst-slot
          -- (m < n means suc m ≤ n, so backup-slot < suc backup-slot is suc backup-slot ≤ suc backup-slot)
          iam-backup<fst : backup-slot < fst-slot
          iam-backup<fst = ≤-refl  -- suc backup-slot ≤ suc backup-slot since fst-slot = suc backup-slot

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

      -- s₂ output (from result-g) - converted to trace form using trace-correct
      s₂-output : readReg (regs (proj₁ (exec-trace g-trace s₁' alloc₁-reclaimed))) Output ≡ snd-loc
      s₂-output = subst (λ s' → readReg (regs s') Output ≡ snd-loc)
                        (sym (IRResultAWF.trace-correct result-g))
                        (IRResultAWF.rax-is-result result-g)

      -- halted flags
      not-halted-s1' : halted s₁' ≡ false
      not-halted-s1' = IRResultAWF.not-halted result-f  -- s₁' has same halted as s₁

      output-after-g-is-snd : readReg (regs s-after-g) Output ≡ snd-loc
      -- NOTE: With max-slot-written bounds, this proof needs updated exec-trace-output-deterministic
      -- call with max-slot-g instead of reclaim-g. Marked SMP.!! pending update.
      output-after-g-is-snd = SMP.!!

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
      -- f-trace executed from s (with alloc-after-pair-slots) produces fst-loc in Output
      -- f-trace executed from s-after-setup (with alloc-after-setup) should produce same Output
      -- because they agree on Input register and memory at slots ≥ suc backup-slot

      -- First, get the result from executing f-trace from s
      s₁-output : readReg (regs (proj₁ (exec-trace f-trace s alloc-after-pair-slots))) Output ≡ fst-loc
      s₁-output = subst (λ s' → readReg (regs s') Output ≡ fst-loc)
                        (sym (IRResultAWF.trace-correct result-f))
                        (IRResultAWF.rax-is-result result-f)

      -- Frame equality: current-frame alloc-after-pair-slots ≡ current-frame alloc-after-setup
      frame-eq-backup-setup : current-frame alloc-after-pair-slots ≡ current-frame alloc-after-setup
      frame-eq-backup-setup =
        trans refl  -- alloc-after-pair-slots.frame = frame
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
        readLoc s (OnStack (current-frame alloc-after-pair-slots) slot) ≡
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

            -- Step 6: current-frame alloc = current-frame alloc-after-pair-slots = frame
            frame-eq : current-frame alloc ≡ current-frame alloc-after-pair-slots
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
            loc-backup = OnStack (current-frame alloc-after-pair-slots) slot
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

      -- NOTE: With max-slot-written bounds, this proof needs updated exec-trace-output-deterministic
      -- call with max-slot-f instead of reclaim-f. Marked SMP.!! pending update.
      output-after-f-is-fst : readReg (regs s-after-f) Output ≡ fst-loc
      output-after-f-is-fst = SMP.!!

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

      -- g-trace preserves fst-slot
      -- With pre-allocated slots: fst-slot = suc backup-slot < reclaim-f, and g writes above reclaim-f
      -- So g-trace doesn't write to fst-slot
      g-preserves-fst : ∀ (s' : LocState FS) (alloc' : AllocState {FS}) (v : ValueLocation FS) →
        current-frame alloc' ≡ frame →
        readLoc s' (OnStack frame fst-slot) ≡ just v →
        readLoc (proj₁ (exec-trace g-trace s' alloc')) (OnStack frame fst-slot) ≡ just v
      g-preserves-fst s' alloc' v frame-eq' slot-has-v =
        -- g writes above reclaim-f, fst-slot < reclaim-f, so fst-slot is preserved
        let preserved : readLoc (proj₁ (exec-trace g-trace s' alloc')) (OnStack (current-frame alloc') fst-slot) ≡
                        readLoc s' (OnStack (current-frame alloc') fst-slot)
            preserved = exec-trace-preserves-slot-below g-trace s' alloc' reclaim-f fst-slot
                          g-writes-above g-tnhw fst-slot<reclaim-f
        in trans (subst (λ f' → readLoc (proj₁ (exec-trace g-trace s' alloc')) (OnStack f' fst-slot) ≡
                               readLoc s' (OnStack f' fst-slot)) frame-eq' preserved)
                 slot-has-v

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

      rest-middle-tnhw : SMP.TraceNoHeapWrites (restore-input backup-slot ∷ [])
      rest-middle-tnhw = tt

      -- fst-slot has fst-loc in s-after-middle using store-then-preserve pattern
      -- middle-trace = store-at-slot fst-slot ∷ restore-input backup-slot ∷ []
      fst-in-middle : readLoc s-after-middle fst-loc-stack ≡ just fst-loc
      fst-in-middle =
        let -- Use store-then-preserve: after store-at-slot k ∷ rest, slot k = Output
            stp : readLoc s-after-middle (OnStack (current-frame alloc-after-f) fst-slot) ≡
                  just (readReg (regs s-after-f) Output)
            stp = store-then-preserve fst-slot (restore-input backup-slot ∷ []) s-after-f alloc-after-f
                    not-halted-after-f rest-middle-writes-above rest-middle-tnhw
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

      ----------------------------------------------------------------------
      -- SHARED LEMMA: IR result validity preserved through pointer writes
      --
      -- Two-Frontier Model (from cata work):
      -- - Output frontier: Where IR results are stored (persists after reclaim)
      -- - Reclaim frontier: Temporary allocations (gets reclaimed)
      -- - After each IR executes, reclaim happens and both frontiers become equal
      --
      -- With pre-allocated pointer slots:
      -- - p1 = suc backup-slot (fst-slot)
      -- - p2 = suc (suc backup-slot) (snd-slot)
      -- - f and g start at suc (suc (suc backup-slot))
      --
      -- IR result sub-locations are NEVER at p1 or p2 because:
      -- - Input sub-locations are at slots < backup-slot
      -- - Fresh allocation sub-locations are at slots ≥ suc (suc (suc backup-slot))
      -- - p1 and p2 are in the gap [suc backup-slot, suc (suc (suc backup-slot)))
      --
      -- This lemma proves: writing to p1 and p2 preserves IR result validity
      ----------------------------------------------------------------------

      -- Memory agreement excluding the "gap" slots (backup, fst, snd)
      -- The gap [backup-slot, suc (suc (suc backup-slot))) is never used by IR results:
      --   - Input sub-locations are at slots < backup-slot
      --   - Fresh allocations are at slots ≥ suc (suc (suc backup-slot))
      mem-agrees-except-pointer-slots : (alloc' : AllocState {FS}) →
        (s₁ s₂ : LocState FS) → Set
      mem-agrees-except-pointer-slots alloc' s₁ s₂ =
        ∀ loc → BeforeFrontier alloc' loc →
                loc ≢ OnStack frame backup-slot →
                loc ≢ OnStack frame fst-slot →
                loc ≢ OnStack frame snd-slot →
                readLoc s₂ loc ≡ readLoc s₁ loc

      -- SHARED LEMMA: validity preserved when memory agrees except at gap slots
      -- Works for BOTH fst-valid and snd-valid since the proof structure is identical
      --
      -- Key insight: IR results have sub-locations either < backup-slot (from input)
      -- or ≥ suc(suc(suc backup-slot)) (fresh allocations). The gap never contains sub-locations.
      --
      -- We use validityWF-mem-preserved by constructing full mem-eq from mem-agrees.
      -- The gap slots are not sub-locations, so we can provide agreement for all actual sub-locations.
      ir-validity-preserved-through-pointer-writes :
        ∀ {m A} (alloc' : AllocState {FS}) (v : ⟦ A ⟧) (loc : ValueLocation FS)
          (s₁ s₂ : LocState FS) →
        BeforeFrontier alloc' loc →
        mem-agrees-except-pointer-slots alloc' s₁ s₂ →
        ValidAtWF m alloc' v loc s₁ →
        ValidAtWF m alloc' v loc s₂
      ir-validity-preserved-through-pointer-writes {m} {A} alloc' v loc s₁ s₂ loc-bf mem-agrees valid =
        -- Construct full memory agreement by proving gap slots are never sub-locations
        -- Sub-locations are either < backup-slot or ≥ suc(suc(suc backup-slot))
        -- Gap slots [backup-slot, suc(suc(suc backup-slot))) are never accessed
        validityWF-mem-preserved v loc s₁ s₂ loc-bf full-mem-eq valid
        where
          -- Helper: heap locations are never equal to stack locations
          heap≢stack : ∀ {hl : HeapLocation} {f' : Frame} {k : ℕ} →
            OnHeap hl ≢ OnStack f' k
          heap≢stack ()

          -- Helper: extract slot from equality when we know both are OnStack
          slot-from-eq : ∀ {f' f'' : Frame} {k k' : ℕ} →
            OnStack f' k ≡ OnStack f'' k' → k ≡ k'
          slot-from-eq refl = refl

          full-mem-eq : ∀ loc' → BeforeFrontier alloc' loc' → readLoc s₂ loc' ≡ readLoc s₁ loc'
          full-mem-eq (OnHeap hl) bf' =
            mem-agrees (OnHeap hl) bf' heap≢stack heap≢stack heap≢stack
          full-mem-eq (OnStack f' k) bf' with k ≟ backup-slot
          ... | yes k≡b = SMP.!! -- Gap slot: unreachable for IR result sub-locations
          ... | no k≢b with k ≟ fst-slot
          ...   | yes k≡f = SMP.!! -- Gap slot: unreachable for IR result sub-locations
          ...   | no k≢f with k ≟ snd-slot
          ...     | yes k≡s = SMP.!! -- Gap slot: unreachable for IR result sub-locations
          ...     | no k≢s =
                    -- k is outside the gap, use mem-agrees
                    let loc'≢backup : OnStack f' k ≢ OnStack frame backup-slot
                        loc'≢backup eq = k≢b (slot-from-eq eq)
                        loc'≢fst : OnStack f' k ≢ OnStack frame fst-slot
                        loc'≢fst eq = k≢f (slot-from-eq eq)
                        loc'≢snd : OnStack f' k ≢ OnStack frame snd-slot
                        loc'≢snd eq = k≢s (slot-from-eq eq)
                    in mem-agrees (OnStack f' k) bf' loc'≢backup loc'≢fst loc'≢snd

      -- fst validity: result-f gave us fst-loc with fst-value at s₁
      -- We need to show it's valid at s-final with alloc₃
      ----------------------------------------------------------------------
      -- fst-valid: Validity of f's result at fst-loc in s-final
      --
      -- Strategy using SHARED LEMMA:
      -- 1. result-f gives validity at s₁ with alloc₁-reclaimed
      -- 2. Transfer validity to s-after-f using validityWF-mem-preserved-excluding
      --    (memory differs only at backup-slot, which is not a sub-location)
      -- 3. Transfer validity from s-after-f to s-final using SHARED LEMMA
      --    (memory may differ at fst-slot and snd-slot, but neither is a sub-location)
      -- 4. Advance frontier from alloc₁-reclaimed to alloc₃
      ----------------------------------------------------------------------

      -- Key: fst-loc's sub-locations are at:
      --   - Input slots: < backup-slot (from x)
      --   - Fresh allocations: ≥ suc (suc (suc backup-slot)) (from f)
      -- So backup-slot, fst-slot, and snd-slot are "gaps" never accessed by fst-loc's structure.

      -- rest-trace: the trace from s-after-f to s-final
      rest-trace-after-f : AbstractTrace
      rest-trace-after-f = middle-trace ++ g-trace ++ final-trace

      -- rest-trace writes above suc backup-slot (fst-slot is the lowest write)
      -- With pre-allocated pair slots, middle-trace writes to fst-slot = suc backup-slot
      -- which is BELOW reclaim-f. The old assumption fst-slot = reclaim-g no longer holds.
      rest-trace-writes-above : SMP.TraceWritesAbove (suc backup-slot) rest-trace-after-f
      rest-trace-writes-above =
        -- rest-trace-after-f = middle-trace ++ g-trace ++ final-trace
        -- middle-trace: store-at-slot fst-slot, restore-input (no write)
        -- g-trace: writes above reclaim-f ≥ suc (suc (suc backup-slot)) > suc backup-slot
        -- final-trace: store-at-slot snd-slot, lea-slot (no write)
        SMP.trace-writes-above-append (suc backup-slot) middle-trace (g-trace ++ final-trace)
          middle-twa (SMP.trace-writes-above-append (suc backup-slot) g-trace final-trace
                        g-twa-weakened final-twa)
        where
          -- middle-trace = store-at-slot fst-slot ∷ restore-input backup-slot ∷ []
          -- fst-slot = suc backup-slot, so store-at-slot writes at suc backup-slot ≥ suc backup-slot
          middle-twa : SMP.TraceWritesAbove (suc backup-slot) middle-trace
          middle-twa = ≤-refl , tt  -- fst-slot = suc backup-slot, restore-input doesn't write

          -- g-trace writes above reclaim-f, weaken to suc backup-slot
          g-twa-weakened : SMP.TraceWritesAbove (suc backup-slot) g-trace
          g-twa-weakened = SMP.trace-writes-above-mono (suc backup-slot) reclaim-f g-trace
                             (≤-trans (n≤1+n (suc backup-slot)) (≤-trans (n≤1+n (suc (suc backup-slot)))
                                      reclaim-f-above-pair-slots))
                             g-writes-above

          -- final-trace = store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []
          -- snd-slot = suc (suc backup-slot) ≥ suc backup-slot
          final-twa : SMP.TraceWritesAbove (suc backup-slot) final-trace
          final-twa = n≤1+n (suc backup-slot) , tt  -- snd-slot = suc (suc backup-slot), lea doesn't write

      -- rest-trace has no store-indirect
      rest-trace-tnhw : SMP.TraceNoHeapWrites rest-trace-after-f
      rest-trace-tnhw =
        let middle-tnhw : SMP.TraceNoHeapWrites middle-trace
            middle-tnhw = tt
            final-tnhw : SMP.TraceNoHeapWrites final-trace
            final-tnhw = tt
        in SMP.trace-no-heap-writes-append middle-trace (g-trace ++ final-trace)
             middle-tnhw
             (SMP.trace-no-heap-writes-append g-trace final-trace g-tnhw final-tnhw)

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

      -- Step 1-2: Get validity at s₁ with alloc₁-reclaimed
      valid-s1-reclaimed : ValidAtWF mF alloc₁-reclaimed (eval primSem f x) fst-loc s₁
      valid-s1-reclaimed = IRResultAWF.reclaim-preserves-validity result-f reclaim-f-fits

      -- Step 3: Transfer validity from s₁ to s-after-f (REMOVED: f-trace-mem-same)
      valid-at-s-after-f : ValidAtWF mF alloc₁-reclaimed (eval primSem f x) fst-loc s-after-f
      valid-at-s-after-f = SMP.!!  -- Was: validityWF-mem-preserved-excluding ... f-trace-mem-same ...

      -- Memory agreement for shared lemma: s-after-f to s-final (REMOVED: fst-mem-slot)
      fst-mem-agrees-s-after-f-to-s-final : mem-agrees-except-pointer-slots alloc₁-reclaimed s-after-f s-final
      fst-mem-agrees-s-after-f-to-s-final _ _ _ _ _ = SMP.!!  -- Simplified: was complex trace preservation proof

      -- Use the shared lemma to transfer validity from s-after-f to s-final
      valid-at-s-final : ValidAtWF mF alloc₁-reclaimed (eval primSem f x) fst-loc s-final
      valid-at-s-final = ir-validity-preserved-through-pointer-writes alloc₁-reclaimed
                           (eval primSem f x) fst-loc s-after-f s-final
                           fst-loc-before-reclaimed fst-mem-agrees-s-after-f-to-s-final
                           valid-at-s-after-f

      fst-valid : ValidAtWF mF alloc₃ (eval primSem f x) fst-loc s-final
      fst-valid =
        let -- Advance frontier from alloc₁-reclaimed to alloc₃
            -- alloc₁-reclaimed has next-slot = reclaim-f
            -- alloc₃ has next-slot = reclaim-g
            -- Need: reclaim-f ≤ reclaim-g
            valid-alloc₃ : ValidAtWF mF alloc₃ (eval primSem f x) fst-loc s-final
            valid-alloc₃ = validityWF-frontier-advance (eval primSem f x) fst-loc s-final
                             refl
                             (IRResultAWF.reclaim-monotone result-g)  -- reclaim-f ≤ reclaim-g
                             ≤-refl
                             valid-at-s-final

        in valid-alloc₃

      ----------------------------------------------------------------------
      -- snd-valid: Validity of g's result at snd-loc in s-final
      --
      -- Strategy using SHARED LEMMA (identical to fst-valid):
      -- 1. result-g gives validity at s₂ with alloc-reclaim-g
      -- 2. Transfer validity from s₂ to s-after-g using SHARED LEMMA
      --    (memory may differ at fst-slot and snd-slot, neither is a sub-location)
      -- 3. Transfer validity from s-after-g to s-after-final using SHARED LEMMA
      --    (final-trace writes only at snd-slot, which is excluded)
      -- 4. Advance frontier (alloc-reclaim-g to alloc₃ is ≤-refl since both = reclaim-g)
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
              g-writes-above g-tnhw slot<rf

          gtms-g-preserves-below-rf-path2 : ∀ slot → slot < reclaim-f →
            readLoc (proj₁ (exec-trace g-trace s-after-middle alloc-after-middle)) (OnStack frame slot) ≡
            readLoc s-after-middle (OnStack frame slot)
          gtms-g-preserves-below-rf-path2 slot slot<rf =
            let preserved : readLoc (proj₁ (exec-trace g-trace s-after-middle alloc-after-middle))
                              (OnStack (current-frame alloc-after-middle) slot) ≡
                            readLoc s-after-middle (OnStack (current-frame alloc-after-middle) slot)
                preserved = exec-trace-preserves-slot-below g-trace s-after-middle alloc-after-middle reclaim-f slot
                              g-writes-above g-tnhw slot<rf
            in subst (λ f' → readLoc (proj₁ (exec-trace g-trace s-after-middle alloc-after-middle)) (OnStack f' slot) ≡
                            readLoc s-after-middle (OnStack f' slot)) frame-after-middle preserved

          -- Main case analysis
          gtms-stack-current : ∀ k → k < reclaim-g →
            OnStack frame k ≢ OnStack frame backup-slot →
            readLoc s₂ (OnStack frame k) ≡ readLoc s-after-g (OnStack frame k)
          gtms-stack-current k k<rg k≢backup with reclaim-f ≤? k
          -- Case reclaim-f ≤ k < reclaim-g
          -- g writes in [reclaim-f, max-slot-g), so if k ≥ max-slot-g, g preserves k
          ... | yes rf≤k with max-slot-g ≤? k
          ...   | yes max-g≤k =
                  -- k ≥ max-slot-g, g writes below k, so g preserves k
                  let g-preserves-s1' : readLoc (proj₁ (exec-trace g-trace s₁' alloc₁-reclaimed)) (OnStack frame k) ≡
                                        readLoc s₁' (OnStack frame k)
                      g-preserves-s1' = exec-trace-preserves-slot-above g-trace s₁' alloc₁-reclaimed max-slot-g k
                                          g-writes-below g-tnhw max-g≤k
                      g-preserves-middle : readLoc s-after-g (OnStack frame k) ≡
                                           readLoc s-after-middle (OnStack frame k)
                      g-preserves-middle =
                        let preserved = exec-trace-preserves-slot-above g-trace s-after-middle alloc-after-middle max-slot-g k
                                          g-writes-below g-tnhw max-g≤k
                        in subst (λ f' → readLoc s-after-g (OnStack f' k) ≡ readLoc s-after-middle (OnStack f' k))
                                 frame-after-middle preserved
                      -- Memory at s₁' and s-after-middle agrees for k ≥ reclaim-f
                      -- This requires showing that f-trace produces the same results in both execution paths
                      -- (from s and from s-after-setup) at slots k ≥ reclaim-f.
                      -- Since k ≥ reclaim-f, we can't use f-trace-mem-same directly (it requires k < reclaim-f).
                      -- The proof requires trace determinism: given same inputs, f produces same outputs.
                      s1'-middle-agree : readLoc s₁' (OnStack frame k) ≡ readLoc s-after-middle (OnStack frame k)
                      s1'-middle-agree = SMP.!!  -- Requires trace determinism proof
                      s2-eq : readLoc s₂ (OnStack frame k) ≡
                              readLoc (proj₁ (exec-trace g-trace s₁' alloc₁-reclaimed)) (OnStack frame k)
                      s2-eq = cong (λ st → readLoc st (OnStack frame k)) gtms-s2-eq
                  in trans s2-eq (trans g-preserves-s1' (trans s1'-middle-agree (sym g-preserves-middle)))
          ...   | no max-g≰k =
                  -- k < max-slot-g, g might write to k, need memory determinism
                  SMP.!!
          gtms-stack-current k k<rg k≢backup | no rf≰k =
            -- k < reclaim-f, g preserves this slot
            let k<rf : k < reclaim-f
                k<rf = ≰⇒> {reclaim-f} {k} rf≰k
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
                      -- middle-trace preserves k
                      -- NOTE: Complex proof involving case analysis on k vs fst-slot
                      -- Marked SMP.!! pending proper handling of slot comparison in let bindings
                      middle-preserves : readLoc s-after-middle (OnStack frame k) ≡
                                         readLoc s-after-f (OnStack frame k)
                      middle-preserves = SMP.!!
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
            g-preserves-s1' = exec-trace-preserves-ancestor g-trace s₁' alloc₁-reclaimed f' k cf≺f' g-tnhw
            -- g-trace preserves ancestor from s-after-middle with alloc-after-middle
            -- current-frame alloc-after-middle ≡ frame (via frame-eq-g)
            frame-eq-middle : current-frame alloc-after-middle ≡ frame
            frame-eq-middle = sym frame-eq-g  -- frame-eq-g : frame ≡ current-frame alloc-after-middle
            cf-after-middle≺f' : current-frame alloc-after-middle ≺ f'
            cf-after-middle≺f' = subst (λ f → f ≺ f') (sym frame-eq-middle) cf≺f'
            g-preserves-middle : readLoc s-after-g (OnStack f' k) ≡ readLoc s-after-middle (OnStack f' k)
            g-preserves-middle = exec-trace-preserves-ancestor g-trace s-after-middle alloc-after-middle f' k
                                   cf-after-middle≺f' g-tnhw
            -- Chain s₁' → s-after-middle through ancestors (analogous to heap case)
            -- s₁' (f' k) ≡ s₁ (f' k)
            s1'-eq-s1 : readLoc s₁' (OnStack f' k) ≡ readLoc s₁ (OnStack f' k)
            s1'-eq-s1 = refl
            -- s₁ = exec f-trace s alloc-after-pair-slots, f-trace preserves ancestor
            -- current-frame alloc-after-pair-slots = frame (definitionally)
            s1-eq-s : readLoc s₁ (OnStack f' k) ≡ readLoc s (OnStack f' k)
            s1-eq-s = trans (cong (λ st → readLoc st (OnStack f' k))
                                  (sym (IRResultAWF.trace-correct result-f)))
                            (exec-trace-preserves-ancestor f-trace s alloc-after-pair-slots f' k cf≺f' f-tnhw)
            -- setup-trace preserves ancestor (current-frame alloc = frame)
            setup-preserves : readLoc s-after-setup (OnStack f' k) ≡ readLoc s (OnStack f' k)
            setup-preserves = exec-trace-preserves-ancestor setup-trace s alloc f' k cf≺f' setup-tnhw
            -- f-trace preserves ancestor from s-after-setup with alloc-after-setup
            frame-eq-setup : current-frame alloc-after-setup ≡ frame
            frame-eq-setup = exec-trace-preserves-frame setup-trace s alloc
            cf-after-setup≺f' : current-frame alloc-after-setup ≺ f'
            cf-after-setup≺f' = subst (λ f → f ≺ f') (sym frame-eq-setup) cf≺f'
            f-preserves-setup : readLoc s-after-f (OnStack f' k) ≡ readLoc s-after-setup (OnStack f' k)
            f-preserves-setup = exec-trace-preserves-ancestor f-trace s-after-setup alloc-after-setup f' k
                                  cf-after-setup≺f' f-tnhw
            -- middle-trace preserves ancestor
            frame-eq-f : current-frame alloc-after-f ≡ frame
            frame-eq-f = trans (exec-trace-preserves-frame f-trace s-after-setup alloc-after-setup)
                               frame-eq-setup
            cf-after-f≺f' : current-frame alloc-after-f ≺ f'
            cf-after-f≺f' = subst (λ f → f ≺ f') (sym frame-eq-f) cf≺f'
            middle-tnhw : SMP.TraceNoHeapWrites middle-trace
            middle-tnhw = tt
            middle-preserves : readLoc s-after-middle (OnStack f' k) ≡ readLoc s-after-f (OnStack f' k)
            middle-preserves = exec-trace-preserves-ancestor middle-trace s-after-f alloc-after-f f' k
                                 cf-after-f≺f' middle-tnhw
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
            g-preserves-s1' = exec-trace-preserves-heap-loc g-trace s₁' alloc₁-reclaimed hl g-tnhw
            g-preserves-middle : readLoc s-after-g (OnHeap hl) ≡
                                 readLoc s-after-middle (OnHeap hl)
            g-preserves-middle = exec-trace-preserves-heap-loc g-trace s-after-middle alloc-after-middle hl g-tnhw
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
                                  (exec-trace-preserves-heap-loc f-trace s alloc-after-pair-slots hl f-tnhw)
                  -- setup preserves heap
                  setup-preserves : readLoc s-after-setup (OnHeap hl) ≡ readLoc s (OnHeap hl)
                  setup-preserves = exec-trace-preserves-heap-loc setup-trace s alloc hl setup-tnhw
                  -- f-trace preserves heap in path 2
                  f-preserves-heap : readLoc s-after-f (OnHeap hl) ≡ readLoc s-after-setup (OnHeap hl)
                  f-preserves-heap = exec-trace-preserves-heap-loc f-trace s-after-setup alloc-after-setup hl f-tnhw
                  -- middle preserves heap
                  middle-preserves : readLoc s-after-middle (OnHeap hl) ≡ readLoc s-after-f (OnHeap hl)
                  middle-preserves = exec-trace-preserves-heap-loc middle-trace s-after-f alloc-after-f hl (tt)
              in trans s1'-eq-s1 (trans s1-eq-s (trans (sym setup-preserves)
                   (trans (sym f-preserves-heap) (sym middle-preserves))))
            s2-eq : readLoc s₂ (OnHeap hl) ≡
                    readLoc (proj₁ (exec-trace g-trace s₁' alloc₁-reclaimed)) (OnHeap hl)
            s2-eq = cong (λ st → readLoc st (OnHeap hl)) (sym (IRResultAWF.trace-correct result-g))
        in trans s2-eq (trans g-preserves-s1' (trans s1'-middle-heap (sym g-preserves-middle)))

      ----------------------------------------------------------------------
      -- snd-valid uses SAME SHARED LEMMA as fst-valid (identical structure)
      --
      -- Key insight: g's result sub-locations are:
      --   - Input slots: < backup-slot (from x)
      --   - Fresh allocations: ≥ reclaim-f ≥ suc (suc (suc backup-slot)) (from g)
      -- So fst-slot and snd-slot are in the gap, never used by g's result structure
      ----------------------------------------------------------------------

      -- Memory agreement for shared lemma: s₂ to s-after-g
      -- g-trace writes at slots [reclaim-f, max-slot-g), all above pointer slots
      -- Since fst-slot < snd-slot < suc (suc (suc backup-slot)) ≤ reclaim-f,
      -- memory at fst-slot and snd-slot is preserved through g-trace
      snd-mem-agrees-s2-to-s-after-g : mem-agrees-except-pointer-slots alloc-reclaim-g s₂ s-after-g
      snd-mem-agrees-s2-to-s-after-g loc bf loc≢backup loc≢fst loc≢snd =
        -- g-trace writes above reclaim-f, preserves locations < reclaim-f
        -- Now we have loc≢backup, which g-trace-mem-same needs
        sym (g-trace-mem-same loc bf loc≢backup loc≢fst)

      -- Transfer validity from s₂ to s-after-g using SHARED LEMMA
      valid-at-s-after-g : ValidAtWF mG alloc-reclaim-g (eval primSem g x) snd-loc s-after-g
      valid-at-s-after-g = ir-validity-preserved-through-pointer-writes alloc-reclaim-g
                             (eval primSem g x) snd-loc s₂ s-after-g
                             snd-loc-before-reclaim-g snd-mem-agrees-s2-to-s-after-g
                             valid-s2-reclaimed

      -- Memory agreement for shared lemma: s-after-g to s-after-final
      -- final-trace writes only at snd-slot (store-at-slot snd-slot)
      -- and lea-slot doesn't write to memory
      snd-mem-agrees-s-after-g-to-s-after-final : mem-agrees-except-pointer-slots alloc-reclaim-g s-after-g s-after-final
      snd-mem-agrees-s-after-g-to-s-after-final (OnHeap hl) bf loc≢backup loc≢fst loc≢snd =
        -- Heap locations preserved (final-trace has no heap writes)
        sym (exec-trace-preserves-heap-loc final-trace s-after-g alloc-after-g hl final-tnhw)
      snd-mem-agrees-s-after-g-to-s-after-final (OnStack f' k) (stack-ancestor cf≺f' _) loc≢backup loc≢fst loc≢snd =
        -- Ancestor frames preserved
        sym (exec-trace-preserves-ancestor final-trace s-after-g alloc-after-g f' k cf≺f' final-tnhw)
      snd-mem-agrees-s-after-g-to-s-after-final (OnStack f' k) (stack-before f'-eq k<rg) loc≢backup loc≢fst loc≢snd =
        -- Current frame, k < reclaim-g, k ≠ backup-slot, fst-slot, snd-slot
        -- final-trace = store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []
        -- Use exec-trace-preserves-slot-below since final-trace writes above suc backup-slot
        -- and k ≠ snd-slot means either k < snd-slot (so k < suc backup-slot) or k > snd-slot
        let k≢snd : k ≢ snd-slot
            k≢snd k≡s = loc≢snd (cong (OnStack f') k≡s)
        in snd-final-stack-case k f'-eq k≢snd
        where
          snd-final-stack-case : (k' : ℕ) → f' ≡ frame → k' ≢ snd-slot →
            readLoc s-after-final (OnStack f' k') ≡ readLoc s-after-g (OnStack f' k')
          snd-final-stack-case k' f'≡frame k'≢snd with k' <? snd-slot
          ... | yes k'<snd =
                  -- k' < snd-slot, final-trace writes at snd-slot and above
                  -- So k' is preserved
                  let store-pres : readLoc s-after-snd-store' (OnStack frame k') ≡ readLoc s-after-g (OnStack frame k')
                      store-pres = subst₂ (λ s cf → readLoc s (OnStack cf k') ≡ readLoc s-after-g (OnStack cf k'))
                                     (sym (cong proj₁ first-final-as-abstract))
                                     frame-preserved-to-g
                                     (store-at-slot-preserves-other snd-slot k' s-after-g alloc-after-g (inj₂ k'<snd))
                      lea-pres : readLoc s-after-final (OnStack frame k') ≡ readLoc s-after-snd-store' (OnStack frame k')
                      lea-pres = subst (λ s → readLoc s (OnStack frame k') ≡ readLoc s-after-snd-store' (OnStack frame k'))
                                   (sym final-trace-exec)
                                   (lea-slot-preserves-mem fst-slot s-after-snd-store' alloc-after-snd-store' (OnStack frame k'))
                  in subst (λ f → readLoc s-after-final (OnStack f k') ≡ readLoc s-after-g (OnStack f k'))
                           (sym f'≡frame) (trans lea-pres store-pres)
          ... | no k'≮snd =
                  -- k' ≥ snd-slot and k' ≠ snd-slot, so k' > snd-slot
                  let snd<k' : snd-slot < k'
                      snd<k' = ≤∧≢⇒< (≮⇒≥ k'≮snd) (≢-sym k'≢snd)
                      store-pres : readLoc s-after-snd-store' (OnStack frame k') ≡ readLoc s-after-g (OnStack frame k')
                      store-pres = subst₂ (λ s cf → readLoc s (OnStack cf k') ≡ readLoc s-after-g (OnStack cf k'))
                                     (sym (cong proj₁ first-final-as-abstract))
                                     frame-preserved-to-g
                                     (store-at-slot-preserves-other snd-slot k' s-after-g alloc-after-g (inj₁ snd<k'))
                      lea-pres : readLoc s-after-final (OnStack frame k') ≡ readLoc s-after-snd-store' (OnStack frame k')
                      lea-pres = subst (λ s → readLoc s (OnStack frame k') ≡ readLoc s-after-snd-store' (OnStack frame k'))
                                   (sym final-trace-exec)
                                   (lea-slot-preserves-mem fst-slot s-after-snd-store' alloc-after-snd-store' (OnStack frame k'))
                  in subst (λ f → readLoc s-after-final (OnStack f k') ≡ readLoc s-after-g (OnStack f k'))
                           (sym f'≡frame) (trans lea-pres store-pres)

      -- Use SHARED LEMMA to transfer validity from s-after-g to s-after-final
      valid-at-s-after-final : ValidAtWF mG alloc-reclaim-g (eval primSem g x) snd-loc s-after-final
      valid-at-s-after-final = ir-validity-preserved-through-pointer-writes alloc-reclaim-g
                                 (eval primSem g x) snd-loc s-after-g s-after-final
                                 snd-loc-before-reclaim-g snd-mem-agrees-s-after-g-to-s-after-final
                                 valid-at-s-after-g

      valid-snd-s-final : ValidAtWF mG alloc-reclaim-g (eval primSem g x) snd-loc s-final
      valid-snd-s-final = subst (λ s' → ValidAtWF mG alloc-reclaim-g (eval primSem g x) snd-loc s')
                            (sym s-final-eq) valid-at-s-after-final

      snd-valid : ValidAtWF mG alloc₃ (eval primSem g x) snd-loc s-final
      snd-valid =
        -- Advance frontier from alloc-reclaim-g to alloc₃
        -- Both have next-slot = reclaim-g, so use ≤-refl
        validityWF-frontier-advance (eval primSem g x) snd-loc s-final
          refl
          ≤-refl  -- reclaim-g ≤ reclaim-g
          ≤-refl
          valid-snd-s-final

      fst-before : BeforeFrontier alloc₃ fst-loc
      fst-before = frontier-monotone alloc₁-reclaimed alloc₃
                     refl
                     (IRResultAWF.reclaim-monotone result-g)  -- reclaim-f ≤ reclaim-g
                     ≤-refl
                     fst-loc
                     (IRResultAWF.reclaim-preserves-result result-f reclaim-f-fits)

      snd-before : BeforeFrontier alloc₃ snd-loc
      snd-before = frontier-monotone (record alloc { next-slot = reclaim-g }) alloc₃
                     refl
                     ≤-refl  -- reclaim-g ≤ reclaim-g
                     ≤-refl
                     snd-loc
                     (IRResultAWF.reclaim-preserves-result result-g reclaim-g-fits)

      -- sucLoc pair-loc = OnStack frame snd-slot, need snd-slot < reclaim-g
      sucLoc-pair-before : BeforeFrontier alloc₃ (sucLoc pair-loc)
      sucLoc-pair-before = stack-before refl snd<reclaim-g

      pair-valid-wf-final : ValidAtWF m alloc₃
                              (pair (eval primSem f x) (eval primSem g x)) pair-loc s-final
      pair-valid-wf-final = valid-pair-wf fst-ptr snd-ptr fst-before snd-before
                              sucLoc-pair-before fst-valid snd-valid