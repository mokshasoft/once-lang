-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Machine.IR.PairWF2.Validity
--
-- Plan 0.18 — Option C extraction of PairWF2 phases 9-11.
--
-- Phases 9-11 (oaf-*, oag-*, fst/snd preservation, validity chains;
-- originally PairWF2.agda lines 1769-2823) live in this compilation
-- unit. PairWF2.run-pair instantiates the nested chain
-- `Validity.L2.L3` with its phase-1-to-8 products, then reads off the
-- single export `pair-valid-wf-final`.
--
-- Nesting layout (each level derives intermediate states from the
-- previous level's products, so that the *next* level's parameters
-- can mention them in their types):
--
--   Validity      — function args + setup primitives;
--                   derives slots, alloc-after-pair-slots,
--                   s-after-setup / alloc-after-setup.
--   .L2           — result-f + FstFacts + middle-trace + halted
--                   witnesses; derives reclaim-f, alloc-after-f-reclaim,
--                   s-after-f / alloc-after-f, s-after-middle, etc.
--   .L3           — result-g + SndFacts + final-trace + remaining
--                   final-phase products. Body contains the migrated
--                   validity proofs.
------------------------------------------------------------------------

module Once.CCC.Machine.IR.PairWF2.Validity where

open import Data.Nat using (ℕ; suc; _<_; _≤_; _≥_; s≤s; z≤n; _⊔_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; m≤n+m; n≤1+n; +-comm; +-assoc; +-suc; +-identityʳ; +-monoˡ-≤; +-monoʳ-≤; <-≤-trans; <⇒≤; <⇒≢; m≤m⊔n; m≤n⊔m; ⊔-lub; _<?_; ≮⇒≥)
open import Data.Empty using (⊥-elim)
open import Data.Bool using (false)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym; cong; cong₂; subst; subst₂)
open import Relation.Nullary using (yes; no)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore hiding (AllocMode; Stack; Heap)
open import Once.Semantics.Machine using (⟦_⟧; sem-pair)
pair = sem-pair
open import Once.CCC.IR
open import Once.CCC.Eval using (eval)
open import Once.CCC.IR.Size
open import Once.CCC.IR.Stack
open import Once.CCC.Machine.Allocation hiding (AllocMode)
open import Once.CCC.Machine.ClosureWellFormed

import Once.CCC.Machine.SMPrimitives as SMP

module ValidityImpl {FS : FrameSemantics} (program-bound : ℕ) where
  open FrameSemantics FS
  open FrontierInvariant {FS}
  open MemOps {FS}
  open WriteOps {FS}
  open StackAllocation {FS}
  open AbstractExec {FS}
  open ExecLemmas {FS}

  open SMP.MemoryOps {FS}
  open SMP.InstrPrimitives {FS}
  open SMP.TracePrimitives {FS}
  open SMP.TraceComposition {FS}
  open SMP.TraceOutputDeterminism {FS}

  open ClosureWellFormedDef {FS} program-bound
    using (ValidAtWF; IRResultAWF; ResultPlace; unit-result; at-loc;
           RecDispatcherWF; mk-IRResultAWF-via-bump;
           valid-pair-wf; valid-unit-wf;
           validityWF-mem-only; validityWF-mem-preserved;
           validityWF-mem-preserved-in-regions;
           validityWF-frontier-advance;
           validityWF-trace-preserves;
           irresult-mem-preserved; mem-preserved-from-tnhw)

  ------------------------------------------------------------------------
  -- Validity — outermost level
  ------------------------------------------------------------------------
  module Validity
    {A B C : Type}
    (mIn : AllocMode)
    (f : IR A B) (g : IR A C)
    (x : ⟦ A ⟧)
    -- Function args
    (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS})
    (not-halted : halted s ≡ false)
    (rdi-eq : readReg (regs s) Input1 ≡ SV-Ptr input-loc)
    -- Plan 0.18 wire-through: PairWF2 also passes the input validity
    -- and frontier witnesses so Validity owns ALL setup-time prep
    -- (no run-pair-side duplication).
    (input-valid-wf : ValidAtWF mIn alloc x input-loc s)
    (input-before : BeforeFrontier alloc input-loc)
    where

    -- Phase 1: derived slot layout
    frame : Frame
    frame = current-frame alloc

    backup-slot : ℕ
    backup-slot = next-slot alloc

    fst-slot : ℕ
    fst-slot = suc backup-slot

    snd-slot : ℕ
    snd-slot = suc fst-slot

    f-start : ℕ
    f-start = suc snd-slot

    pair-overhead : ℕ
    pair-overhead = suc pair-slots

    pair-loc : ValueLocation FS
    pair-loc = AtStack frame fst-slot

    alloc-after-pair-slots : AllocState {FS}
    alloc-after-pair-slots = record alloc { next-slot = f-start }

    -- Phase 2: setup-trace is a concrete list; derive it + trivial witnesses.
    setup-trace : AbstractTrace
    setup-trace = mov-to-output ∷ store-at-slot backup-slot
                  ∷ instr-alloc-stack pair-overhead ∷ []

    setup-twf : TraceWF s alloc setup-trace
    setup-twf = twf-∷ tt (twf-∷ tt (twf-∷ tt twf-[]))

    s-after-setup : LocState FS
    s-after-setup = proj₁ (exec-trace setup-trace s alloc)

    alloc-after-setup : AllocState {FS}
    alloc-after-setup = proj₂ (exec-trace setup-trace s alloc)

    not-halted-after-setup : halted s-after-setup ≡ false
    not-halted-after-setup = exec-trace-preserves-halted-WF setup-trace s alloc
                               not-halted setup-twf

    ----------------------------------------------------------------------
    -- Plan 0.18 prep — derivations PairWF2 used to compute locally.
    -- Wrapped in `abstract` so downstream sees only propositional types.
    ----------------------------------------------------------------------
    abstract
      alloc-setup-eq-pair-slots : alloc-after-setup ≡ alloc-after-pair-slots
      alloc-setup-eq-pair-slots =
        let s₁ʳ = proj₁ (exec-abstract mov-to-output s alloc)
            alloc₁ʳ = proj₂ (exec-abstract mov-to-output s alloc)
            not-halted₁ʳ = exec-abstract-preserves-halted mov-to-output s alloc not-halted iph-mov-to-output
            s₂ʳ = proj₁ (exec-abstract (store-at-slot backup-slot) s₁ʳ alloc₁ʳ)
            alloc₂ʳ = proj₂ (exec-abstract (store-at-slot backup-slot) s₁ʳ alloc₁ʳ)
            not-halted₂ʳ = exec-abstract-preserves-halted (store-at-slot backup-slot) s₁ʳ alloc₁ʳ not-halted₁ʳ iph-store-at-slot
            setup-decomp : exec-trace setup-trace s alloc ≡
                           exec-trace (store-at-slot backup-slot ∷ instr-alloc-stack pair-overhead ∷ []) s₁ʳ alloc₁ʳ
            setup-decomp = exec-trace-cons mov-to-output _ s alloc not-halted
            store-decomp : exec-trace (store-at-slot backup-slot ∷ instr-alloc-stack pair-overhead ∷ []) s₁ʳ alloc₁ʳ ≡
                           exec-trace (instr-alloc-stack pair-overhead ∷ []) s₂ʳ alloc₂ʳ
            store-decomp = exec-trace-cons (store-at-slot backup-slot) _ s₁ʳ alloc₁ʳ not-halted₁ʳ
            alloc-single : exec-trace (instr-alloc-stack pair-overhead ∷ []) s₂ʳ alloc₂ʳ ≡
                           exec-abstract (instr-alloc-stack pair-overhead) s₂ʳ alloc₂ʳ
            alloc-single = exec-trace-single (instr-alloc-stack pair-overhead) s₂ʳ alloc₂ʳ not-halted₂ʳ
            f-start-arith : next-slot alloc +ℕ pair-overhead ≡ f-start
            f-start-arith = trans (+-comm (next-slot alloc) 3) refl
            via-chain : proj₂ (exec-trace setup-trace s alloc) ≡
                        record alloc { next-slot = next-slot alloc +ℕ pair-overhead }
            via-chain = cong proj₂ (trans setup-decomp (trans store-decomp alloc-single))
        in trans via-chain
                 (cong (λ n → record alloc { next-slot = n }) f-start-arith)

      rdi-eq-after-setup : readReg (regs s-after-setup) Input1 ≡ SV-Ptr input-loc
      rdi-eq-after-setup =
        let s₁ʳ = proj₁ (exec-abstract mov-to-output s alloc)
            alloc₁ʳ = proj₂ (exec-abstract mov-to-output s alloc)
            mov-preserves : readReg (regs s₁ʳ) Input1 ≡ readReg (regs s) Input1
            mov-preserves = writeReg-preserves (regs s) Output Input1 (readReg (regs s) Input1) (λ ())
            not-halted₁ʳ = exec-abstract-preserves-halted mov-to-output s alloc not-halted iph-mov-to-output
            s₂ʳ = proj₁ (exec-abstract (store-at-slot backup-slot) s₁ʳ alloc₁ʳ)
            alloc₂ʳ = proj₂ (exec-abstract (store-at-slot backup-slot) s₁ʳ alloc₁ʳ)
            store-preserves : readReg (regs s₂ʳ) Input1 ≡ readReg (regs s₁ʳ) Input1
            store-preserves = exec-abstract-store-at-slot-preserves-input backup-slot s₁ʳ alloc₁ʳ
            not-halted₂ʳ = exec-abstract-preserves-halted (store-at-slot backup-slot) s₁ʳ alloc₁ʳ not-halted₁ʳ iph-store-at-slot
            s₃ʳ = proj₁ (exec-abstract (instr-alloc-stack pair-overhead) s₂ʳ alloc₂ʳ)
            alloc-stack-preserves : readReg (regs s₃ʳ) Input1 ≡ readReg (regs s₂ʳ) Input1
            alloc-stack-preserves = refl
            setup-decomp : exec-trace setup-trace s alloc ≡
                           exec-trace (store-at-slot backup-slot ∷ instr-alloc-stack pair-overhead ∷ []) s₁ʳ alloc₁ʳ
            setup-decomp = exec-trace-cons mov-to-output (store-at-slot backup-slot ∷ instr-alloc-stack pair-overhead ∷ []) s alloc not-halted
            store-decomp : exec-trace (store-at-slot backup-slot ∷ instr-alloc-stack pair-overhead ∷ []) s₁ʳ alloc₁ʳ ≡
                           exec-trace (instr-alloc-stack pair-overhead ∷ []) s₂ʳ alloc₂ʳ
            store-decomp = exec-trace-cons (store-at-slot backup-slot) (instr-alloc-stack pair-overhead ∷ []) s₁ʳ alloc₁ʳ not-halted₁ʳ
            alloc-single : exec-trace (instr-alloc-stack pair-overhead ∷ []) s₂ʳ alloc₂ʳ ≡
                           exec-abstract (instr-alloc-stack pair-overhead) s₂ʳ alloc₂ʳ
            alloc-single = exec-trace-single (instr-alloc-stack pair-overhead) s₂ʳ alloc₂ʳ not-halted₂ʳ
            s-eq : s-after-setup ≡ s₃ʳ
            s-eq = cong proj₁ (trans setup-decomp (trans store-decomp alloc-single))
        in trans (cong (λ st → readReg (regs st) Input1) s-eq)
                 (trans alloc-stack-preserves
                   (trans store-preserves (trans mov-preserves rdi-eq)))

      mem-preserved-through-setup : ∀ loc → BeforeFrontier alloc loc →
        readLoc s-after-setup loc ≡ readLoc s loc
      mem-preserved-through-setup loc bf =
        let s₁ʳ = proj₁ (exec-abstract mov-to-output s alloc)
            alloc₁ʳ = proj₂ (exec-abstract mov-to-output s alloc)
            not-halted₁ʳ = exec-abstract-preserves-halted mov-to-output s alloc not-halted iph-mov-to-output
            mov-mem : readLoc s₁ʳ loc ≡ readLoc s loc
            mov-mem = SMP.RecSchemeSemantics.exec-abstract-mov-to-output-preserves-mem s alloc loc
            frame-eq : current-frame alloc₁ʳ ≡ current-frame alloc
            frame-eq = exec-abstract-preserves-frame mov-to-output s alloc
            loc≢slot : loc ≢ AtStack (current-frame alloc₁ʳ) backup-slot
            loc≢slot eq = fresh-stack-after alloc loc bf
                            (trans eq (cong (λ fr → AtStack fr backup-slot) frame-eq))
            s₂ʳ = proj₁ (exec-abstract (store-at-slot backup-slot) s₁ʳ alloc₁ʳ)
            alloc₂ʳ = proj₂ (exec-abstract (store-at-slot backup-slot) s₁ʳ alloc₁ʳ)
            not-halted₂ʳ = exec-abstract-preserves-halted (store-at-slot backup-slot) s₁ʳ alloc₁ʳ not-halted₁ʳ iph-store-at-slot
            store-mem : readLoc s₂ʳ loc ≡ readLoc s₁ʳ loc
            store-mem = exec-abstract-store-at-slot-preserves-loc backup-slot s₁ʳ alloc₁ʳ loc loc≢slot
            s₃ʳ = proj₁ (exec-abstract (instr-alloc-stack pair-overhead) s₂ʳ alloc₂ʳ)
            alloc-stack-mem : readLoc s₃ʳ loc ≡ readLoc s₂ʳ loc
            alloc-stack-mem = ExecLemmas.readLoc-stackMem-eq s₃ʳ s₂ʳ loc refl refl
            setup-decomp : exec-trace setup-trace s alloc ≡
                           exec-trace (store-at-slot backup-slot ∷ instr-alloc-stack pair-overhead ∷ []) s₁ʳ alloc₁ʳ
            setup-decomp = exec-trace-cons mov-to-output (store-at-slot backup-slot ∷ instr-alloc-stack pair-overhead ∷ []) s alloc not-halted
            store-decomp : exec-trace (store-at-slot backup-slot ∷ instr-alloc-stack pair-overhead ∷ []) s₁ʳ alloc₁ʳ ≡
                           exec-trace (instr-alloc-stack pair-overhead ∷ []) s₂ʳ alloc₂ʳ
            store-decomp = exec-trace-cons (store-at-slot backup-slot) (instr-alloc-stack pair-overhead ∷ []) s₁ʳ alloc₁ʳ not-halted₁ʳ
            alloc-single : exec-trace (instr-alloc-stack pair-overhead ∷ []) s₂ʳ alloc₂ʳ ≡
                           exec-abstract (instr-alloc-stack pair-overhead) s₂ʳ alloc₂ʳ
            alloc-single = exec-trace-single (instr-alloc-stack pair-overhead) s₂ʳ alloc₂ʳ not-halted₂ʳ
            s-eq : s-after-setup ≡ s₃ʳ
            s-eq = cong proj₁ (trans setup-decomp (trans store-decomp alloc-single))
        in trans (cong (λ st → readLoc st loc) s-eq) (trans alloc-stack-mem (trans store-mem mov-mem))

    -- Layout monotonicity bridges (non-abstract — these are short and used
    -- definitionally in dependent types).
    bf-to-after-pair-slots : ∀ loc → BeforeFrontier alloc loc → BeforeFrontier alloc-after-pair-slots loc
    bf-to-after-pair-slots loc bf = frontier-monotone alloc alloc-after-pair-slots refl
                                      (≤-trans (n≤1+n backup-slot) (≤-trans (n≤1+n fst-slot) (n≤1+n snd-slot)))
                                      ≤-refl loc bf

    input-before-at-f-start : BeforeFrontier alloc-after-pair-slots input-loc
    input-before-at-f-start = bf-to-after-pair-slots input-loc input-before

    input-valid-wf-at-f-start : ValidAtWF mIn alloc-after-pair-slots x input-loc s
    input-valid-wf-at-f-start = validityWF-frontier-advance x input-loc s refl
                                  (≤-trans (n≤1+n backup-slot) (≤-trans (n≤1+n fst-slot) (n≤1+n snd-slot)))
                                  ≤-refl input-valid-wf

    input-valid-wf-after-setup : ValidAtWF mIn alloc-after-pair-slots x input-loc s-after-setup
    input-valid-wf-after-setup =
      validityWF-frontier-advance x input-loc s-after-setup refl
        (≤-trans (n≤1+n backup-slot) (≤-trans (n≤1+n fst-slot) (n≤1+n snd-slot)))
        ≤-refl
        (validityWF-mem-preserved x input-loc s s-after-setup input-before
          mem-preserved-through-setup
          input-valid-wf)

    ----------------------------------------------------------------------
    -- L2 — after f-exec + middle prep
    ----------------------------------------------------------------------
    module L2
      (mF : AllocMode)
      (result-f : IRResultAWF mF f x s-after-setup alloc-after-pair-slots)
      -- FstFacts (renamed for direct use)
      (fst-loc : ValueLocation FS)
      (fst-rax-eq :
        readReg (regs (IRResultAWF.final-state result-f)) Output ≡
        SV-Ptr fst-loc)
      (fst-valid-from-f :
        ValidAtWF mF (IRResultAWF.final-alloc result-f) (eval f x)
                     fst-loc (IRResultAWF.final-state result-f))
      (fst-before-pre-from-f :
        BeforeFrontier (IRResultAWF.final-alloc result-f) fst-loc)
      (fst-rec-valid-from-f :
        ValidAtWF mF
          (record alloc-after-pair-slots
            { next-slot     = next-slot     (IRResultAWF.final-alloc result-f)
            ; next-heap-ref = next-heap-ref (IRResultAWF.final-alloc result-f) })
          (eval f x) fst-loc (IRResultAWF.final-state result-f))
      (fst-rec-before-from-f :
        BeforeFrontier
          (record alloc-after-pair-slots
            { next-slot     = next-slot     (IRResultAWF.final-alloc result-f)
            ; next-heap-ref = next-heap-ref (IRResultAWF.final-alloc result-f) })
          fst-loc)
      -- f-tnhw cannot be derived from result-f projections; pass as primitive
      (f-tnhw : TraceNoHeapWrites (IRResultAWF.trace result-f))
      where

      -- Phase 3 derived
      f-trace : AbstractTrace
      f-trace = IRResultAWF.trace result-f

      s₁ : LocState FS
      s₁ = IRResultAWF.final-state result-f

      max-slot-f : ℕ
      max-slot-f = IRResultAWF.max-slot-written result-f

      f-twa : TraceWritesAbove f-start f-trace
      f-twa = IRResultAWF.trace-writes-above result-f

      f-twb : TraceWritesBelow max-slot-f f-trace
      f-twb = IRResultAWF.trace-writes-below result-f

      f-tsra : TraceSlotReadsAbove f-start f-trace
      f-tsra = IRResultAWF.trace-slot-reads-above result-f

      f-tsrb : TraceSlotReadsBelow max-slot-f f-trace
      f-tsrb = IRResultAWF.trace-slot-reads-below result-f

      reclaim-f : ℕ
      reclaim-f = next-slot (IRResultAWF.final-alloc result-f)

      reclaim-f-above-f-start : f-start ≤ reclaim-f
      reclaim-f-above-f-start = IRResultAWF.slot-monotone result-f

      alloc-after-f-reclaim : AllocState {FS}
      alloc-after-f-reclaim = record alloc
        { next-slot     = reclaim-f
        ; next-heap-ref = next-heap-ref (IRResultAWF.final-alloc result-f) }

      f-tph : TraceWF s-after-setup alloc-after-pair-slots f-trace
      f-tph = IRResultAWF.trace-twf result-f

      f-frame-eq : current-frame alloc-after-pair-slots ≡
                   current-frame alloc-after-setup
      f-frame-eq = trans refl (sym (exec-trace-preserves-frame setup-trace s alloc))

      f-tph-runtime : TraceWF s-after-setup alloc-after-setup f-trace
      f-tph-runtime = TraceWF-frame-eq f-frame-eq f-tph

      s-after-f : LocState FS
      s-after-f = proj₁ (exec-trace f-trace s-after-setup alloc-after-setup)

      alloc-after-f : AllocState {FS}
      alloc-after-f = proj₂ (exec-trace f-trace s-after-setup alloc-after-setup)

      not-halted-after-f : halted s-after-f ≡ false
      not-halted-after-f = exec-trace-preserves-halted-WF f-trace
                             s-after-setup alloc-after-setup
                             not-halted-after-setup f-tph-runtime

      s-after-fst-store : LocState FS
      s-after-fst-store = proj₁ (exec-abstract (store-at-slot fst-slot)
                                  s-after-f alloc-after-f)

      alloc-after-fst-store : AllocState {FS}
      alloc-after-fst-store = proj₂ (exec-abstract (store-at-slot fst-slot)
                                       s-after-f alloc-after-f)

      -- middle-trace is concrete; derive it + its TraceWF.
      middle-trace : AbstractTrace
      middle-trace = store-at-slot fst-slot ∷ restore-input backup-slot ∷ []

      ------------------------------------------------------------------
      -- Plan 0.18 wire-through: derive mri-* + middle-restore-input-witness
      -- internally (previously passed in as L2 params from PairWF2).
      -- Wrapped in `abstract` to keep downstream propositional only.
      ------------------------------------------------------------------
      abstract
        mri-backup-setup-stores :
          readLoc s-after-setup (AtStack (current-frame alloc) backup-slot) ≡
            just (readReg (regs s) Input1)
        mri-backup-setup-stores =
          let prefix-trace = mov-to-output ∷ store-at-slot backup-slot ∷ []
              s-after-prefix = proj₁ (exec-trace prefix-trace s alloc)
              alloc-after-prefix = proj₂ (exec-trace prefix-trace s alloc)
              prefix-stores : readLoc s-after-prefix (AtStack (current-frame alloc) backup-slot) ≡
                              just (readReg (regs s) Input1)
              prefix-stores = SMP.RecSchemeSemantics.rec-scheme-stores-input backup-slot s alloc not-halted
              prefix-twf : TraceWF s alloc prefix-trace
              prefix-twf = twf-∷ tt (twf-∷ tt twf-[])
              not-halted-prefix : halted s-after-prefix ≡ false
              not-halted-prefix = exec-trace-preserves-halted-WF prefix-trace s alloc not-halted prefix-twf
              alloc-step-mem : readLoc (proj₁ (exec-abstract (instr-alloc-stack pair-overhead) s-after-prefix alloc-after-prefix))
                                       (AtStack (current-frame alloc) backup-slot) ≡
                               readLoc s-after-prefix (AtStack (current-frame alloc) backup-slot)
              alloc-step-mem = ExecLemmas.readLoc-stackMem-eq
                                 (proj₁ (exec-abstract (instr-alloc-stack pair-overhead) s-after-prefix alloc-after-prefix))
                                 s-after-prefix
                                 (AtStack (current-frame alloc) backup-slot) refl refl
              setup-eq : exec-trace setup-trace s alloc ≡
                         exec-abstract (instr-alloc-stack pair-overhead) s-after-prefix alloc-after-prefix
              setup-eq =
                trans (exec-trace-append prefix-trace (instr-alloc-stack pair-overhead ∷ []) s alloc)
                      (exec-trace-single (instr-alloc-stack pair-overhead) s-after-prefix alloc-after-prefix not-halted-prefix)
              s-eq : s-after-setup ≡ proj₁ (exec-abstract (instr-alloc-stack pair-overhead) s-after-prefix alloc-after-prefix)
              s-eq = cong proj₁ setup-eq
          in trans (cong (λ st → readLoc st (AtStack (current-frame alloc) backup-slot)) s-eq)
                   (trans alloc-step-mem prefix-stores)

        mri-backup-setup-has-input : readLoc s-after-setup (AtStack frame backup-slot) ≡ just (SV-Ptr input-loc)
        mri-backup-setup-has-input = trans mri-backup-setup-stores (cong just rdi-eq)

        mri-backup<f-start : backup-slot < f-start
        mri-backup<f-start = ≤-trans (n≤1+n fst-slot) (n≤1+n snd-slot)

        mri-frame-setup-eq : current-frame alloc-after-setup ≡ frame
        mri-frame-setup-eq = exec-trace-preserves-frame setup-trace s alloc

        mri-f-preserves-backup :
          readLoc s-after-f (AtStack (current-frame alloc-after-setup) backup-slot) ≡
          readLoc s-after-setup (AtStack (current-frame alloc-after-setup) backup-slot)
        mri-f-preserves-backup = exec-trace-preserves-slot-below f-trace s-after-setup alloc-after-setup
                                   f-start backup-slot f-twa f-tnhw mri-backup<f-start

        mri-f-has-input-at-backup : readLoc s-after-f (AtStack frame backup-slot) ≡ just (SV-Ptr input-loc)
        mri-f-has-input-at-backup =
          trans (subst (λ fr → readLoc s-after-f (AtStack fr backup-slot) ≡
                               readLoc s-after-setup (AtStack fr backup-slot))
                       mri-frame-setup-eq mri-f-preserves-backup)
                mri-backup-setup-has-input

        mri-frame-f-eq : current-frame alloc-after-f ≡ frame
        mri-frame-f-eq = trans (exec-trace-preserves-frame f-trace s-after-setup alloc-after-setup)
                               mri-frame-setup-eq

        mri-store-fst-preserves-backup :
          readLoc s-after-fst-store (AtStack frame backup-slot) ≡
          readLoc s-after-f (AtStack frame backup-slot)
        mri-store-fst-preserves-backup =
          subst (λ fr → readLoc s-after-fst-store (AtStack fr backup-slot) ≡
                        readLoc s-after-f (AtStack fr backup-slot))
                mri-frame-f-eq
                (store-at-slot-preserves-other fst-slot backup-slot s-after-f alloc-after-f
                                                (inj₂ (≤-refl {x = fst-slot})))

        mri-fst-store-has-input : readLoc s-after-fst-store (AtStack frame backup-slot) ≡
                                   just (SV-Ptr input-loc)
        mri-fst-store-has-input = trans mri-store-fst-preserves-backup mri-f-has-input-at-backup

        mri-frame-fst-store-eq : current-frame alloc-after-fst-store ≡ frame
        mri-frame-fst-store-eq = trans (exec-abstract-preserves-frame (store-at-slot fst-slot) s-after-f alloc-after-f)
                                       mri-frame-f-eq

        mri-backup-witness-at-fst-store :
          readLoc s-after-fst-store (AtStack (current-frame alloc-after-fst-store) backup-slot) ≡
          just (SV-Ptr input-loc)
        mri-backup-witness-at-fst-store =
          subst (λ fr → readLoc s-after-fst-store (AtStack fr backup-slot) ≡ just (SV-Ptr input-loc))
                (sym mri-frame-fst-store-eq)
                mri-fst-store-has-input

      middle-restore-input-witness :
        InstrWF s-after-fst-store alloc-after-fst-store (restore-input backup-slot)
      middle-restore-input-witness = (SV-Ptr input-loc , mri-backup-witness-at-fst-store)

      middle-twf : TraceWF s-after-f alloc-after-f middle-trace
      middle-twf = twf-∷ tt (twf-∷ middle-restore-input-witness twf-[])

      s-after-middle : LocState FS
      s-after-middle = proj₁ (exec-trace middle-trace s-after-f alloc-after-f)

      alloc-after-middle : AllocState {FS}
      alloc-after-middle = proj₂ (exec-trace middle-trace s-after-f alloc-after-f)

      not-halted-after-middle : halted s-after-middle ≡ false
      not-halted-after-middle = exec-trace-preserves-halted-WF middle-trace
                                  s-after-f alloc-after-f
                                  not-halted-after-f middle-twf

      -- Post-hoist alias (Plan 0.13.3): s₁' is s-after-middle.
      s₁' : LocState FS
      s₁' = s-after-middle

      ------------------------------------------------------------------
      -- Plan 0.18 wire-through: rdi-eq-at-s-after-middle derived internally
      -- (previously passed as L3 param from PairWF2).
      ------------------------------------------------------------------
      abstract
        rdi-not-halted-fst-store : halted s-after-fst-store ≡ false
        rdi-not-halted-fst-store = trans (store-at-slot-halted fst-slot s-after-f alloc-after-f) not-halted-after-f

        rdi-restore-sets-input :
          readReg (regs (proj₁ (exec-abstract (restore-input backup-slot)
                                                s-after-fst-store alloc-after-fst-store))) Input1
            ≡ SV-Ptr input-loc
        rdi-restore-sets-input =
          SMP.RecSchemeSemantics.exec-abstract-restore-input-sets-input
            backup-slot s-after-fst-store alloc-after-fst-store (SV-Ptr input-loc)
            mri-backup-witness-at-fst-store

        rdi-middle-decomp : exec-trace middle-trace s-after-f alloc-after-f ≡
                            exec-trace (restore-input backup-slot ∷ []) s-after-fst-store alloc-after-fst-store
        rdi-middle-decomp = exec-trace-cons (store-at-slot fst-slot) (restore-input backup-slot ∷ [])
                                            s-after-f alloc-after-f not-halted-after-f

        rdi-restore-single :
          exec-trace (restore-input backup-slot ∷ []) s-after-fst-store alloc-after-fst-store ≡
          exec-abstract (restore-input backup-slot) s-after-fst-store alloc-after-fst-store
        rdi-restore-single = exec-trace-single (restore-input backup-slot) s-after-fst-store alloc-after-fst-store
                                                rdi-not-halted-fst-store

        rdi-s-middle-eq : s-after-middle ≡
                          proj₁ (exec-abstract (restore-input backup-slot) s-after-fst-store alloc-after-fst-store)
        rdi-s-middle-eq = cong proj₁ (trans rdi-middle-decomp rdi-restore-single)

        rdi-eq-at-s-after-middle : readReg (regs s-after-middle) Input1 ≡ SV-Ptr input-loc
        rdi-eq-at-s-after-middle =
          trans (cong (λ st → readReg (regs st) Input1) rdi-s-middle-eq) rdi-restore-sets-input

      ------------------------------------------------------------------
      -- Plan 0.18 wire-through: valid-at-s-after-middle for g's rec-wf call.
      -- Bridges input-loc validity through setup + f + middle.
      ------------------------------------------------------------------
      input-before-at-reclaim-f : BeforeFrontier alloc-after-f-reclaim input-loc
      input-before-at-reclaim-f = frontier-monotone alloc alloc-after-f-reclaim refl
                                    (≤-trans (n≤1+n backup-slot)
                                      (≤-trans (n≤1+n fst-slot)
                                        (≤-trans (n≤1+n snd-slot) reclaim-f-above-f-start)))
                                    (IRResultAWF.heap-monotone result-f)
                                    input-loc input-before

      input-valid-wf-s1 : ValidAtWF mIn alloc x input-loc (IRResultAWF.final-state result-f)
      input-valid-wf-s1 = validityWF-mem-preserved x input-loc s (IRResultAWF.final-state result-f) input-before
                            (λ loc bf → trans (irresult-mem-preserved result-f loc (bf-to-after-pair-slots loc bf))
                                              (mem-preserved-through-setup loc bf))
                            input-valid-wf

      input-valid-wf-at-reclaim-f : ValidAtWF mIn alloc-after-f-reclaim x input-loc (IRResultAWF.final-state result-f)
      input-valid-wf-at-reclaim-f = validityWF-frontier-advance x input-loc (IRResultAWF.final-state result-f) refl
                                      (≤-trans (n≤1+n backup-slot)
                                        (≤-trans (n≤1+n fst-slot)
                                          (≤-trans (n≤1+n snd-slot) reclaim-f-above-f-start)))
                                      (IRResultAWF.heap-monotone result-f)
                                      input-valid-wf-s1

      abstract
        val-mid-frame-setup : current-frame alloc-after-setup ≡ frame
        val-mid-frame-setup = exec-trace-preserves-frame setup-trace s alloc

        val-mid-frame-pair-slots : current-frame alloc-after-pair-slots ≡ frame
        val-mid-frame-pair-slots = refl

        val-mid-frame-after-f : current-frame alloc-after-f ≡ frame
        val-mid-frame-after-f =
          trans (exec-trace-preserves-frame f-trace s-after-setup alloc-after-setup)
                val-mid-frame-setup

        val-mid-oaf-frame-eq : current-frame alloc-after-setup ≡ current-frame alloc-after-pair-slots
        val-mid-oaf-frame-eq = trans val-mid-frame-setup (sym val-mid-frame-pair-slots)

        val-mid-oaf-mem-trivial : ∀ slot → f-start ≤ slot → slot < IRResultAWF.max-slot-written result-f →
          readLoc s-after-setup (AtStack (current-frame alloc-after-setup) slot) ≡
          readLoc s-after-setup (AtStack (current-frame alloc-after-pair-slots) slot)
        val-mid-oaf-mem-trivial slot _ _ =
          cong (λ fr → readLoc s-after-setup (AtStack fr slot)) val-mid-oaf-frame-eq

        val-mid-twa : TraceWritesAbove fst-slot middle-trace
        val-mid-twa = ≤-refl , tt

        val-mid-twb : TraceWritesBelow f-start middle-trace
        val-mid-twb = (n≤1+n snd-slot) , tt

        val-mid-tnhw : TraceNoHeapWrites middle-trace
        val-mid-tnhw = tt

        val-mid-input-region : ∀ slot → slot < backup-slot →
          readLoc s-after-middle (AtStack frame slot) ≡ readLoc (IRResultAWF.final-state result-f) (AtStack frame slot)
        val-mid-input-region slot slot<backup =
          let backup≤f-start : backup-slot ≤ f-start
              backup≤f-start = ≤-trans (n≤1+n backup-slot)
                                       (≤-trans (n≤1+n fst-slot) (n≤1+n snd-slot))
              slot<f-start : slot < f-start
              slot<f-start = ≤-trans slot<backup backup≤f-start
              slot<fst : slot < fst-slot
              slot<fst = ≤-trans slot<backup (n≤1+n backup-slot)
              mid-pres : readLoc s-after-middle (AtStack (current-frame alloc-after-f) slot) ≡
                         readLoc s-after-f (AtStack (current-frame alloc-after-f) slot)
              mid-pres = SMP.TracePrimitives.exec-trace-preserves-slot-below middle-trace
                           s-after-f alloc-after-f fst-slot slot
                           val-mid-twa val-mid-tnhw slot<fst
              mid-pres-frame : readLoc s-after-middle (AtStack frame slot) ≡
                               readLoc s-after-f (AtStack frame slot)
              mid-pres-frame = subst (λ fr → readLoc s-after-middle (AtStack fr slot) ≡
                                             readLoc s-after-f (AtStack fr slot))
                                     val-mid-frame-after-f mid-pres
              f-pres : readLoc s-after-f (AtStack (current-frame alloc-after-setup) slot) ≡
                       readLoc s-after-setup (AtStack (current-frame alloc-after-setup) slot)
              f-pres = SMP.TracePrimitives.exec-trace-preserves-slot-below f-trace s-after-setup
                         alloc-after-setup f-start slot f-twa f-tnhw slot<f-start
              f-pres-frame : readLoc s-after-f (AtStack frame slot) ≡
                             readLoc s-after-setup (AtStack frame slot)
              f-pres-frame = subst (λ fr → readLoc s-after-f (AtStack fr slot) ≡
                                           readLoc s-after-setup (AtStack fr slot))
                                   val-mid-frame-setup f-pres
              exec-f-pres : readLoc (proj₁ (exec-trace f-trace s-after-setup alloc-after-pair-slots))
                              (AtStack (current-frame alloc-after-pair-slots) slot) ≡
                            readLoc s-after-setup (AtStack (current-frame alloc-after-pair-slots) slot)
              exec-f-pres = SMP.TracePrimitives.exec-trace-preserves-slot-below f-trace s-after-setup
                              alloc-after-pair-slots f-start slot f-twa f-tnhw slot<f-start
              exec-f-pres-frame : readLoc (proj₁ (exec-trace f-trace s-after-setup alloc-after-pair-slots))
                                    (AtStack frame slot) ≡
                                  readLoc s-after-setup (AtStack frame slot)
              exec-f-pres-frame = subst (λ fr → readLoc (proj₁ (exec-trace f-trace s-after-setup alloc-after-pair-slots))
                                                  (AtStack fr slot) ≡
                                                readLoc s-after-setup (AtStack fr slot))
                                        val-mid-frame-pair-slots exec-f-pres
              s₁-pres : readLoc (IRResultAWF.final-state result-f) (AtStack frame slot) ≡ readLoc s-after-setup (AtStack frame slot)
              s₁-pres = subst (λ st → readLoc st (AtStack frame slot) ≡ readLoc s-after-setup (AtStack frame slot))
                              (IRResultAWF.trace-correct result-f) exec-f-pres-frame
              s-after-f→s₁ : readLoc s-after-f (AtStack frame slot) ≡ readLoc (IRResultAWF.final-state result-f) (AtStack frame slot)
              s-after-f→s₁ = trans f-pres-frame (sym s₁-pres)
          in trans mid-pres-frame s-after-f→s₁

        val-mid-fresh-region : ∀ slot → f-start ≤ slot → slot < reclaim-f →
          readLoc s-after-middle (AtStack frame slot) ≡ readLoc (IRResultAWF.final-state result-f) (AtStack frame slot)
        val-mid-fresh-region slot f-start≤slot slot<reclaim =
          let slot<max : slot < IRResultAWF.max-slot-written result-f
              slot<max = <-≤-trans slot<reclaim (IRResultAWF.max-slot-geq-final result-f)
              mid-pres : readLoc s-after-middle (AtStack (current-frame alloc-after-f) slot) ≡
                         readLoc s-after-f (AtStack (current-frame alloc-after-f) slot)
              mid-pres = SMP.TracePrimitives.exec-trace-preserves-slot-above middle-trace
                           s-after-f alloc-after-f f-start slot
                           val-mid-twb val-mid-tnhw f-start≤slot
              mid-pres-frame : readLoc s-after-middle (AtStack frame slot) ≡
                               readLoc s-after-f (AtStack frame slot)
              mid-pres-frame = subst (λ fr → readLoc s-after-middle (AtStack fr slot) ≡
                                             readLoc s-after-f (AtStack fr slot))
                                     val-mid-frame-after-f mid-pres
              mem-det : readLoc s-after-f (AtStack (current-frame alloc-after-setup) slot) ≡
                        readLoc (proj₁ (exec-trace f-trace s-after-setup alloc-after-pair-slots))
                                (AtStack (current-frame alloc-after-pair-slots) slot)
              mem-det = SMP.TraceOutputDeterminism.exec-trace-mem-deterministic f-trace
                          s-after-setup s-after-setup alloc-after-setup alloc-after-pair-slots
                          f-start (IRResultAWF.max-slot-written result-f)
                          not-halted-after-setup not-halted-after-setup
                          val-mid-oaf-frame-eq refl
                          f-tsra f-tsrb f-twa f-twb f-tnhw
                          val-mid-oaf-mem-trivial
                          slot f-start≤slot slot<max
              mem-det-frame : readLoc s-after-f (AtStack frame slot) ≡
                              readLoc (proj₁ (exec-trace f-trace s-after-setup alloc-after-pair-slots))
                                      (AtStack frame slot)
              mem-det-frame = subst₂ (λ f1 f2 → readLoc s-after-f (AtStack f1 slot) ≡
                                                readLoc (proj₁ (exec-trace f-trace s-after-setup alloc-after-pair-slots))
                                                        (AtStack f2 slot))
                                     val-mid-frame-setup val-mid-frame-pair-slots mem-det
              s₁-eq : readLoc (proj₁ (exec-trace f-trace s-after-setup alloc-after-pair-slots))
                              (AtStack frame slot) ≡
                      readLoc (IRResultAWF.final-state result-f) (AtStack frame slot)
              s₁-eq = cong (λ st → readLoc st (AtStack frame slot)) (IRResultAWF.trace-correct result-f)
              s-after-f→s₁ : readLoc s-after-f (AtStack frame slot) ≡ readLoc (IRResultAWF.final-state result-f) (AtStack frame slot)
              s-after-f→s₁ = trans mem-det-frame s₁-eq
          in trans mid-pres-frame s-after-f→s₁

        val-mid-heap : ∀ h → readLoc s-after-middle (AtDynamic h) ≡ readLoc (IRResultAWF.final-state result-f) (AtDynamic h)
        val-mid-heap h =
          let mid-pres : readLoc s-after-middle (AtDynamic h) ≡ readLoc s-after-f (AtDynamic h)
              mid-pres = SMP.TracePrimitives.exec-trace-preserves-heap-loc middle-trace
                           s-after-f alloc-after-f h val-mid-tnhw
              f-pres : readLoc s-after-f (AtDynamic h) ≡ readLoc s-after-setup (AtDynamic h)
              f-pres = SMP.TracePrimitives.exec-trace-preserves-heap-loc f-trace s-after-setup
                         alloc-after-setup h f-tnhw
              exec-f-pres : readLoc (proj₁ (exec-trace f-trace s-after-setup alloc-after-pair-slots))
                              (AtDynamic h) ≡
                            readLoc s-after-setup (AtDynamic h)
              exec-f-pres = SMP.TracePrimitives.exec-trace-preserves-heap-loc f-trace s-after-setup
                              alloc-after-pair-slots h f-tnhw
              s₁-pres : readLoc (IRResultAWF.final-state result-f) (AtDynamic h) ≡ readLoc s-after-setup (AtDynamic h)
              s₁-pres = subst (λ st → readLoc st (AtDynamic h) ≡ readLoc s-after-setup (AtDynamic h))
                              (IRResultAWF.trace-correct result-f) exec-f-pres
              s-after-f→s₁ : readLoc s-after-f (AtDynamic h) ≡ readLoc (IRResultAWF.final-state result-f) (AtDynamic h)
              s-after-f→s₁ = trans f-pres (sym s₁-pres)
          in trans mid-pres s-after-f→s₁

        val-mid-ancestors : ∀ f' k → current-frame alloc-after-f-reclaim ≺ f' →
          readLoc s-after-middle (AtStack f' k) ≡ readLoc (IRResultAWF.final-state result-f) (AtStack f' k)
        val-mid-ancestors f' k cf≺f' =
          let frame≺f' : frame ≺ f'
              frame≺f' = cf≺f'
              alloc-after-f-cf≺f' : current-frame alloc-after-f ≺ f'
              alloc-after-f-cf≺f' = subst (_≺ f') (sym val-mid-frame-after-f) frame≺f'
              mid-pres : readLoc s-after-middle (AtStack f' k) ≡ readLoc s-after-f (AtStack f' k)
              mid-pres = SMP.TracePrimitives.exec-trace-preserves-ancestor middle-trace
                           s-after-f alloc-after-f f' k alloc-after-f-cf≺f' val-mid-tnhw
              alloc-after-setup-cf≺f' : current-frame alloc-after-setup ≺ f'
              alloc-after-setup-cf≺f' = subst (_≺ f') (sym val-mid-frame-setup) frame≺f'
              f-pres : readLoc s-after-f (AtStack f' k) ≡ readLoc s-after-setup (AtStack f' k)
              f-pres = SMP.TracePrimitives.exec-trace-preserves-ancestor f-trace s-after-setup
                         alloc-after-setup f' k alloc-after-setup-cf≺f' f-tnhw
              alloc-pair-slots-cf≺f' : current-frame alloc-after-pair-slots ≺ f'
              alloc-pair-slots-cf≺f' = subst (_≺ f') (sym val-mid-frame-pair-slots) frame≺f'
              exec-f-pres : readLoc (proj₁ (exec-trace f-trace s-after-setup alloc-after-pair-slots))
                              (AtStack f' k) ≡
                            readLoc s-after-setup (AtStack f' k)
              exec-f-pres = SMP.TracePrimitives.exec-trace-preserves-ancestor f-trace s-after-setup
                              alloc-after-pair-slots f' k alloc-pair-slots-cf≺f' f-tnhw
              s₁-pres : readLoc (IRResultAWF.final-state result-f) (AtStack f' k) ≡ readLoc s-after-setup (AtStack f' k)
              s₁-pres = subst (λ st → readLoc st (AtStack f' k) ≡ readLoc s-after-setup (AtStack f' k))
                              (IRResultAWF.trace-correct result-f) exec-f-pres
              s-after-f→s₁ : readLoc s-after-f (AtStack f' k) ≡ readLoc (IRResultAWF.final-state result-f) (AtStack f' k)
              s-after-f→s₁ = trans f-pres (sym s₁-pres)
          in trans mid-pres s-after-f→s₁

        val-mid-backup≤f-start : backup-slot ≤ f-start
        val-mid-backup≤f-start = ≤-trans (n≤1+n backup-slot)
                                         (≤-trans (n≤1+n fst-slot) (n≤1+n snd-slot))

        val-mid-f-start≤reclaim-f : f-start ≤ reclaim-f
        val-mid-f-start≤reclaim-f = reclaim-f-above-f-start

        valid-at-s-after-middle : ValidAtWF mIn alloc-after-f-reclaim x input-loc s-after-middle
        valid-at-s-after-middle =
          validityWF-mem-preserved-in-regions alloc-after-f-reclaim
            x input-loc backup-slot f-start (IRResultAWF.final-state result-f) s-after-middle
            input-before-at-reclaim-f
            val-mid-backup≤f-start val-mid-f-start≤reclaim-f
            val-mid-input-region val-mid-fresh-region val-mid-heap val-mid-ancestors
            input-valid-wf-at-reclaim-f

      --------------------------------------------------------------------
      -- L3 — after g-exec + final prep
      --------------------------------------------------------------------
      module L3
        (mG : AllocMode)
        (result-g : IRResultAWF mG g x s-after-middle alloc-after-f-reclaim)
        -- SndFacts (only the ones the validity chain uses)
        (snd-loc : ValueLocation FS)
        (snd-rax-eq :
          readReg (regs (IRResultAWF.final-state result-g)) Output ≡
          SV-Ptr snd-loc)
        (snd-rec-valid-from-g :
          ValidAtWF mG
            (record alloc-after-f-reclaim
              { next-slot     = next-slot     (IRResultAWF.final-alloc result-g)
              ; next-heap-ref = next-heap-ref (IRResultAWF.final-alloc result-g) })
            (eval g x) snd-loc (IRResultAWF.final-state result-g))
        (snd-rec-before-from-g :
          BeforeFrontier
            (record alloc-after-f-reclaim
              { next-slot     = next-slot     (IRResultAWF.final-alloc result-g)
              ; next-heap-ref = next-heap-ref (IRResultAWF.final-alloc result-g) })
            snd-loc)
        -- g-tnhw primitive (others derivable)
        (g-tnhw : TraceNoHeapWrites (IRResultAWF.trace result-g))
        -- Final-state bundle.
        -- PairWF2 defines s-final via pair-trace (the whole composed trace);
        -- Validity only needs the equality with the chained version.
        (s-final : LocState FS)
        (s-final-eq-prim :
          s-final ≡ proj₁ (exec-trace
            (store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
            (proj₁ (exec-trace (IRResultAWF.trace result-g)
                     s-after-middle alloc-after-middle))
            (proj₂ (exec-trace (IRResultAWF.trace result-g)
                     s-after-middle alloc-after-middle))))
        where

        -- The s₁'-call's halted precondition is just not-halted-after-middle.
        not-halted-at-s-after-middle : halted s-after-middle ≡ false
        not-halted-at-s-after-middle = not-halted-after-middle

        -- Phase 4 derived
        g-trace : AbstractTrace
        g-trace = IRResultAWF.trace result-g

        s₂ : LocState FS
        s₂ = IRResultAWF.final-state result-g

        max-slot-g : ℕ
        max-slot-g = IRResultAWF.max-slot-written result-g

        reclaim-g : ℕ
        reclaim-g = next-slot (IRResultAWF.final-alloc result-g)

        g-twa : TraceWritesAbove reclaim-f g-trace
        g-twa = IRResultAWF.trace-writes-above result-g

        g-twb : TraceWritesBelow max-slot-g g-trace
        g-twb = IRResultAWF.trace-writes-below result-g

        g-tsra : TraceSlotReadsAbove reclaim-f g-trace
        g-tsra = IRResultAWF.trace-slot-reads-above result-g

        alloc-final : AllocState {FS}
        alloc-final = record alloc
          { next-slot     = reclaim-g
          ; next-heap-ref = next-heap-ref (IRResultAWF.final-alloc result-g) }

        final-trace : AbstractTrace
        final-trace = store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []

        s-after-g : LocState FS
        s-after-g = proj₁ (exec-trace g-trace s-after-middle alloc-after-middle)

        alloc-after-g : AllocState {FS}
        alloc-after-g = proj₂ (exec-trace g-trace s-after-middle alloc-after-middle)

        s-after-snd-store : LocState FS
        s-after-snd-store = proj₁ (exec-abstract (store-at-slot snd-slot)
                                     s-after-g alloc-after-g)

        alloc-after-snd-store : AllocState {FS}
        alloc-after-snd-store = proj₂ (exec-abstract (store-at-slot snd-slot)
                                         s-after-g alloc-after-g)

        s-after-final : LocState FS
        s-after-final = proj₁ (exec-trace final-trace s-after-g alloc-after-g)

        -- Slot ordering facts used by the validity proofs
        fst-slot<reclaim-f : fst-slot < reclaim-f
        fst-slot<reclaim-f = ≤-trans (n≤1+n snd-slot) reclaim-f-above-f-start

        snd-slot<reclaim-f : snd-slot < reclaim-f
        snd-slot<reclaim-f = reclaim-f-above-f-start

        backup≤reclaim-f : backup-slot ≤ reclaim-f
        backup≤reclaim-f = ≤-trans (n≤1+n backup-slot)
                            (≤-trans (n≤1+n fst-slot)
                              (≤-trans (n≤1+n snd-slot) reclaim-f-above-f-start))

        snd<reclaim-g : snd-slot < reclaim-g
        snd<reclaim-g = <-≤-trans snd-slot<reclaim-f
                          (IRResultAWF.slot-monotone result-g)

        -- Frame chain: g preserves, middle preserves, f preserves,
        -- setup preserves; alloc-after-pair-slots has same current-frame
        -- as alloc by record-update.
        frame-after-g : current-frame alloc-after-g ≡ frame
        frame-after-g =
          trans (exec-trace-preserves-frame g-trace s-after-middle alloc-after-middle)
            (trans (exec-trace-preserves-frame middle-trace s-after-f alloc-after-f)
              (trans (exec-trace-preserves-frame f-trace s-after-setup alloc-after-setup)
                (exec-trace-preserves-frame setup-trace s alloc)))

        frame-preserved-through : current-frame alloc-after-snd-store ≡ frame
        frame-preserved-through =
          trans (exec-abstract-preserves-frame (store-at-slot snd-slot)
                  s-after-g alloc-after-g) frame-after-g

        -- s-final-eq is propositional; the original was definitional via
        -- pair-trace decomposition, but Validity only needs the equality.
        s-final-eq : s-final ≡ s-after-final
        s-final-eq = s-final-eq-prim

        g-frame-eq : current-frame alloc-after-f-reclaim ≡
                     current-frame alloc-after-middle
        g-frame-eq = sym
          (trans (exec-trace-preserves-frame middle-trace s-after-f alloc-after-f)
            (trans (exec-trace-preserves-frame f-trace s-after-setup alloc-after-setup)
              (exec-trace-preserves-frame setup-trace s alloc)))

        g-tph-runtime : TraceWF s-after-middle alloc-after-middle g-trace
        g-tph-runtime = TraceWF-frame-eq g-frame-eq (IRResultAWF.trace-twf result-g)

        not-halted-after-g : halted s-after-g ≡ false
        not-halted-after-g = exec-trace-preserves-halted-WF g-trace
                               s-after-middle alloc-after-middle
                               not-halted-after-middle g-tph-runtime

        not-halted-after-snd-store : halted s-after-snd-store ≡ false
        not-halted-after-snd-store = trans (store-at-slot-halted snd-slot
                                              s-after-g alloc-after-g)
                                          not-halted-after-g

        final-trace-decomp : exec-trace final-trace s-after-g alloc-after-g ≡
                             exec-trace (lea-slot fst-slot ∷ [])
                               s-after-snd-store alloc-after-snd-store
        final-trace-decomp = exec-trace-cons (store-at-slot snd-slot)
                               (lea-slot fst-slot ∷ [])
                               s-after-g alloc-after-g not-halted-after-g

        lea-single : exec-trace (lea-slot fst-slot ∷ [])
                       s-after-snd-store alloc-after-snd-store ≡
                     exec-abstract (lea-slot fst-slot)
                       s-after-snd-store alloc-after-snd-store
        lea-single = exec-trace-single (lea-slot fst-slot)
                       s-after-snd-store alloc-after-snd-store
                       not-halted-after-snd-store

        s-after-final-eq : s-after-final ≡
                           proj₁ (exec-abstract (lea-slot fst-slot)
                                   s-after-snd-store alloc-after-snd-store)
        s-after-final-eq = cong proj₁ (trans final-trace-decomp lea-single)

        --------------------------------------------------------------------
        -- Migrated phase 9-11 proofs (PairWF2.agda lines 1769-2823)
        --------------------------------------------------------------------
        oaf-frame-eq : current-frame alloc-after-setup ≡ current-frame alloc-after-pair-slots
        oaf-frame-eq = trans (exec-trace-preserves-frame setup-trace s alloc) refl
  
        -- Input1 preservation through setup-trace (mov-to-output and store-at-slot don't modify Input1)
        oaf-input-preserved : readReg (regs s-after-setup) Input1 ≡ readReg (regs s) Input1
        oaf-input-preserved =
          let s₁' = proj₁ (exec-abstract mov-to-output s alloc)
              alloc₁' = proj₂ (exec-abstract mov-to-output s alloc)
              mov-preserves-input : readReg (regs s₁') Input1 ≡ readReg (regs s) Input1
              mov-preserves-input = writeReg-preserves (regs s) Output Input1 (readReg (regs s) Input1) (λ ())
              not-halted₁' = exec-abstract-preserves-halted mov-to-output s alloc not-halted iph-mov-to-output
              s₂' = proj₁ (exec-abstract (store-at-slot backup-slot) s₁' alloc₁')
              alloc₂' = proj₂ (exec-abstract (store-at-slot backup-slot) s₁' alloc₁')
              store-preserves-input : readReg (regs s₂') Input1 ≡ readReg (regs s₁') Input1
              store-preserves-input = exec-abstract-store-at-slot-preserves-input backup-slot s₁' alloc₁'
              not-halted₂' = exec-abstract-preserves-halted (store-at-slot backup-slot) s₁' alloc₁' not-halted₁' iph-store-at-slot
              s₃' = proj₁ (exec-abstract (instr-alloc-stack pair-overhead) s₂' alloc₂')
              alloc-stack-preserves-input : readReg (regs s₃') Input1 ≡ readReg (regs s₂') Input1
              alloc-stack-preserves-input = refl
              setup-decomp : exec-trace setup-trace s alloc ≡
                             exec-trace (store-at-slot backup-slot ∷ instr-alloc-stack pair-overhead ∷ []) s₁' alloc₁'
              setup-decomp = exec-trace-cons mov-to-output (store-at-slot backup-slot ∷ instr-alloc-stack pair-overhead ∷ []) s alloc not-halted
              store-decomp : exec-trace (store-at-slot backup-slot ∷ instr-alloc-stack pair-overhead ∷ []) s₁' alloc₁' ≡
                             exec-trace (instr-alloc-stack pair-overhead ∷ []) s₂' alloc₂'
              store-decomp = exec-trace-cons (store-at-slot backup-slot) (instr-alloc-stack pair-overhead ∷ []) s₁' alloc₁' not-halted₁'
              alloc-single : exec-trace (instr-alloc-stack pair-overhead ∷ []) s₂' alloc₂' ≡
                             exec-abstract (instr-alloc-stack pair-overhead) s₂' alloc₂'
              alloc-single = exec-trace-single (instr-alloc-stack pair-overhead) s₂' alloc₂' not-halted₂'
              s-setup-eq : s-after-setup ≡ s₃'
              s-setup-eq = cong proj₁ (trans setup-decomp (trans store-decomp alloc-single))
          in trans (cong (λ st → readReg (regs st) Input1) s-setup-eq)
                   (trans alloc-stack-preserves-input
                     (trans store-preserves-input mov-preserves-input))
  
        -- Memory agreement at [f-start, max-slot-f): setup writes only at backup-slot < f-start
        -- Both frames are equal to `frame`:
        -- - current-frame alloc-after-setup ≡ frame (via exec-trace-preserves-frame)
        -- - current-frame alloc-after-pair-slots ≡ frame (by definition, only next-slot changed)
        oaf-frame-setup : current-frame alloc-after-setup ≡ frame
        oaf-frame-setup = exec-trace-preserves-frame setup-trace s alloc
  
        oaf-frame-pair-slots : current-frame alloc-after-pair-slots ≡ frame
        oaf-frame-pair-slots = refl
  
        oaf-mem-agree : ∀ slot → f-start ≤ slot → slot < max-slot-f →
          readLoc s-after-setup (AtStack (current-frame alloc-after-setup) slot) ≡
          readLoc s (AtStack (current-frame alloc-after-pair-slots) slot)
        oaf-mem-agree slot f-start≤slot slot<max =
          -- setup-trace writes only to backup-slot, and f-start > backup-slot
          -- So memory at slot ≥ f-start is unchanged
          -- Use frame equalities to convert to `frame`, prove equality, then convert back
          subst₂ (λ f1 f2 → readLoc s-after-setup (AtStack f1 slot) ≡ readLoc s (AtStack f2 slot))
                 (sym oaf-frame-setup) (sym oaf-frame-pair-slots)
                 oaf-mem-at-frame
          where
            -- backup-slot < f-start (since f-start = suc (suc (suc backup-slot)))
            -- and f-start ≤ slot, so backup-slot < slot
            backup<f-start : backup-slot < f-start
            backup<f-start = ≤-trans (n≤1+n fst-slot) (n≤1+n snd-slot)
            backup<slot : backup-slot < slot
            backup<slot = <-≤-trans backup<f-start f-start≤slot
  
            -- Core proof: s-after-setup agrees with s at (AtStack frame slot)
            oaf-mem-at-frame : readLoc s-after-setup (AtStack frame slot) ≡ readLoc s (AtStack frame slot)
            oaf-mem-at-frame =
              let s₁' = proj₁ (exec-abstract mov-to-output s alloc)
                  alloc₁' = proj₂ (exec-abstract mov-to-output s alloc)
                  mov-preserves-mem : readLoc s₁' (AtStack frame slot) ≡ readLoc s (AtStack frame slot)
                  mov-preserves-mem = readLoc-stackMem-eq s₁' s (AtStack frame slot) refl refl
                  s₂' = proj₁ (exec-abstract (store-at-slot backup-slot) s₁' alloc₁')
                  alloc₂' = proj₂ (exec-abstract (store-at-slot backup-slot) s₁' alloc₁')
                  not-halted₁' = exec-abstract-preserves-halted mov-to-output s alloc not-halted iph-mov-to-output
                  frame₁' : current-frame alloc₁' ≡ frame
                  frame₁' = exec-abstract-preserves-frame mov-to-output s alloc
                  store-preserves-slot : readLoc s₂' (AtStack frame slot) ≡ readLoc s₁' (AtStack frame slot)
                  store-preserves-slot = subst (λ f → readLoc s₂' (AtStack f slot) ≡ readLoc s₁' (AtStack f slot))
                                               frame₁'
                                               (store-at-slot-preserves-other backup-slot slot s₁' alloc₁' (inj₁ backup<slot))
                  -- instr-alloc-stack pair-overhead preserves stack memory.
                  s₃' = proj₁ (exec-abstract (instr-alloc-stack pair-overhead) s₂' alloc₂')
                  not-halted₂' = exec-abstract-preserves-halted (store-at-slot backup-slot) s₁' alloc₁' not-halted₁' iph-store-at-slot
                  alloc-stack-preserves-slot : readLoc s₃' (AtStack frame slot) ≡ readLoc s₂' (AtStack frame slot)
                  alloc-stack-preserves-slot = readLoc-stackMem-eq s₃' s₂' (AtStack frame slot) refl refl
                  -- Connect s-after-setup to s₃'
                  setup-decomp : exec-trace setup-trace s alloc ≡
                                 exec-trace (store-at-slot backup-slot ∷ instr-alloc-stack pair-overhead ∷ []) s₁' alloc₁'
                  setup-decomp = exec-trace-cons mov-to-output (store-at-slot backup-slot ∷ instr-alloc-stack pair-overhead ∷ []) s alloc not-halted
                  store-decomp : exec-trace (store-at-slot backup-slot ∷ instr-alloc-stack pair-overhead ∷ []) s₁' alloc₁' ≡
                                 exec-trace (instr-alloc-stack pair-overhead ∷ []) s₂' alloc₂'
                  store-decomp = exec-trace-cons (store-at-slot backup-slot) (instr-alloc-stack pair-overhead ∷ []) s₁' alloc₁' not-halted₁'
                  alloc-single : exec-trace (instr-alloc-stack pair-overhead ∷ []) s₂' alloc₂' ≡
                                 exec-abstract (instr-alloc-stack pair-overhead) s₂' alloc₂'
                  alloc-single = exec-trace-single (instr-alloc-stack pair-overhead) s₂' alloc₂' not-halted₂'
                  s-setup-eq : s-after-setup ≡ s₃'
                  s-setup-eq = cong proj₁ (trans setup-decomp (trans store-decomp alloc-single))
              in trans (cong (λ st → readLoc st (AtStack frame slot)) s-setup-eq)
                       (trans alloc-stack-preserves-slot
                         (trans store-preserves-slot mov-preserves-mem))
  
        -- s₁ output from trace-correct and rax-is-result
        oaf-s1-output : readReg (regs (proj₁ (exec-trace f-trace s-after-setup alloc-after-pair-slots))) Output ≡ SV-Ptr fst-loc
        oaf-s1-output = subst (λ st → readReg (regs st) Output ≡ SV-Ptr fst-loc)
                              (sym (IRResultAWF.trace-correct result-f))
                              fst-rax-eq
  
        -- Both executions start from s-after-setup, just differ in alloc.next-slot.
        -- mem-agree is trivial (both states are s-after-setup).
        oaf-mem-agree-trivial : ∀ slot → f-start ≤ slot → slot < max-slot-f →
          readLoc s-after-setup (AtStack (current-frame alloc-after-setup) slot) ≡
          readLoc s-after-setup (AtStack (current-frame alloc-after-pair-slots) slot)
        oaf-mem-agree-trivial slot _ _ =
          cong (λ fr → readLoc s-after-setup (AtStack fr slot)) oaf-frame-eq
  
        output-after-f : readReg (regs s-after-f) Output ≡ SV-Ptr fst-loc
        output-after-f =
          trans (exec-trace-output-deterministic f-trace
                  s-after-setup s-after-setup alloc-after-setup alloc-after-pair-slots f-start max-slot-f
                  not-halted-after-setup not-halted-after-setup oaf-frame-eq refl
                  f-tsra (IRResultAWF.trace-slot-reads-below result-f)
                  f-twa f-tnhw oaf-mem-agree-trivial)
                oaf-s1-output
  
        -- Output at s-after-g contains snd-loc
        -- Use exec-trace-output-deterministic: two executions of g-trace from states
        -- that agree on Input1 and memory in [reclaim-f, max-slot-g) give same Output.
        --
        -- Execution 1: g-trace from s-after-middle with alloc-after-middle → s-after-g
        -- Execution 2: g-trace from s₁' with alloc-after-f-reclaim → (via trace-correct)
        -- IRResultAWF.rax-is-result gives Output = snd-loc
  
        -- Prerequisites for exec-trace-output-deterministic
        -- Frame equality
        oag-frame-eq : current-frame alloc-after-middle ≡ current-frame alloc-after-f-reclaim
        oag-frame-eq = trans (exec-trace-preserves-frame middle-trace s-after-f alloc-after-f)
                       (trans (exec-trace-preserves-frame f-trace s-after-setup alloc-after-setup)
                       (trans (exec-trace-preserves-frame setup-trace s alloc) refl))
  
        -- Input1 equality: after state-only hoist, s₁' = s-after-middle, so this
        -- IS rdi-eq-at-s-after-middle.
        oag-input-s1' : readReg (regs s₁') Input1 ≡ SV-Ptr input-loc
        oag-input-s1' = rdi-eq-at-s-after-middle
  
        -- Decompose middle-trace: store-at-slot fst-slot ∷ restore-input backup-slot ∷ []
        -- (moved before oag-input-after-middle which needs these)
        oag-s-after-fst-store : LocState FS
        oag-s-after-fst-store = proj₁ (exec-abstract (store-at-slot fst-slot) s-after-f alloc-after-f)
  
        oag-alloc-after-fst-store : AllocState {FS}
        oag-alloc-after-fst-store = proj₂ (exec-abstract (store-at-slot fst-slot) s-after-f alloc-after-f)
  
        oag-not-halted-fst-store : halted oag-s-after-fst-store ≡ false
        oag-not-halted-fst-store = trans (store-at-slot-halted fst-slot s-after-f alloc-after-f) not-halted-after-f
  
        oag-frame-fst-store-eq : current-frame oag-alloc-after-fst-store ≡ frame
        oag-frame-fst-store-eq = trans (exec-abstract-preserves-frame (store-at-slot fst-slot) s-after-f alloc-after-f)
                                       (trans (exec-trace-preserves-frame f-trace s-after-setup alloc-after-setup)
                                              (exec-trace-preserves-frame setup-trace s alloc))
  
        -- Input1 after middle-trace: restore-input backup-slot sets Input1 to backup-slot's value
        -- Chain: setup writes input-loc to backup → f preserves → store fst preserves → restore reads
        -- Key steps: (1) setup writes input-loc to backup-slot, (2) f-trace preserves backup (writes above f-start),
        -- (3) store-at-slot fst-slot preserves backup (fst > backup), (4) restore-input reads backup and sets Input1
        abstract
          oag-input-after-middle : readReg (regs s-after-middle) Input1 ≡ SV-Ptr input-loc
          oag-input-after-middle =
            let -- Step 1: After setup-trace, backup-slot has input-loc
                -- setup-trace = mov-to-output ∷ store-at-slot backup-slot ∷ []
                -- Use rec-scheme-stores-input which proves exactly this
                setup-stores : readLoc s-after-setup (AtStack (current-frame alloc) backup-slot) ≡ just (readReg (regs s) Input1)
                setup-stores = mri-backup-setup-stores  -- Plan 0.14: reuse bridging proof from abstract block
                setup-has-input : readLoc s-after-setup (AtStack frame backup-slot) ≡ just (SV-Ptr input-loc)
                setup-has-input = trans setup-stores (cong just rdi-eq)
  
                -- Step 2: f-trace preserves backup-slot (writes above f-start, backup-slot < f-start)
                -- backup-slot < f-start (backup-slot < suc (suc (suc backup-slot)))
                backup<f-start : backup-slot < f-start
                backup<f-start = ≤-trans (n≤1+n fst-slot) (n≤1+n snd-slot)
                -- f-trace writes above f-start
                -- Use exec-trace-preserves-slot-below
                frame-setup-eq : current-frame alloc-after-setup ≡ frame
                frame-setup-eq = exec-trace-preserves-frame setup-trace s alloc
                f-preserves-backup : readLoc s-after-f (AtStack (current-frame alloc-after-setup) backup-slot) ≡
                                     readLoc s-after-setup (AtStack (current-frame alloc-after-setup) backup-slot)
                f-preserves-backup = exec-trace-preserves-slot-below f-trace s-after-setup alloc-after-setup f-start backup-slot
                                       f-twa f-tnhw backup<f-start
                -- Transport to frame
                f-has-input : readLoc s-after-f (AtStack frame backup-slot) ≡ just (SV-Ptr input-loc)
                f-has-input = trans (subst (λ f → readLoc s-after-f (AtStack f backup-slot) ≡ readLoc s-after-setup (AtStack f backup-slot))
                                           frame-setup-eq f-preserves-backup)
                                    setup-has-input
  
                -- Step 3: store-at-slot fst-slot preserves backup-slot (backup-slot < fst-slot)
                -- fst-slot = suc backup-slot, so backup-slot < fst-slot is suc backup-slot ≤ suc backup-slot = ≤-refl
                backup<fst : backup-slot < fst-slot
                backup<fst = ≤-refl
                frame-f-eq : current-frame alloc-after-f ≡ frame
                frame-f-eq = trans (exec-trace-preserves-frame f-trace s-after-setup alloc-after-setup)
                                   (exec-trace-preserves-frame setup-trace s alloc)
                store-fst-preserves-backup : readLoc oag-s-after-fst-store (AtStack frame backup-slot) ≡ readLoc s-after-f (AtStack frame backup-slot)
                store-fst-preserves-backup = subst (λ f → readLoc oag-s-after-fst-store (AtStack f backup-slot) ≡ readLoc s-after-f (AtStack f backup-slot))
                                                   frame-f-eq
                                                   (store-at-slot-preserves-other fst-slot backup-slot s-after-f alloc-after-f (inj₂ backup<fst))
                fst-store-has-input : readLoc oag-s-after-fst-store (AtStack frame backup-slot) ≡ just (SV-Ptr input-loc)
                fst-store-has-input = trans store-fst-preserves-backup f-has-input
  
                -- Step 4: restore-input backup-slot sets Input1 to value at backup-slot
                fst-store-backup-slot-eq : readLoc oag-s-after-fst-store (AtStack (current-frame oag-alloc-after-fst-store) backup-slot) ≡ just (SV-Ptr input-loc)
                fst-store-backup-slot-eq = subst (λ f → readLoc oag-s-after-fst-store (AtStack f backup-slot) ≡ just (SV-Ptr input-loc))
                                                 (sym oag-frame-fst-store-eq)
                                                 fst-store-has-input
                restore-sets-input : readReg (regs (proj₁ (exec-abstract (restore-input backup-slot) oag-s-after-fst-store oag-alloc-after-fst-store))) Input1 ≡ SV-Ptr input-loc
                restore-sets-input = SMP.RecSchemeSemantics.exec-abstract-restore-input-sets-input backup-slot oag-s-after-fst-store oag-alloc-after-fst-store (SV-Ptr input-loc) fst-store-backup-slot-eq
  
                -- Connect s-after-middle to the restore result
                -- s-after-middle = proj₁ (exec-trace middle-trace s-after-f alloc-after-f)
                -- middle-trace = store-at-slot fst-slot ∷ restore-input backup-slot ∷ []
                middle-decomp : exec-trace middle-trace s-after-f alloc-after-f ≡
                                exec-trace (restore-input backup-slot ∷ []) oag-s-after-fst-store oag-alloc-after-fst-store
                middle-decomp = exec-trace-cons (store-at-slot fst-slot) (restore-input backup-slot ∷ []) s-after-f alloc-after-f not-halted-after-f
                restore-single : exec-trace (restore-input backup-slot ∷ []) oag-s-after-fst-store oag-alloc-after-fst-store ≡
                                 exec-abstract (restore-input backup-slot) oag-s-after-fst-store oag-alloc-after-fst-store
                restore-single = exec-trace-single (restore-input backup-slot) oag-s-after-fst-store oag-alloc-after-fst-store oag-not-halted-fst-store
                s-middle-eq : s-after-middle ≡ proj₁ (exec-abstract (restore-input backup-slot) oag-s-after-fst-store oag-alloc-after-fst-store)
                s-middle-eq = cong proj₁ (trans middle-decomp restore-single)
  
            in trans (cong (λ st → readReg (regs st) Input1) s-middle-eq) restore-sets-input
  
        oag-input-eq : readReg (regs s-after-middle) Input1 ≡ readReg (regs s₁') Input1
        oag-input-eq = trans oag-input-after-middle (sym oag-input-s1')
  
        -- Memory agreement at [reclaim-f, max-slot-g)
        -- middle-trace writes to fst-slot (< reclaim-f), so slots ≥ reclaim-f unchanged from s-after-f
        -- s-after-f vs s₁': need trace determinism on f-trace results for memory
        -- This is complex because s-after-f and s₁ may differ in memory outside [f-start, max-slot-f)
        -- For now, use the fact that both agree on slots in [reclaim-f, max-slot-g) because:
        -- - slots ≥ reclaim-f are uninitialized before g runs
        -- - the memory values at these slots don't affect g's output
        oag-frame-middle : current-frame alloc-after-middle ≡ frame
        oag-frame-middle = trans (exec-trace-preserves-frame middle-trace s-after-f alloc-after-f)
                           (trans (exec-trace-preserves-frame f-trace s-after-setup alloc-after-setup)
                                  (exec-trace-preserves-frame setup-trace s alloc))
  
        oag-frame-reclaim : current-frame alloc-after-f-reclaim ≡ frame
        oag-frame-reclaim = refl
  
        abstract
          oag-mem-agree : ∀ slot → reclaim-f ≤ slot → slot < max-slot-g →
            readLoc s-after-middle (AtStack (current-frame alloc-after-middle) slot) ≡
            readLoc s₁' (AtStack (current-frame alloc-after-f-reclaim) slot)
          oag-mem-agree slot rf≤slot slot<max with slot <? max-slot-f
          ... | yes slot<max-f =
            -- Case 1: slot ∈ [reclaim-f, max-slot-f) - in f's write range, use determinism
            let -- Frame equalities
                frame-f-eq : current-frame alloc-after-f ≡ frame
                frame-f-eq = trans (exec-trace-preserves-frame f-trace s-after-setup alloc-after-setup)
                                   (exec-trace-preserves-frame setup-trace s alloc)
  
                -- middle-trace preserves slot ≥ reclaim-f (writes at fst-slot < reclaim-f)
                middle-twb : TraceWritesBelow reclaim-f middle-trace
                middle-twb = fst-slot<reclaim-f , tt
                middle-pres = SMP.TracePrimitives.exec-trace-preserves-slot-above middle-trace
                                s-after-f alloc-after-f reclaim-f slot middle-twb tt rf≤slot
                middle-pres-frame = subst (λ fr → readLoc s-after-middle (AtStack fr slot) ≡
                                                  readLoc s-after-f (AtStack fr slot))
                                          frame-f-eq middle-pres
  
                -- slot ≥ reclaim-f ≥ f-start
                slot≥f-start : f-start ≤ slot
                slot≥f-start = ≤-trans reclaim-f-above-f-start rf≤slot
  
                -- Use determinism lemma for [f-start, max-slot-f).
                -- Plan 0.13.3 Phase d (option b): both executions start from
                -- s-after-setup; mem-agree is trivial (same starting state).
                mem-det = SMP.TraceOutputDeterminism.exec-trace-mem-deterministic f-trace
                            s-after-setup s-after-setup alloc-after-setup alloc-after-pair-slots f-start max-slot-f
                            not-halted-after-setup not-halted-after-setup
                            oaf-frame-eq refl
                            f-tsra f-tsrb f-twa f-twb f-tnhw oaf-mem-agree-trivial
                            slot slot≥f-start slot<max-f
  
                -- Convert frames
                mem-det-frame : readLoc s-after-f (AtStack frame slot) ≡
                                readLoc (proj₁ (exec-trace f-trace s-after-setup alloc-after-pair-slots)) (AtStack frame slot)
                mem-det-frame = subst₂ (λ f1 f2 → readLoc s-after-f (AtStack f1 slot) ≡
                                                  readLoc (proj₁ (exec-trace f-trace s-after-setup alloc-after-pair-slots)) (AtStack f2 slot))
                                       oaf-frame-setup oaf-frame-pair-slots mem-det
  
                -- Convert to s₁ using trace-correct
                s₁-eq : readLoc (proj₁ (exec-trace f-trace s-after-setup alloc-after-pair-slots)) (AtStack frame slot) ≡
                        readLoc s₁ (AtStack frame slot)
                s₁-eq = cong (λ st → readLoc st (AtStack frame slot)) (IRResultAWF.trace-correct result-f)
  
                -- After state-only hoist, s₁' = s-after-middle, so s₁'-eq becomes
                -- the full chain we just built (rather than refl).
                s₁'-eq : readLoc s₁' (AtStack frame slot) ≡ readLoc s₁ (AtStack frame slot)
                s₁'-eq = trans middle-pres-frame (trans mem-det-frame s₁-eq)
  
                f-eq : readLoc s-after-f (AtStack frame slot) ≡ readLoc s₁ (AtStack frame slot)
                f-eq = trans mem-det-frame s₁-eq
  
            in subst₂ (λ f1 f2 → readLoc s-after-middle (AtStack f1 slot) ≡ readLoc s₁' (AtStack f2 slot))
                      (sym oag-frame-middle) (sym oag-frame-reclaim)
                      (trans middle-pres-frame (trans f-eq (sym s₁'-eq)))
          ... | no slot≮max-f =
            -- Case 2: slot ≥ max-slot-f - f doesn't write there, both preserve from s
            let slot≥max-f : max-slot-f ≤ slot
                slot≥max-f = ≮⇒≥ slot≮max-f
  
                -- Frame equalities
                frame-f-eq : current-frame alloc-after-f ≡ frame
                frame-f-eq = trans (exec-trace-preserves-frame f-trace s-after-setup alloc-after-setup)
                                   (exec-trace-preserves-frame setup-trace s alloc)
  
                -- middle-trace preserves slot ≥ reclaim-f (writes at fst-slot < reclaim-f)
                middle-twb : TraceWritesBelow reclaim-f middle-trace
                middle-twb = fst-slot<reclaim-f , tt
                middle-pres = SMP.TracePrimitives.exec-trace-preserves-slot-above middle-trace
                                s-after-f alloc-after-f reclaim-f slot middle-twb tt rf≤slot
                middle-pres-frame = subst (λ fr → readLoc s-after-middle (AtStack fr slot) ≡
                                                  readLoc s-after-f (AtStack fr slot))
                                          frame-f-eq middle-pres
  
                -- Plan 0.13.3 Phase d (option b): f-trace runs from s-after-setup
                -- at both runtime (alloc-after-setup) and construction (alloc-after-pair-slots).
                -- Both preserve from s-after-setup at slots ≥ max-slot-f.
                f-pres = SMP.TracePrimitives.exec-trace-preserves-slot-above f-trace
                           s-after-setup alloc-after-setup max-slot-f slot f-twb f-tnhw slot≥max-f
                s-after-f-pres = subst (λ fr → readLoc s-after-f (AtStack fr slot) ≡
                                               readLoc s-after-setup (AtStack fr slot))
                                       oaf-frame-setup f-pres
  
                -- s₁ also preserves from s-after-setup (construction f-trace writes below max-slot-f)
                s₁-f-pres = SMP.TracePrimitives.exec-trace-preserves-slot-above f-trace
                              s-after-setup alloc-after-pair-slots max-slot-f slot f-twb f-tnhw slot≥max-f
                s₁-pres = subst (λ st → readLoc st (AtStack frame slot) ≡ readLoc s-after-setup (AtStack frame slot))
                                (IRResultAWF.trace-correct result-f) s₁-f-pres
  
                -- After state-only hoist, s₁' = s-after-middle, so s₁'-eq becomes
                -- the chain (s-after-middle → s-after-f → s-after-setup → s₁).
                f-eq : readLoc s-after-f (AtStack frame slot) ≡ readLoc s₁ (AtStack frame slot)
                f-eq = trans s-after-f-pres (sym s₁-pres)
  
                s₁'-eq : readLoc s₁' (AtStack frame slot) ≡ readLoc s₁ (AtStack frame slot)
                s₁'-eq = trans middle-pres-frame f-eq
  
            in subst₂ (λ f1 f2 → readLoc s-after-middle (AtStack f1 slot) ≡ readLoc s₁' (AtStack f2 slot))
                      (sym oag-frame-middle) (sym oag-frame-reclaim)
                      (trans middle-pres-frame (trans f-eq (sym s₁'-eq)))
  
          -- s₂ output from trace-correct and rax-is-result
        oag-s2-output : readReg (regs (proj₁ (exec-trace g-trace s₁' alloc-after-f-reclaim))) Output ≡ SV-Ptr snd-loc
        oag-s2-output = subst (λ st → readReg (regs st) Output ≡ SV-Ptr snd-loc)
                              (sym (IRResultAWF.trace-correct result-g))
                              snd-rax-eq
  
        output-after-g : readReg (regs s-after-g) Output ≡ SV-Ptr snd-loc
        output-after-g =
          trans (exec-trace-output-deterministic g-trace
                  s-after-middle s₁' alloc-after-middle alloc-after-f-reclaim reclaim-f max-slot-g
                  not-halted-after-middle not-halted-at-s-after-middle oag-frame-eq oag-input-eq
                  g-tsra (IRResultAWF.trace-slot-reads-below result-g)
                  g-twa g-tnhw oag-mem-agree)
                oag-s2-output
  
        -- Decompose middle-trace: store-at-slot fst-slot ∷ restore-input backup-slot ∷ []
        -- s-after-fst-store / alloc-after-fst-store are defined earlier in
        -- this where-block (alongside s-after-f / alloc-after-f).
        not-halted-after-fst-store : halted s-after-fst-store ≡ false
        not-halted-after-fst-store = trans (store-at-slot-halted fst-slot s-after-f alloc-after-f) not-halted-after-f
  
        -- fst-slot gets fst-loc after store-at-slot fst-slot
        fst-written-in-store : readLoc s-after-fst-store (AtStack (current-frame alloc-after-f) fst-slot) ≡ just (SV-Ptr fst-loc)
        fst-written-in-store = trans (store-at-slot-result fst-slot s-after-f alloc-after-f)
                                     (cong just output-after-f)
  
        -- Frame equality for fst-slot location
        frame-after-f-eq : current-frame alloc-after-f ≡ frame
        frame-after-f-eq = trans (exec-trace-preserves-frame f-trace s-after-setup alloc-after-setup)
                                 (exec-trace-preserves-frame setup-trace s alloc)
  
        -- frame after fst-store is same as frame-after-f
        frame-after-fst-store-eq : current-frame alloc-after-fst-store ≡ frame
        frame-after-fst-store-eq = trans (exec-abstract-preserves-frame (store-at-slot fst-slot) s-after-f alloc-after-f)
                                         frame-after-f-eq
  
        -- restore-input preserves all memory locations (it only modifies Input1 register)
        restore-preserves-fst : readLoc (proj₁ (exec-abstract (restore-input backup-slot) s-after-fst-store alloc-after-fst-store))
                                        (AtStack frame fst-slot) ≡ readLoc s-after-fst-store (AtStack frame fst-slot)
        restore-preserves-fst =
          readLoc-stackMem-eq
            (proj₁ (exec-abstract (restore-input backup-slot) s-after-fst-store alloc-after-fst-store))
            s-after-fst-store
            (AtStack frame fst-slot)
            (SMP.RecSchemeSemantics.exec-abstract-restore-input-preserves-stackMem backup-slot s-after-fst-store alloc-after-fst-store)
            (SMP.RecSchemeSemantics.exec-abstract-restore-input-preserves-heapMem backup-slot s-after-fst-store alloc-after-fst-store)
  
        -- Combine: s-after-middle has fst-loc at fst-slot
        -- middle-trace = store-at-slot fst-slot ∷ restore-input backup-slot ∷ []
        -- restore-input only modifies register, not memory, so fst-slot is preserved
        abstract
          fst-at-s-after-middle : readLoc s-after-middle (AtStack frame fst-slot) ≡ just (SV-Ptr fst-loc)
          fst-at-s-after-middle =
            -- Use exec-trace-preserves-slot-below on the restore-input part
            -- First, restore-input doesn't write to any stack slot (TraceWritesAbove anything)
            -- So we can use the slot-below preservation lemma
            let rest-trace : AbstractTrace
                rest-trace = restore-input backup-slot ∷ []
                -- rest-trace writes nowhere (TraceWritesAbove any bound)
                rest-twa : TraceWritesAbove fst-slot rest-trace
                rest-twa = tt
                rest-tnhw : TraceNoHeapWrites rest-trace
                rest-tnhw = tt
                -- After fst-store, fst-slot < fst-slot is false, so use different reasoning
                -- Actually, restore-input doesn't write to stack at all
                -- Let's use readLoc-stackMem-eq on the trace execution
                s-after-rest : LocState FS
                s-after-rest = proj₁ (exec-trace rest-trace s-after-fst-store alloc-after-fst-store)
                alloc-after-rest : AllocState {FS}
                alloc-after-rest = proj₂ (exec-trace rest-trace s-after-fst-store alloc-after-fst-store)
                -- s-after-middle is definitionally equal to executing middle-trace from s-after-f
                -- and middle-trace = store-at-slot fst-slot ∷ rest-trace
                -- So s-after-middle = s-after-rest when computed through the decomposition
                -- Use the cons lemma
                middle-decomp : exec-trace middle-trace s-after-f alloc-after-f ≡
                               exec-trace rest-trace s-after-fst-store alloc-after-fst-store
                middle-decomp = exec-trace-cons (store-at-slot fst-slot) rest-trace s-after-f alloc-after-f not-halted-after-f
                s-middle-eq : s-after-middle ≡ s-after-rest
                s-middle-eq = cong proj₁ middle-decomp
                -- restore-input preserves stack memory
                rest-preserves-stackMem : stackMem s-after-rest ≡ stackMem s-after-fst-store
                rest-preserves-stackMem = SMP.RecSchemeSemantics.restore-trace-preserves-stackMem backup-slot s-after-fst-store alloc-after-fst-store
                                            not-halted-after-fst-store
                rest-preserves-heapMem : heapMem s-after-rest ≡ heapMem s-after-fst-store
                rest-preserves-heapMem = SMP.RecSchemeSemantics.restore-trace-preserves-heapMem backup-slot s-after-fst-store alloc-after-fst-store
                                           not-halted-after-fst-store
                rest-preserves-fst' : readLoc s-after-rest (AtStack frame fst-slot) ≡
                                      readLoc s-after-fst-store (AtStack frame fst-slot)
                rest-preserves-fst' = readLoc-stackMem-eq s-after-rest s-after-fst-store (AtStack frame fst-slot)
                                        rest-preserves-stackMem rest-preserves-heapMem
                fst-at-fst-store : readLoc s-after-fst-store (AtStack frame fst-slot) ≡ just (SV-Ptr fst-loc)
                fst-at-fst-store = subst (λ f → readLoc s-after-fst-store (AtStack f fst-slot) ≡ just (SV-Ptr fst-loc))
                                     frame-after-f-eq fst-written-in-store
            in trans (cong (λ st → readLoc st (AtStack frame fst-slot)) s-middle-eq)
                     (trans rest-preserves-fst' fst-at-fst-store)
  
          -- fst-slot preserved through rest of middle-trace (restore-input doesn't write)
          -- then through g-trace (writes above reclaim-f > fst-slot)
          -- then through final-trace (writes to snd-slot ≠ fst-slot, lea doesn't write)
  
          -- g-trace preserves fst-slot (writes above reclaim-f, fst-slot < reclaim-f)
        g-preserves-fst : readLoc s-after-g (AtStack frame fst-slot) ≡ readLoc s-after-middle (AtStack frame fst-slot)
        g-preserves-fst =
          let preserved = exec-trace-preserves-slot-below g-trace s-after-middle alloc-after-middle
                            reclaim-f fst-slot g-twa g-tnhw fst-slot<reclaim-f
              frame-eq = exec-trace-preserves-frame middle-trace s-after-f alloc-after-f
          in subst (λ f → readLoc s-after-g (AtStack f fst-slot) ≡ readLoc s-after-middle (AtStack f fst-slot))
                   (trans frame-eq frame-after-f-eq) preserved
  
        -- store-at-slot snd-slot preserves fst-slot (different slots)
        -- snd-slot = suc fst-slot, so fst-slot < snd-slot means suc fst-slot ≤ suc fst-slot = ≤-refl
        snd-store-preserves-fst : readLoc s-after-snd-store (AtStack frame fst-slot) ≡ readLoc s-after-g (AtStack frame fst-slot)
        snd-store-preserves-fst =
          subst (λ f → readLoc s-after-snd-store (AtStack f fst-slot) ≡ readLoc s-after-g (AtStack f fst-slot))
                frame-preserved-through
                (store-at-slot-preserves-other snd-slot fst-slot s-after-g alloc-after-g (inj₂ ≤-refl))
  
        -- lea-slot preserves all memory
        lea-preserves-fst : readLoc (proj₁ (exec-abstract (lea-slot fst-slot) s-after-snd-store alloc-after-snd-store))
                                    (AtStack frame fst-slot) ≡ readLoc s-after-snd-store (AtStack frame fst-slot)
        lea-preserves-fst = lea-slot-preserves-mem fst-slot s-after-snd-store alloc-after-snd-store (AtStack frame fst-slot)
  
        fst-ptr : readLoc s-final (AtStack frame fst-slot) ≡ just (SV-Ptr fst-loc)
        fst-ptr =
          -- Chain: s-final -> s-after-final -> lea preserves -> store snd preserves -> g preserves -> s-after-middle
          let eq1 = cong (λ st → readLoc st (AtStack frame fst-slot)) s-final-eq
              eq2 = cong (λ st → readLoc st (AtStack frame fst-slot)) s-after-final-eq
          in trans eq1 (trans eq2 (trans lea-preserves-fst
                                  (trans snd-store-preserves-fst
                                  (trans g-preserves-fst fst-at-s-after-middle))))
  
        -- snd-slot gets snd-loc from final-trace
        snd-written : readLoc s-after-snd-store (AtStack frame snd-slot) ≡ just (SV-Ptr snd-loc)
        snd-written = subst (λ f → readLoc s-after-snd-store (AtStack f snd-slot) ≡ just (SV-Ptr snd-loc))
                            frame-preserved-through
                            (trans (store-at-slot-result snd-slot s-after-g alloc-after-g)
                                   (cong just output-after-g))
  
        -- lea-slot preserves snd-slot
        lea-preserves-snd : readLoc (proj₁ (exec-abstract (lea-slot fst-slot) s-after-snd-store alloc-after-snd-store))
                                    (AtStack frame snd-slot) ≡ readLoc s-after-snd-store (AtStack frame snd-slot)
        lea-preserves-snd = lea-slot-preserves-mem fst-slot s-after-snd-store alloc-after-snd-store (AtStack frame snd-slot)
  
        snd-ptr : readLoc s-final (AtStack frame snd-slot) ≡ just (SV-Ptr snd-loc)
        snd-ptr =
          let eq1 = cong (λ st → readLoc st (AtStack frame snd-slot)) s-final-eq
              eq2 = cong (λ st → readLoc st (AtStack frame snd-slot)) s-after-final-eq
          in trans eq1 (trans eq2 (trans lea-preserves-snd snd-written))
  
        ------------------------------------------------------------------------
        -- fst-valid and snd-valid (validity of sub-results)
        --
        -- Key insight: Use validityWF-trace-preserves with positive bounds.
        -- - fst-loc is BeforeFrontier at reclaim-f
        -- - After f, rest of trace writes above suc backup-slot > fst-slot
        -- - So fst-loc's validity is preserved
        ------------------------------------------------------------------------
        fst-before : BeforeFrontier alloc-final fst-loc
        fst-before = frontier-monotone alloc-after-f-reclaim alloc-final
                       refl
                       (IRResultAWF.slot-monotone result-g)
                       (IRResultAWF.heap-monotone result-g)
                       fst-loc
                       fst-rec-before-from-f
  
        snd-before : BeforeFrontier alloc-final snd-loc
        snd-before = frontier-monotone
                       (record alloc { next-slot     = reclaim-g
                                     ; next-heap-ref = next-heap-ref (IRResultAWF.final-alloc result-g) })
                       alloc-final
                       refl ≤-refl ≤-refl snd-loc
                       snd-rec-before-from-g
  
        -- sucLoc pair-loc = AtStack frame snd-slot
        sucLoc-pair-before : BeforeFrontier alloc-final (sucLoc pair-loc)
        sucLoc-pair-before = stack-before refl snd<reclaim-g
  
        ----------------------------------------------------------------------
        -- fst-valid: Validity of f's result at fst-loc in s-final
        --
        -- Strategy using POSITIVE BOUNDS:
        -- 1. reclaim-preserves-validity gives validity at s₁ with alloc-after-f-reclaim
        -- 2. Transfer validity from s₁ to s-after-f using validityWF-mem-preserved-in-regions
        --    Memory agrees in two disjoint regions:
        --      - Input1 region: [0, backup-slot) - preserved from initial state
        --      - Fresh region: [f-start, reclaim-f) - written by f-trace deterministically
        --    The gap [backup-slot, f-start) = {backup-slot, fst-slot, snd-slot} contains
        --    no sub-locations of fst-loc.
        -- 3. Apply validityWF-trace-preserves for rest-trace to reach s-final
        -- 4. Advance frontier from reclaim-f to reclaim-g
        --
        -- Key insight (positive characterization): fst-loc's sub-locations are in:
        --   - Input1 region: [0, backup-slot) - from input x
        --   - Fresh region: [f-start, reclaim-f) - from f's allocations
        ----------------------------------------------------------------------
  
        -- Step 1: Get validity at s₁ with alloc-after-f-reclaim
        valid-s1-reclaimed : ValidAtWF mF alloc-after-f-reclaim (eval f x) fst-loc s₁
        valid-s1-reclaimed = fst-rec-valid-from-f
  
        -- fst-loc is before frontier at alloc-after-f-reclaim
        fst-loc-before-reclaimed : BeforeFrontier alloc-after-f-reclaim fst-loc
        fst-loc-before-reclaimed = fst-rec-before-from-f
  
        -- Step 2: Memory agreement from s₁ to s-after-f using POSITIVE BOUNDS
        -- s₁ = exec f-trace s alloc-after-pair-slots (recursive call result)
        -- s-after-f = exec f-trace s-after-setup alloc-after-setup
        --
        -- Region bounds for fst-loc's sub-locations:
        --   input-bound = backup-slot (sub-locations from x are < backup-slot)
        --   fresh-start = f-start (sub-locations from f are ≥ f-start)
  
        -- Memory agrees on input region [0, backup-slot)
        -- Both s₁ and s-after-f preserve this from initial state (f writes above f-start)
        abstract
          f-mem-input-region : ∀ slot → slot < backup-slot →
            readLoc s-after-f (AtStack frame slot) ≡ readLoc s₁ (AtStack frame slot)
          f-mem-input-region slot slot<backup =
            let -- slot < backup-slot < f-start, so slot < f-start
                backup≤f-start' : backup-slot ≤ f-start
                backup≤f-start' = ≤-trans (n≤1+n backup-slot) (≤-trans (n≤1+n fst-slot) (n≤1+n snd-slot))
                slot<f-start : slot < f-start
                slot<f-start = ≤-trans slot<backup backup≤f-start'
                -- s-after-f preserves slot from s-after-setup (f-trace writes above f-start > slot)
                f-pres = SMP.TracePrimitives.exec-trace-preserves-slot-below f-trace s-after-setup
                           alloc-after-setup f-start slot f-twa f-tnhw slot<f-start
                f-pres-frame = subst (λ fr → readLoc s-after-f (AtStack fr slot) ≡
                                             readLoc s-after-setup (AtStack fr slot))
                                     oaf-frame-setup f-pres
                -- s₁ preserves slot from s-after-setup (construction f-trace writes above f-start > slot)
                exec-f-pres = SMP.TracePrimitives.exec-trace-preserves-slot-below f-trace s-after-setup
                                alloc-after-pair-slots f-start slot f-twa f-tnhw slot<f-start
                s₁-pres = subst (λ st → readLoc st (AtStack frame slot) ≡ readLoc s-after-setup (AtStack frame slot))
                                (IRResultAWF.trace-correct result-f) exec-f-pres
            in trans f-pres-frame (sym s₁-pres)
  
          -- Memory agrees on fresh region [f-start, reclaim-f)
          -- Both executions of f-trace write same values (deterministic given same Input1)
          f-mem-fresh-region : ∀ slot → f-start ≤ slot → slot < reclaim-f →
            readLoc s-after-f (AtStack frame slot) ≡ readLoc s₁ (AtStack frame slot)
          f-mem-fresh-region slot f-start≤slot slot<reclaim =
            let slot<max : slot < max-slot-f
                slot<max = <-≤-trans slot<reclaim (IRResultAWF.max-slot-geq-final result-f)
                -- Plan 0.13.3 Phase d (option b): both executions start from s-after-setup.
                mem-det = SMP.TraceOutputDeterminism.exec-trace-mem-deterministic f-trace
                            s-after-setup s-after-setup alloc-after-setup alloc-after-pair-slots f-start max-slot-f
                            not-halted-after-setup not-halted-after-setup oaf-frame-eq refl
                            f-tsra f-tsrb f-twa f-twb f-tnhw oaf-mem-agree-trivial
                            slot f-start≤slot slot<max
                mem-det-frame : readLoc s-after-f (AtStack frame slot) ≡
                                readLoc (proj₁ (exec-trace f-trace s-after-setup alloc-after-pair-slots)) (AtStack frame slot)
                mem-det-frame = subst₂ (λ f1 f2 → readLoc s-after-f (AtStack f1 slot) ≡
                                                  readLoc (proj₁ (exec-trace f-trace s-after-setup alloc-after-pair-slots)) (AtStack f2 slot))
                                       oaf-frame-setup oaf-frame-pair-slots mem-det
                s₁-eq : readLoc (proj₁ (exec-trace f-trace s-after-setup alloc-after-pair-slots)) (AtStack frame slot) ≡
                        readLoc s₁ (AtStack frame slot)
                s₁-eq = cong (λ st → readLoc st (AtStack frame slot)) (IRResultAWF.trace-correct result-f)
            in trans mem-det-frame s₁-eq
  
          -- Memory agrees on heap (no heap writes)
          f-mem-heap : ∀ h → readLoc s-after-f (AtDynamic h) ≡ readLoc s₁ (AtDynamic h)
          f-mem-heap h =
            let -- s-after-f preserves heap from s-after-setup (f-trace has no heap writes)
                s-after-f-pres = SMP.TracePrimitives.exec-trace-preserves-heap-loc f-trace s-after-setup alloc-after-setup h f-tnhw
                -- s₁ preserves heap from s-after-setup (construction f-trace has no heap writes)
                exec-f-pres = SMP.TracePrimitives.exec-trace-preserves-heap-loc f-trace s-after-setup alloc-after-pair-slots h f-tnhw
                s₁-pres = subst (λ st → readLoc st (AtDynamic h) ≡ readLoc s-after-setup (AtDynamic h))
                                (IRResultAWF.trace-correct result-f) exec-f-pres
            in trans s-after-f-pres (sym s₁-pres)
  
          -- Memory agrees on ancestor frames (f doesn't write there)
          f-mem-ancestors : ∀ f' k → current-frame alloc-after-f-reclaim ≺ f' →
            readLoc s-after-f (AtStack f' k) ≡ readLoc s₁ (AtStack f' k)
          f-mem-ancestors f' k cf≺f' =
            let -- s-after-f preserves ancestors from s-after-setup
                alloc-after-setup-cf≺f' : current-frame alloc-after-setup ≺ f'
                alloc-after-setup-cf≺f' = subst (_≺ f') (sym oaf-frame-setup) cf≺f'
                s-after-f-pres = SMP.TracePrimitives.exec-trace-preserves-ancestor f-trace s-after-setup
                                   alloc-after-setup f' k alloc-after-setup-cf≺f' f-tnhw
                -- s₁ preserves ancestors from s-after-setup
                alloc-pair-slots-cf≺f' : current-frame alloc-after-pair-slots ≺ f'
                alloc-pair-slots-cf≺f' = subst (_≺ f') (sym oaf-frame-pair-slots) cf≺f'
                exec-f-pres = SMP.TracePrimitives.exec-trace-preserves-ancestor f-trace s-after-setup alloc-after-pair-slots
                                f' k alloc-pair-slots-cf≺f' f-tnhw
                s₁-pres = subst (λ st → readLoc st (AtStack f' k) ≡ readLoc s-after-setup (AtStack f' k))
                                (IRResultAWF.trace-correct result-f) exec-f-pres
            in trans s-after-f-pres (sym s₁-pres)
  
        -- Region ordering: backup-slot ≤ f-start ≤ reclaim-f
        backup≤f-start : backup-slot ≤ f-start
        backup≤f-start = ≤-trans (n≤1+n backup-slot) (≤-trans (n≤1+n fst-slot) (n≤1+n snd-slot))
  
        f-start≤reclaim-f : f-start ≤ reclaim-f
        f-start≤reclaim-f = reclaim-f-above-f-start
  
        -- Transfer validity from s₁ to s-after-f using positive regions lemma
        valid-at-s-after-f : ValidAtWF mF alloc-after-f-reclaim (eval f x) fst-loc s-after-f
        valid-at-s-after-f = validityWF-mem-preserved-in-regions alloc-after-f-reclaim
                               (eval f x) fst-loc backup-slot f-start s₁ s-after-f
                               fst-loc-before-reclaimed backup≤f-start f-start≤reclaim-f
                               f-mem-input-region f-mem-fresh-region f-mem-heap f-mem-ancestors
                               valid-s1-reclaimed
  
        -- Step 3: Transfer validity from s-after-f to s-final using POSITIVE BOUNDS
        --
        -- rest-trace = middle ++ g ++ final writes to:
        --   - fst-slot, snd-slot (in gap [backup-slot, f-start))
        --   - g's allocations in [reclaim-f, max-g)
        --
        -- fst-loc's sub-locations are in [0, backup-slot) ∪ [f-start, reclaim-f).
        -- rest-trace does NOT write to these regions, so sub-locations are preserved.
        --
        -- Note: We can't use validityWF-trace-preserves here because rest-trace writes
        -- BELOW reclaim-f (at fst-slot, snd-slot). Instead, we use positive region
        -- preservation again.
  
        -- Memory agrees on input region [0, backup-slot): rest-trace writes above backup-slot
        abstract
          rest-mem-input-region : ∀ slot → slot < backup-slot →
            readLoc s-final (AtStack frame slot) ≡ readLoc s-after-f (AtStack frame slot)
          rest-mem-input-region slot slot<backup =
            let -- slot < backup-slot < fst-slot = suc backup-slot
                slot<fst : slot < fst-slot
                slot<fst = ≤-trans slot<backup (n≤1+n backup-slot)
                slot<snd : slot < snd-slot
                slot<snd = ≤-trans slot<fst (n≤1+n fst-slot)
                slot<reclaim-f : slot < reclaim-f
                slot<reclaim-f = <-≤-trans slot<backup backup≤reclaim-f
                -- middle-trace writes at fst-slot, so TraceWritesAbove fst-slot
                middle-twa : TraceWritesAbove fst-slot middle-trace
                middle-twa = ≤-refl , tt  -- store-at-slot fst-slot writes at fst-slot, restore-input doesn't write
                middle-tnhw : TraceNoHeapWrites middle-trace
                middle-tnhw = tt
                -- middle-trace preserves slot from s-after-f to s-after-middle
                middle-pres = SMP.TracePrimitives.exec-trace-preserves-slot-below middle-trace
                                s-after-f alloc-after-f fst-slot slot middle-twa middle-tnhw slot<fst
                middle-pres-frame = subst (λ fr → readLoc s-after-middle (AtStack fr slot) ≡
                                                  readLoc s-after-f (AtStack fr slot))
                                          frame-after-f-eq middle-pres
                -- g-trace writes above reclaim-f, so preserves slot < reclaim-f
                g-pres = SMP.TracePrimitives.exec-trace-preserves-slot-below g-trace
                           s-after-middle alloc-after-middle reclaim-f slot g-twa g-tnhw slot<reclaim-f
                g-pres-frame = subst (λ fr → readLoc s-after-g (AtStack fr slot) ≡
                                             readLoc s-after-middle (AtStack fr slot))
                                     oag-frame-middle g-pres
                -- final-trace writes at snd-slot, so TraceWritesAbove snd-slot
                final-twa : TraceWritesAbove snd-slot final-trace
                final-twa = ≤-refl , tt  -- store-at-slot snd-slot writes at snd-slot, lea doesn't write
                final-tnhw : TraceNoHeapWrites final-trace
                final-tnhw = tt
                -- final-trace preserves slot from s-after-g to s-after-final
                final-pres = SMP.TracePrimitives.exec-trace-preserves-slot-below final-trace
                               s-after-g alloc-after-g snd-slot slot final-twa final-tnhw slot<snd
                final-pres-frame = subst (λ fr → readLoc s-after-final (AtStack fr slot) ≡
                                                 readLoc s-after-g (AtStack fr slot))
                                         frame-preserved-through final-pres
                -- Chain: s-after-final preserves from s-after-f
                chain = trans final-pres-frame (trans g-pres-frame middle-pres-frame)
                -- Use s-final-eq : s-final ≡ s-after-final
            in subst (λ st → readLoc st (AtStack frame slot) ≡ readLoc s-after-f (AtStack frame slot))
                     (sym s-final-eq) chain
  
          -- Memory agrees on fresh region [f-start, reclaim-f): rest-trace writes elsewhere
          -- rest-trace writes to [backup-slot, f-start) ∪ [reclaim-f, max-g), so [f-start, reclaim-f) preserved
          rest-mem-fresh-region : ∀ slot → f-start ≤ slot → slot < reclaim-f →
            readLoc s-final (AtStack frame slot) ≡ readLoc s-after-f (AtStack frame slot)
          rest-mem-fresh-region slot f-start≤slot slot<reclaim =
            let -- middle-trace writes at fst-slot < f-start, so preserves slot ≥ f-start
                -- fst-slot < f-start since suc fst-slot = snd-slot and f-start = suc snd-slot
                -- So fst-slot < f-start = suc fst-slot ≤ f-start = snd-slot ≤ suc snd-slot = n≤1+n snd-slot
                fst<f-start : fst-slot < f-start
                fst<f-start = n≤1+n snd-slot
                middle-twb : TraceWritesBelow f-start middle-trace
                middle-twb = fst<f-start , tt  -- store-at-slot fst-slot writes at fst-slot < f-start
                middle-tnhw : TraceNoHeapWrites middle-trace
                middle-tnhw = tt
                middle-pres = SMP.TracePrimitives.exec-trace-preserves-slot-above middle-trace
                                s-after-f alloc-after-f f-start slot middle-twb middle-tnhw f-start≤slot
                middle-pres-frame = subst (λ fr → readLoc s-after-middle (AtStack fr slot) ≡
                                                  readLoc s-after-f (AtStack fr slot))
                                          frame-after-f-eq middle-pres
                -- g-trace writes above reclaim-f, so preserves slot < reclaim-f
                g-pres = SMP.TracePrimitives.exec-trace-preserves-slot-below g-trace
                           s-after-middle alloc-after-middle reclaim-f slot g-twa g-tnhw slot<reclaim
                g-pres-frame = subst (λ fr → readLoc s-after-g (AtStack fr slot) ≡
                                             readLoc s-after-middle (AtStack fr slot))
                                     oag-frame-middle g-pres
                -- final-trace writes at snd-slot < f-start, so preserves slot ≥ f-start
                -- snd-slot < f-start = suc snd-slot ≤ f-start = f-start ≤ f-start = ≤-refl
                snd<f-start : snd-slot < f-start
                snd<f-start = ≤-refl
                final-twb : TraceWritesBelow f-start final-trace
                final-twb = snd<f-start , tt  -- store-at-slot snd-slot writes at snd-slot < f-start
                final-tnhw : TraceNoHeapWrites final-trace
                final-tnhw = tt
                final-pres = SMP.TracePrimitives.exec-trace-preserves-slot-above final-trace
                               s-after-g alloc-after-g f-start slot final-twb final-tnhw f-start≤slot
                final-pres-frame = subst (λ fr → readLoc s-after-final (AtStack fr slot) ≡
                                                 readLoc s-after-g (AtStack fr slot))
                                         frame-preserved-through final-pres
                -- Chain: s-after-final preserves from s-after-f
                chain = trans final-pres-frame (trans g-pres-frame middle-pres-frame)
                -- Use s-final-eq : s-final ≡ s-after-final
            in subst (λ st → readLoc st (AtStack frame slot) ≡ readLoc s-after-f (AtStack frame slot))
                     (sym s-final-eq) chain
  
          -- Memory agrees on heap (no heap writes in rest-trace)
          rest-mem-heap : ∀ h → readLoc s-final (AtDynamic h) ≡ readLoc s-after-f (AtDynamic h)
          rest-mem-heap h =
            let -- middle-trace preserves heap from s-after-f to s-after-middle
                middle-tnhw : TraceNoHeapWrites middle-trace
                middle-tnhw = tt
                middle-pres = SMP.TracePrimitives.exec-trace-preserves-heap-loc middle-trace s-after-f alloc-after-f h middle-tnhw
                -- g-trace preserves heap from s-after-middle to s-after-g
                g-pres = SMP.TracePrimitives.exec-trace-preserves-heap-loc g-trace s-after-middle alloc-after-middle h g-tnhw
                -- final-trace preserves heap from s-after-g to s-after-final
                final-tnhw : TraceNoHeapWrites final-trace
                final-tnhw = tt
                final-pres = SMP.TracePrimitives.exec-trace-preserves-heap-loc final-trace s-after-g alloc-after-g h final-tnhw
                -- Chain: s-after-final preserves from s-after-f
                chain = trans final-pres (trans g-pres middle-pres)
                -- Use s-final-eq : s-final ≡ s-after-final
            in subst (λ st → readLoc st (AtDynamic h) ≡ readLoc s-after-f (AtDynamic h))
                     (sym s-final-eq) chain
  
          -- Memory agrees on ancestor frames
          rest-mem-ancestors : ∀ f' k → current-frame alloc-after-f-reclaim ≺ f' →
            readLoc s-final (AtStack f' k) ≡ readLoc s-after-f (AtStack f' k)
          rest-mem-ancestors f' k cf≺f' =
            let -- Convert cf≺f' to work with each alloc (all have current-frame = frame)
                frame≺f' : frame ≺ f'
                frame≺f' = subst (_≺ f') oag-frame-reclaim cf≺f'
                -- middle-trace preserves ancestors from s-after-f to s-after-middle
                middle-tnhw : TraceNoHeapWrites middle-trace
                middle-tnhw = tt
                alloc-after-f-cf≺f' : current-frame alloc-after-f ≺ f'
                alloc-after-f-cf≺f' = subst (_≺ f') (sym frame-after-f-eq) frame≺f'
                middle-pres = SMP.TracePrimitives.exec-trace-preserves-ancestor middle-trace s-after-f
                                alloc-after-f f' k alloc-after-f-cf≺f' middle-tnhw
                -- g-trace preserves ancestors from s-after-middle to s-after-g
                alloc-after-middle-cf≺f' : current-frame alloc-after-middle ≺ f'
                alloc-after-middle-cf≺f' = subst (_≺ f') (sym oag-frame-middle) frame≺f'
                g-pres = SMP.TracePrimitives.exec-trace-preserves-ancestor g-trace s-after-middle
                           alloc-after-middle f' k alloc-after-middle-cf≺f' g-tnhw
                -- final-trace preserves ancestors from s-after-g to s-after-final
                final-tnhw : TraceNoHeapWrites final-trace
                final-tnhw = tt
                alloc-after-g-cf≺f' : current-frame alloc-after-g ≺ f'
                alloc-after-g-cf≺f' = subst (_≺ f') (sym frame-preserved-through) frame≺f'
                final-pres = SMP.TracePrimitives.exec-trace-preserves-ancestor final-trace s-after-g
                               alloc-after-g f' k alloc-after-g-cf≺f' final-tnhw
                -- Chain: s-after-final preserves from s-after-f
                chain = trans final-pres (trans g-pres middle-pres)
                -- Use s-final-eq : s-final ≡ s-after-final
            in subst (λ st → readLoc st (AtStack f' k) ≡ readLoc s-after-f (AtStack f' k))
                     (sym s-final-eq) chain
  
          -- Transfer validity from s-after-f to s-final using positive regions
        valid-at-s-final : ValidAtWF mF alloc-after-f-reclaim (eval f x) fst-loc s-final
        valid-at-s-final = validityWF-mem-preserved-in-regions alloc-after-f-reclaim
                             (eval f x) fst-loc backup-slot f-start s-after-f s-final
                             fst-loc-before-reclaimed backup≤f-start f-start≤reclaim-f
                             rest-mem-input-region rest-mem-fresh-region rest-mem-heap rest-mem-ancestors
                             valid-at-s-after-f
  
        -- Step 4: Advance frontier from alloc-after-f-reclaim to alloc-final
        fst-valid : ValidAtWF mF alloc-final (eval f x) fst-loc s-final
        fst-valid = validityWF-frontier-advance (eval f x) fst-loc s-final refl
                      (IRResultAWF.slot-monotone result-g)
                      (IRResultAWF.heap-monotone result-g)
                      valid-at-s-final
  
        ----------------------------------------------------------------------
        -- snd-valid: Validity of g's result at snd-loc in s-final
        --
        -- Strategy using POSITIVE BOUNDS (same approach as fst-valid):
        -- 1. reclaim-preserves-validity gives validity at s₂ with alloc-reclaim-g
        -- 2. Transfer validity from s₂ to s-after-g using validityWF-mem-preserved-in-regions
        --    Memory agrees in two disjoint regions:
        --      - Input1 region: [0, backup-slot) - preserved from before g
        --      - Fresh region: [reclaim-f, reclaim-g) - written by g-trace deterministically
        -- 3. Transfer validity from s-after-g to s-final (final-trace preserves both regions)
        -- 4. Frontier advance is trivial (alloc-reclaim-g = alloc-final)
        ----------------------------------------------------------------------
  
        -- Alloc state after g's reclaim (continuation-alloc shape).
        alloc-reclaim-g : AllocState {FS}
        alloc-reclaim-g = record alloc { next-slot     = reclaim-g
                                       ; next-heap-ref = next-heap-ref (IRResultAWF.final-alloc result-g) }
  
        -- Step 1: Get validity at s₂ with alloc-reclaim-g
        valid-s2-reclaimed : ValidAtWF mG alloc-reclaim-g (eval g x) snd-loc s₂
        valid-s2-reclaimed = snd-rec-valid-from-g
  
        -- snd-loc is before frontier at alloc-reclaim-g
        snd-loc-before-reclaim-g : BeforeFrontier alloc-reclaim-g snd-loc
        snd-loc-before-reclaim-g = snd-rec-before-from-g
  
        -- Region bounds for snd-loc's sub-locations:
        --   input-bound = backup-slot (sub-locations from x are < backup-slot)
        --   fresh-start = reclaim-f (sub-locations from g are ≥ reclaim-f)
        backup≤reclaim-f' : backup-slot ≤ reclaim-f
        backup≤reclaim-f' = backup≤reclaim-f
  
        reclaim-f≤reclaim-g : reclaim-f ≤ reclaim-g
        reclaim-f≤reclaim-g = IRResultAWF.slot-monotone result-g  -- alloc-after-f-reclaim has next-slot = reclaim-f
  
        -- Step 2: Memory agreement from s₂ to s-after-g
        -- s₂ = exec g-trace s₁' alloc-after-f-reclaim (recursive call result)
        -- s-after-g = exec g-trace s-after-middle alloc-after-middle
  
        -- Memory agrees on input region [0, backup-slot)
        -- Both s₂ and s-after-g preserve this from before g runs
        abstract
          g-mem-input-region : ∀ slot → slot < backup-slot →
            readLoc s-after-g (AtStack frame slot) ≡ readLoc s₂ (AtStack frame slot)
          g-mem-input-region slot slot<backup =
            let -- slot < backup-slot < reclaim-f, so g-trace preserves slot
                slot<reclaim-f : slot < reclaim-f
                slot<reclaim-f = <-≤-trans slot<backup backup≤reclaim-f'
                -- s-after-g preserves slot from s-after-middle (g-trace writes above reclaim-f)
                g-pres = SMP.TracePrimitives.exec-trace-preserves-slot-below g-trace s-after-middle
                           alloc-after-middle reclaim-f slot g-twa g-tnhw slot<reclaim-f
                g-pres-frame = subst (λ fr → readLoc s-after-g (AtStack fr slot) ≡
                                             readLoc s-after-middle (AtStack fr slot))
                                     oag-frame-middle g-pres
                -- s₂ preserves slot from s₁' (g-trace writes above reclaim-f)
                exec-g-pres = SMP.TracePrimitives.exec-trace-preserves-slot-below g-trace s₁'
                                alloc-after-f-reclaim reclaim-f slot g-twa g-tnhw slot<reclaim-f
                s₂-pres = subst (λ st → readLoc st (AtStack frame slot) ≡ readLoc s₁' (AtStack frame slot))
                                (IRResultAWF.trace-correct result-g) exec-g-pres
                -- After state-only hoist: s₁' = s-after-middle, derive via chain.
                slot<fst : slot < fst-slot
                slot<fst = ≤-trans slot<backup (n≤1+n backup-slot)
                middle-twa : TraceWritesAbove fst-slot middle-trace
                middle-twa = ≤-refl , tt
                middle-pres = SMP.TracePrimitives.exec-trace-preserves-slot-below middle-trace
                                s-after-f alloc-after-f fst-slot slot middle-twa tt slot<fst
                middle-pres-frame = subst (λ fr → readLoc s-after-middle (AtStack fr slot) ≡
                                                  readLoc s-after-f (AtStack fr slot))
                                          frame-after-f-eq middle-pres
                f-input-eq = f-mem-input-region slot slot<backup
                s₁'-eq : readLoc s₁' (AtStack frame slot) ≡ readLoc s₁ (AtStack frame slot)
                s₁'-eq = trans middle-pres-frame f-input-eq
            in trans g-pres-frame (trans middle-pres-frame (trans f-input-eq (trans (sym s₁'-eq) (sym s₂-pres))))
  
          -- Memory agrees on fresh region [reclaim-f, reclaim-g)
          -- Both executions of g-trace write same values (deterministic given same Input1)
          g-mem-fresh-region : ∀ slot → reclaim-f ≤ slot → slot < reclaim-g →
            readLoc s-after-g (AtStack frame slot) ≡ readLoc s₂ (AtStack frame slot)
          g-mem-fresh-region slot rf≤slot slot<rg =
            let -- slot < reclaim-g ≤ max-slot-g
                slot<max : slot < max-slot-g
                slot<max = <-≤-trans slot<rg (IRResultAWF.max-slot-geq-final result-g)
                -- Use exec-trace-mem-deterministic for g-trace
                mem-det = SMP.TraceOutputDeterminism.exec-trace-mem-deterministic g-trace
                            s-after-middle s₁' alloc-after-middle alloc-after-f-reclaim reclaim-f max-slot-g
                            not-halted-after-middle not-halted-at-s-after-middle oag-frame-eq oag-input-eq
                            g-tsra (IRResultAWF.trace-slot-reads-below result-g)
                            g-twa g-twb g-tnhw oag-mem-agree
                            slot rf≤slot slot<max
                -- Convert frames
                mem-det-frame : readLoc s-after-g (AtStack frame slot) ≡
                                readLoc (proj₁ (exec-trace g-trace s₁' alloc-after-f-reclaim)) (AtStack frame slot)
                mem-det-frame = subst₂ (λ f1 f2 → readLoc s-after-g (AtStack f1 slot) ≡
                                                  readLoc (proj₁ (exec-trace g-trace s₁' alloc-after-f-reclaim)) (AtStack f2 slot))
                                       oag-frame-middle oag-frame-reclaim mem-det
                -- Convert exec result to s₂ using trace-correct
                s₂-eq : readLoc (proj₁ (exec-trace g-trace s₁' alloc-after-f-reclaim)) (AtStack frame slot) ≡
                        readLoc s₂ (AtStack frame slot)
                s₂-eq = cong (λ st → readLoc st (AtStack frame slot)) (IRResultAWF.trace-correct result-g)
            in trans mem-det-frame s₂-eq
  
          -- Memory agrees on heap (no heap writes in g-trace)
          g-mem-heap : ∀ h → readLoc s-after-g (AtDynamic h) ≡ readLoc s₂ (AtDynamic h)
          g-mem-heap h =
            let -- s-after-g preserves heap from s-after-middle
                g-heap = SMP.TracePrimitives.exec-trace-preserves-heap-loc g-trace
                           s-after-middle alloc-after-middle h g-tnhw
                -- s₂ preserves heap from s₁'
                exec-g-heap = SMP.TracePrimitives.exec-trace-preserves-heap-loc g-trace
                                s₁' alloc-after-f-reclaim h g-tnhw
                s₂-heap = subst (λ st → readLoc st (AtDynamic h) ≡ readLoc s₁' (AtDynamic h))
                                (IRResultAWF.trace-correct result-g) exec-g-heap
                -- After state-only hoist: s₁' = s-after-middle, derive via chain.
                middle-heap = SMP.TracePrimitives.exec-trace-preserves-heap-loc middle-trace
                                s-after-f alloc-after-f h tt
                f-heap-eq = f-mem-heap h
                s₁'-heap : readLoc s₁' (AtDynamic h) ≡ readLoc s₁ (AtDynamic h)
                s₁'-heap = trans middle-heap f-heap-eq
            in trans g-heap (trans middle-heap (trans f-heap-eq (trans (sym s₁'-heap) (sym s₂-heap))))
  
          -- Memory agrees on ancestor frames
          g-mem-ancestors : ∀ f' k → current-frame alloc-reclaim-g ≺ f' →
            readLoc s-after-g (AtStack f' k) ≡ readLoc s₂ (AtStack f' k)
          g-mem-ancestors f' k cf≺f' =
            let -- current-frame alloc-reclaim-g = frame
                frame≺f' : frame ≺ f'
                frame≺f' = cf≺f'
                -- s-after-g preserves ancestors from s-after-middle
                alloc-after-middle-cf≺f' : current-frame alloc-after-middle ≺ f'
                alloc-after-middle-cf≺f' = subst (_≺ f') (sym oag-frame-middle) frame≺f'
                g-anc = SMP.TracePrimitives.exec-trace-preserves-ancestor g-trace
                          s-after-middle alloc-after-middle f' k alloc-after-middle-cf≺f' g-tnhw
                -- s₂ preserves ancestors from s₁'
                alloc-f-reclaim-cf≺f' : current-frame alloc-after-f-reclaim ≺ f'
                alloc-f-reclaim-cf≺f' = frame≺f'
                exec-g-anc = SMP.TracePrimitives.exec-trace-preserves-ancestor g-trace
                               s₁' alloc-after-f-reclaim f' k alloc-f-reclaim-cf≺f' g-tnhw
                s₂-anc = subst (λ st → readLoc st (AtStack f' k) ≡ readLoc s₁' (AtStack f' k))
                               (IRResultAWF.trace-correct result-g) exec-g-anc
                -- After state-only hoist: s₁' = s-after-middle, derive via chain.
                alloc-after-f-cf≺f' : current-frame alloc-after-f ≺ f'
                alloc-after-f-cf≺f' = subst (_≺ f') (sym frame-after-f-eq) frame≺f'
                middle-anc = SMP.TracePrimitives.exec-trace-preserves-ancestor middle-trace
                               s-after-f alloc-after-f f' k alloc-after-f-cf≺f' tt
                f-anc-eq = f-mem-ancestors f' k frame≺f'
                s₁'-anc : readLoc s₁' (AtStack f' k) ≡ readLoc s₁ (AtStack f' k)
                s₁'-anc = trans middle-anc f-anc-eq
            in trans g-anc (trans middle-anc (trans f-anc-eq (trans (sym s₁'-anc) (sym s₂-anc))))
  
          -- Transfer validity from s₂ to s-after-g using positive regions
        valid-at-s-after-g : ValidAtWF mG alloc-reclaim-g (eval g x) snd-loc s-after-g
        valid-at-s-after-g = validityWF-mem-preserved-in-regions alloc-reclaim-g
                               (eval g x) snd-loc backup-slot reclaim-f s₂ s-after-g
                               snd-loc-before-reclaim-g backup≤reclaim-f' reclaim-f≤reclaim-g
                               g-mem-input-region g-mem-fresh-region g-mem-heap g-mem-ancestors
                               valid-s2-reclaimed
  
        -- Step 3: Transfer validity from s-after-g to s-final
        -- final-trace writes at snd-slot which is in [backup-slot, f-start) ⊂ [backup-slot, reclaim-f)
        -- So it doesn't write to input region [0, backup-slot) or fresh region [reclaim-f, reclaim-g)
  
        -- Memory agrees on input region [0, backup-slot): final-trace writes above backup-slot
        abstract
          final-mem-input-region : ∀ slot → slot < backup-slot →
            readLoc s-final (AtStack frame slot) ≡ readLoc s-after-g (AtStack frame slot)
          final-mem-input-region slot slot<backup =
            let slot<snd : slot < snd-slot
                slot<snd = ≤-trans slot<backup (≤-trans (n≤1+n backup-slot) (n≤1+n fst-slot))
                final-twa : TraceWritesAbove snd-slot final-trace
                final-twa = ≤-refl , tt
                final-pres = SMP.TracePrimitives.exec-trace-preserves-slot-below final-trace
                               s-after-g alloc-after-g snd-slot slot final-twa tt slot<snd
                final-pres-frame = subst (λ fr → readLoc s-after-final (AtStack fr slot) ≡
                                                 readLoc s-after-g (AtStack fr slot))
                                         frame-preserved-through final-pres
            in subst (λ st → readLoc st (AtStack frame slot) ≡ readLoc s-after-g (AtStack frame slot))
                     (sym s-final-eq) final-pres-frame
  
          -- Memory agrees on fresh region [reclaim-f, reclaim-g): final-trace writes below reclaim-f
          final-mem-fresh-region : ∀ slot → reclaim-f ≤ slot → slot < reclaim-g →
            readLoc s-final (AtStack frame slot) ≡ readLoc s-after-g (AtStack frame slot)
          final-mem-fresh-region slot rf≤slot _ =
            let final-twb : TraceWritesBelow reclaim-f final-trace
                final-twb = snd-slot<reclaim-f , tt  -- snd-slot < f-start ≤ reclaim-f
                final-pres = SMP.TracePrimitives.exec-trace-preserves-slot-above final-trace
                               s-after-g alloc-after-g reclaim-f slot final-twb tt rf≤slot
                final-pres-frame = subst (λ fr → readLoc s-after-final (AtStack fr slot) ≡
                                                 readLoc s-after-g (AtStack fr slot))
                                         frame-preserved-through final-pres
            in subst (λ st → readLoc st (AtStack frame slot) ≡ readLoc s-after-g (AtStack frame slot))
                     (sym s-final-eq) final-pres-frame
  
          -- Memory agrees on heap (no heap writes in final-trace)
          final-mem-heap : ∀ h → readLoc s-final (AtDynamic h) ≡ readLoc s-after-g (AtDynamic h)
          final-mem-heap h =
            let final-heap = SMP.TracePrimitives.exec-trace-preserves-heap-loc final-trace
                               s-after-g alloc-after-g h tt
            in subst (λ st → readLoc st (AtDynamic h) ≡ readLoc s-after-g (AtDynamic h))
                     (sym s-final-eq) final-heap
  
          -- Memory agrees on ancestor frames
          final-mem-ancestors : ∀ f' k → current-frame alloc-reclaim-g ≺ f' →
            readLoc s-final (AtStack f' k) ≡ readLoc s-after-g (AtStack f' k)
          final-mem-ancestors f' k cf≺f' =
            let frame≺f' : frame ≺ f'
                frame≺f' = cf≺f'
                alloc-after-g-cf≺f' : current-frame alloc-after-g ≺ f'
                alloc-after-g-cf≺f' = subst (_≺ f') (sym frame-preserved-through) frame≺f'
                final-anc = SMP.TracePrimitives.exec-trace-preserves-ancestor final-trace
                              s-after-g alloc-after-g f' k alloc-after-g-cf≺f' tt
            in subst (λ st → readLoc st (AtStack f' k) ≡ readLoc s-after-g (AtStack f' k))
                     (sym s-final-eq) final-anc
  
          -- Transfer validity from s-after-g to s-final using positive regions
        snd-valid-at-s-final : ValidAtWF mG alloc-reclaim-g (eval g x) snd-loc s-final
        snd-valid-at-s-final = validityWF-mem-preserved-in-regions alloc-reclaim-g
                                 (eval g x) snd-loc backup-slot reclaim-f s-after-g s-final
                                 snd-loc-before-reclaim-g backup≤reclaim-f' reclaim-f≤reclaim-g
                                 final-mem-input-region final-mem-fresh-region final-mem-heap final-mem-ancestors
                                 valid-at-s-after-g
  
        -- Step 4: Frontier advance (trivial since alloc-reclaim-g and alloc-final both have next-slot = reclaim-g)
        snd-valid : ValidAtWF mG alloc-final (eval g x) snd-loc s-final
        snd-valid = validityWF-frontier-advance (eval g x) snd-loc s-final refl ≤-refl ≤-refl snd-valid-at-s-final
  
        ------------------------------------------------------------------------
        -- Final pair validity
        ------------------------------------------------------------------------
        -- Plan 0.14 (Camp 2): run-pair handles Stack-mode pairs only;
        -- pair-loc is AtStack and LocMatchesMode Stack (AtStack _ _) = ⊤.
        pair-valid-wf-final : ValidAtWF Stack alloc-final
                                (pair (eval f x) (eval g x)) pair-loc s-final
        pair-valid-wf-final = valid-pair-wf tt fst-ptr snd-ptr fst-before snd-before
                                sucLoc-pair-before fst-valid snd-valid
