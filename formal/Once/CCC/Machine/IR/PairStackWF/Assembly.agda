-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Machine.IR.PairStackWF.Assembly
--
-- Plan 0.17.1 / 0.18 — Cluster A extraction: state-evolution proofs.
--
-- Exports (used by PairStackWF.run-pair via projections):
--   s-final, s-final-eq, alloc-final
--   alloc-correct-pair                 — exec-alloc-eq
--   pair-trace-twf                     — TraceWF s alloc pair-trace
--   mem-preserved-pair                 — caller-frontier preservation
--   rax-eq                             — Output register holds pair-loc
--   not-halted-final                   — halted s-final ≡ false
--   s-after-snd-store / alloc-after-snd-store / frame-after-snd-store
--   frame-preserved-through
--
-- Depends on PairStackWF.Bounds for pair-trace + trace-bound projections.
-- The middle-trace's restore-input precondition is passed as a
-- parameter (PairStackWF provides it via Validity.L2's
-- middle-restore-input-witness).
--
-- Nesting layout:
--   Assembly     — function args (s, alloc, not-halted); layout + setup.
--   .L2          — adds result-f + f-tnhw + middle-restore-input-witness;
--                  derives runtime f-states + middle-trace.
--   .L3          — adds result-g + g-tnhw; derives g-states +
--                  s-final + heavy state-evolution proofs.
------------------------------------------------------------------------

module Once.CCC.Machine.IR.PairStackWF.Assembly where

open import Data.Nat using (ℕ; suc; _<_; _≤_; s≤s; z≤n) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n; +-comm)
open import Data.Bool using (false)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym; cong; subst)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore hiding (AllocMode; Stack; Heap)
open import Once.Semantics.Machine using (⟦_⟧)
open import Once.CCC.IR
open import Once.CCC.Eval using (eval)
open import Once.CCC.IR.Size
open import Once.CCC.IR.Stack
open import Once.CCC.Machine.Allocation hiding (AllocMode)
open import Once.CCC.Machine.ClosureWellFormed

import Once.CCC.Machine.SMPrimitives as SMP
import Once.CCC.Machine.IR.PairStackWF.Bounds as PB

module AssemblyImpl {FS : FrameSemantics} (program-bound : ℕ) where
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

  open ClosureWellFormedDef {FS} program-bound
    using (IRResultAWF)

  module BImpl = PB.BoundsImpl {FS} program-bound

  ------------------------------------------------------------------------
  -- Assembly — outermost level: function args, layout, setup.
  ------------------------------------------------------------------------
  module Assembly
    {A B C : Type}
    (f : IR A B) (g : IR A C) (x : ⟦ A ⟧)
    (s : LocState FS) (alloc : AllocState {FS})
    (not-halted : halted s ≡ false)
    where

    module B = BImpl.Bounds alloc
    open B
      using ( frame; backup-slot; fst-slot; snd-slot; f-start; pair-overhead;
              alloc-after-pair-slots; backup≤fst; backup≤snd )

    -- Setup trace and derived states
    setup-trace : AbstractTrace
    setup-trace = mov-to-output ∷ store-at-slot backup-slot ∷ instr-alloc-stack pair-overhead ∷ []

    s-after-setup : LocState FS
    s-after-setup = proj₁ (exec-trace setup-trace s alloc)

    alloc-after-setup : AllocState {FS}
    alloc-after-setup = proj₂ (exec-trace setup-trace s alloc)

    setup-twf : TraceWF s alloc setup-trace
    setup-twf = twf-∷ tt (twf-∷ tt (twf-∷ tt twf-[]))

    not-halted-after-setup : halted s-after-setup ≡ false
    not-halted-after-setup = exec-trace-preserves-halted-WF setup-trace s alloc not-halted setup-twf

    ----------------------------------------------------------------------
    -- L2 — adds f-side data + middle-restore-input-witness.
    ----------------------------------------------------------------------
    module L2
      (mF : AllocMode)
      (result-f : IRResultAWF mF f x s-after-setup alloc-after-pair-slots)
      (f-tnhw : TraceNoHeapWrites (IRResultAWF.trace result-f))
      where

      module BL2 = B.L2 f x s-after-setup mF result-f f-tnhw
      open BL2
        using ( f-trace; max-slot-f; rf; sf; reclaim-f; reclaim-f-above-f-start;
                reclaim-f-bound; alloc-after-f-reclaim;
                f-twa; f-twb; f-tsra; f-tsrb;
                fst-slot<reclaim-f; snd-slot<reclaim-f; backup≤reclaim-f )

      s-after-f : LocState FS
      s-after-f = proj₁ (exec-trace f-trace s-after-setup alloc-after-setup)

      alloc-after-f : AllocState {FS}
      alloc-after-f = proj₂ (exec-trace f-trace s-after-setup alloc-after-setup)

      f-frame-eq : current-frame alloc-after-pair-slots ≡ current-frame alloc-after-setup
      f-frame-eq = trans refl (sym (exec-trace-preserves-frame setup-trace s alloc))

      f-tph : TraceWF s-after-setup alloc-after-pair-slots f-trace
      f-tph = IRResultAWF.trace-twf result-f

      f-tph-runtime : TraceWF s-after-setup alloc-after-setup f-trace
      f-tph-runtime = TraceWF-frame-eq f-frame-eq f-tph

      not-halted-after-f : halted s-after-f ≡ false
      not-halted-after-f = exec-trace-preserves-halted-WF f-trace s-after-setup alloc-after-setup
                             not-halted-after-setup f-tph-runtime

      s-after-fst-store : LocState FS
      s-after-fst-store = proj₁ (exec-abstract (store-at-slot fst-slot) s-after-f alloc-after-f)

      alloc-after-fst-store : AllocState {FS}
      alloc-after-fst-store = proj₂ (exec-abstract (store-at-slot fst-slot) s-after-f alloc-after-f)

      middle-trace : AbstractTrace
      middle-trace = store-at-slot fst-slot ∷ restore-input backup-slot ∷ []

      ------------------------------------------------------------------
      -- L3 — adds g-side data + middle-restore-input-witness.
      --
      -- middle-restore-input-witness is hoisted to this level because
      -- its type mentions s-after-fst-store/alloc-after-fst-store
      -- which are L2-derived.
      ------------------------------------------------------------------
      module L3
        (mG : AllocMode)
        (result-g : IRResultAWF mG g x
                      (proj₁ (exec-trace middle-trace s-after-f alloc-after-f))
                      alloc-after-f-reclaim)
        (g-tnhw : TraceNoHeapWrites (IRResultAWF.trace result-g))
        (middle-restore-input-witness :
           InstrWF s-after-fst-store alloc-after-fst-store (restore-input backup-slot))
        where

        middle-twf : TraceWF s-after-f alloc-after-f middle-trace
        middle-twf = twf-∷ tt (twf-∷ middle-restore-input-witness twf-[])

        s-after-middle : LocState FS
        s-after-middle = proj₁ (exec-trace middle-trace s-after-f alloc-after-f)

        alloc-after-middle : AllocState {FS}
        alloc-after-middle = proj₂ (exec-trace middle-trace s-after-f alloc-after-f)

        not-halted-after-middle : halted s-after-middle ≡ false
        not-halted-after-middle = exec-trace-preserves-halted-WF middle-trace s-after-f alloc-after-f
                                    not-halted-after-f middle-twf

        module BL3 = BL2.L3 g s-after-middle mG result-g g-tnhw
        open BL3
          using ( g-trace; max-slot-g; rg; sg; reclaim-g; reclaim-g-bound;
                  g-twa; g-twb; g-tsra; g-tsrb;
                  pair-trace; pair-max-slot; pair-reclaim;
                  req-pair; req-pair-scratch;
                  pair-trace-writes-above; pair-trace-writes-below;
                  pair-trace-slot-reads-above; pair-trace-slot-reads-below;
                  pair-trace-no-heap-writes;
                  pair-max-slot-bound; pair-reclaim-size-bound; pair-scratch-bounded;
                  pair-max-heap-usage-bound; pair-max-slot-geq-final;
                  fst<reclaim-g; snd<reclaim-g )

        alloc-final : AllocState {FS}
        alloc-final = record alloc { next-slot     = reclaim-g
                                   ; next-heap-ref = next-heap-ref (IRResultAWF.final-alloc result-g) }

        s-after-g : LocState FS
        s-after-g = proj₁ (exec-trace g-trace s-after-middle alloc-after-middle)

        alloc-after-g : AllocState {FS}
        alloc-after-g = proj₂ (exec-trace g-trace s-after-middle alloc-after-middle)

        g-frame-eq : current-frame alloc-after-f-reclaim ≡ current-frame alloc-after-middle
        g-frame-eq = sym (trans (exec-trace-preserves-frame middle-trace s-after-f alloc-after-f)
                          (trans (exec-trace-preserves-frame f-trace s-after-setup alloc-after-setup)
                                 (exec-trace-preserves-frame setup-trace s alloc)))

        g-tph : TraceWF s-after-middle alloc-after-f-reclaim g-trace
        g-tph = IRResultAWF.trace-twf result-g

        g-tph-runtime : TraceWF s-after-middle alloc-after-middle g-trace
        g-tph-runtime = TraceWF-frame-eq g-frame-eq g-tph

        not-halted-after-g : halted s-after-g ≡ false
        not-halted-after-g = exec-trace-preserves-halted-WF g-trace s-after-middle alloc-after-middle
                               not-halted-after-middle g-tph-runtime

        final-trace : AbstractTrace
        final-trace = store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []

        s-after-final : LocState FS
        s-after-final = proj₁ (exec-trace final-trace s-after-g alloc-after-g)

        final-twf : TraceWF s-after-g alloc-after-g final-trace
        final-twf = twf-∷ tt (twf-∷ tt twf-[])

        s-final : LocState FS
        s-final = proj₁ (exec-trace pair-trace s alloc)

        ------------------------------------------------------------------
        -- s-final ≡ s-after-final via trace decomposition.
        ------------------------------------------------------------------
        abstract
          s-final-eq : s-final ≡ s-after-final
          s-final-eq =
            let rest-after-setup = f-trace ++ store-at-slot fst-slot ∷ restore-input backup-slot ∷
                                   g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []
                rest-after-f = store-at-slot fst-slot ∷ restore-input backup-slot ∷
                               g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []
                rest-after-middle = g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []
                step1 = exec-trace-append setup-trace rest-after-setup s alloc
                step2 = exec-trace-append f-trace rest-after-f s-after-setup alloc-after-setup
                step3 = exec-trace-append middle-trace rest-after-middle s-after-f alloc-after-f
                step4 = exec-trace-append g-trace final-trace s-after-middle alloc-after-middle
            in cong proj₁ (trans step1 (trans step2 (trans step3 step4)))

        ------------------------------------------------------------------
        -- Frame preservation through the full pair-trace.
        ------------------------------------------------------------------
        abstract
          frame-preserved-through : current-frame alloc-after-g ≡ frame
          frame-preserved-through =
            trans (exec-trace-preserves-frame g-trace s-after-middle alloc-after-middle)
            (trans (exec-trace-preserves-frame middle-trace s-after-f alloc-after-f)
            (trans (exec-trace-preserves-frame f-trace s-after-setup alloc-after-setup)
                   (exec-trace-preserves-frame setup-trace s alloc)))

        ------------------------------------------------------------------
        -- alloc-correct-pair: proj₂ (exec-trace pair-trace s alloc) ≡ alloc-final
        --
        -- Walks 5 trace segments via exec-trace-append, then bridges
        -- runtime alloc to alloc-final using result-f.alloc-correct /
        -- result-g.alloc-correct via the alloc-setup-eq-pair-slots and
        -- alloc-after-middle-eq-f-reclaim bridges.
        ------------------------------------------------------------------
        abstract
          alloc-after-final-eq-after-g :
            proj₂ (exec-trace final-trace s-after-g alloc-after-g) ≡ alloc-after-g
          alloc-after-final-eq-after-g =
            let not-halted-store = exec-abstract-preserves-halted (store-at-slot snd-slot)
                  s-after-g alloc-after-g not-halted-after-g iph-store-at-slot
                step1 = exec-trace-cons (store-at-slot snd-slot) (lea-slot fst-slot ∷ [])
                          s-after-g alloc-after-g not-halted-after-g
                step2 = exec-trace-single (lea-slot fst-slot)
                          (proj₁ (exec-abstract (store-at-slot snd-slot) s-after-g alloc-after-g))
                          (proj₂ (exec-abstract (store-at-slot snd-slot) s-after-g alloc-after-g))
                          not-halted-store
            in cong proj₂ (trans step1 step2)

          alloc-after-middle-eq-after-f : alloc-after-middle ≡ alloc-after-f
          alloc-after-middle-eq-after-f =
            let not-halted-store = exec-abstract-preserves-halted (store-at-slot fst-slot)
                  s-after-f alloc-after-f not-halted-after-f iph-store-at-slot
                step1 = exec-trace-cons (store-at-slot fst-slot) (restore-input backup-slot ∷ [])
                          s-after-f alloc-after-f not-halted-after-f
                step2 = exec-trace-single (restore-input backup-slot)
                          (proj₁ (exec-abstract (store-at-slot fst-slot) s-after-f alloc-after-f))
                          (proj₂ (exec-abstract (store-at-slot fst-slot) s-after-f alloc-after-f))
                          not-halted-store
                restore-preserves-alloc =
                  SMP.RecSchemeSemantics.exec-abstract-restore-input-preserves-alloc {FS}
                    backup-slot
                    (proj₁ (exec-abstract (store-at-slot fst-slot) s-after-f alloc-after-f))
                    (proj₂ (exec-abstract (store-at-slot fst-slot) s-after-f alloc-after-f))
            in trans (cong proj₂ (trans step1 step2)) restore-preserves-alloc

          alloc-setup-eq-pair-slots : alloc-after-setup ≡ alloc-after-pair-slots
          alloc-setup-eq-pair-slots =
            let s₁ʳ = proj₁ (exec-abstract mov-to-output s alloc)
                alloc₁ʳ = proj₂ (exec-abstract mov-to-output s alloc)
                not-halted₁ʳ = exec-abstract-preserves-halted mov-to-output s alloc not-halted iph-mov-to-output
                s₂ʳ = proj₁ (exec-abstract (store-at-slot backup-slot) s₁ʳ alloc₁ʳ)
                alloc₂ʳ = proj₂ (exec-abstract (store-at-slot backup-slot) s₁ʳ alloc₁ʳ)
                not-halted₂ʳ = exec-abstract-preserves-halted (store-at-slot backup-slot) s₁ʳ alloc₁ʳ not-halted₁ʳ iph-store-at-slot
                setup-decomp = exec-trace-cons mov-to-output _ s alloc not-halted
                store-decomp = exec-trace-cons (store-at-slot backup-slot) _ s₁ʳ alloc₁ʳ not-halted₁ʳ
                alloc-single = exec-trace-single (instr-alloc-stack pair-overhead) s₂ʳ alloc₂ʳ not-halted₂ʳ
                f-start-arith : next-slot alloc +ℕ pair-overhead ≡ f-start
                f-start-arith = trans (+-comm (next-slot alloc) 3) refl
                via-chain : proj₂ (exec-trace setup-trace s alloc) ≡
                            record alloc { next-slot = next-slot alloc +ℕ pair-overhead }
                via-chain = cong proj₂ (trans setup-decomp (trans store-decomp alloc-single))
            in trans via-chain
                     (cong (λ n → record alloc { next-slot = n }) f-start-arith)

          alloc-after-f-eq-final-alloc-f : alloc-after-f ≡ IRResultAWF.final-alloc result-f
          alloc-after-f-eq-final-alloc-f =
            let cong-alloc : exec-trace f-trace s-after-setup alloc-after-setup ≡
                             exec-trace f-trace s-after-setup alloc-after-pair-slots
                cong-alloc = cong (exec-trace f-trace s-after-setup) alloc-setup-eq-pair-slots
            in trans (cong proj₂ cong-alloc) (IRResultAWF.alloc-correct result-f)

          alloc-after-f-reclaim-eq-final-alloc-f : alloc-after-f-reclaim ≡ IRResultAWF.final-alloc result-f
          alloc-after-f-reclaim-eq-final-alloc-f =
            cong (λ fr → record (IRResultAWF.final-alloc result-f)
                           { current-frame = fr })
                 (sym (IRResultAWF.frame-preserved result-f))

          alloc-after-middle-eq-f-reclaim : alloc-after-middle ≡ alloc-after-f-reclaim
          alloc-after-middle-eq-f-reclaim =
            trans alloc-after-middle-eq-after-f
                  (trans alloc-after-f-eq-final-alloc-f
                         (sym alloc-after-f-reclaim-eq-final-alloc-f))

          alloc-after-g-eq-final-alloc-g : alloc-after-g ≡ IRResultAWF.final-alloc result-g
          alloc-after-g-eq-final-alloc-g =
            let cong-alloc : exec-trace g-trace s-after-middle alloc-after-middle ≡
                             exec-trace g-trace s-after-middle alloc-after-f-reclaim
                cong-alloc = cong (exec-trace g-trace s-after-middle) alloc-after-middle-eq-f-reclaim
            in trans (cong proj₂ cong-alloc) (IRResultAWF.alloc-correct result-g)

          final-alloc-g-eq-alloc-final : IRResultAWF.final-alloc result-g ≡ alloc-final
          final-alloc-g-eq-alloc-final =
            let frame-g-eq-alloc : current-frame (IRResultAWF.final-alloc result-g) ≡ current-frame alloc
                frame-g-eq-alloc = IRResultAWF.frame-preserved result-g
            in cong (λ fr → record (IRResultAWF.final-alloc result-g) { current-frame = fr })
                    frame-g-eq-alloc

          alloc-correct-pair : proj₂ (exec-trace pair-trace s alloc) ≡ alloc-final
          alloc-correct-pair =
            let rest-after-setup = f-trace ++ store-at-slot fst-slot ∷ restore-input backup-slot ∷
                                   g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []
                rest-after-f = store-at-slot fst-slot ∷ restore-input backup-slot ∷
                               g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []
                rest-after-middle = g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []
                step1 = exec-trace-append setup-trace rest-after-setup s alloc
                step2 = exec-trace-append f-trace rest-after-f s-after-setup alloc-after-setup
                step3 = exec-trace-append middle-trace rest-after-middle s-after-f alloc-after-f
                step4 = exec-trace-append g-trace final-trace s-after-middle alloc-after-middle
                chain : proj₂ (exec-trace pair-trace s alloc) ≡
                        proj₂ (exec-trace final-trace s-after-g alloc-after-g)
                chain = cong proj₂ (trans step1 (trans step2 (trans step3 step4)))
            in trans chain
                (trans alloc-after-final-eq-after-g
                  (trans alloc-after-g-eq-final-alloc-g final-alloc-g-eq-alloc-final))

        ------------------------------------------------------------------
        -- pair-trace-twf: TraceWF s alloc pair-trace.
        ------------------------------------------------------------------
        abstract
          pair-trace-twf : TraceWF s alloc pair-trace
          pair-trace-twf =
            twf-++ not-halted setup-twf
              (twf-++ not-halted-after-setup f-tph-runtime
                (twf-++ not-halted-after-f middle-twf
                  (twf-++ not-halted-after-middle g-tph-runtime
                    final-twf)))

        ------------------------------------------------------------------
        -- mem-preserved-pair: caller-frontier locations preserved.
        ------------------------------------------------------------------
        abstract
          mem-preserved-pair : ∀ loc → BeforeFrontier alloc loc → readLoc s-final loc ≡ readLoc s loc
          mem-preserved-pair (AtStack f' k) (stack-before f'≡cf k<next) =
            subst (λ fr → readLoc s-final (AtStack fr k) ≡ readLoc s (AtStack fr k))
                  (sym f'≡cf)
                  (exec-trace-preserves-slot-below pair-trace s alloc backup-slot k
                     pair-trace-writes-above pair-trace-no-heap-writes k<next)
          mem-preserved-pair (AtStack f' k) (stack-ancestor cf≺f' _) =
            exec-trace-preserves-ancestor pair-trace s alloc f' k cf≺f' pair-trace-no-heap-writes
          mem-preserved-pair (AtDynamic h) (heap-before _) =
            exec-trace-preserves-heap-loc pair-trace s alloc h pair-trace-no-heap-writes

        ------------------------------------------------------------------
        -- rax-eq cluster: lea-slot fst-slot sets Output to AtStack frame fst-slot.
        ------------------------------------------------------------------
        s-after-snd-store : LocState FS
        s-after-snd-store = proj₁ (exec-abstract (store-at-slot snd-slot) s-after-g alloc-after-g)

        alloc-after-snd-store : AllocState {FS}
        alloc-after-snd-store = proj₂ (exec-abstract (store-at-slot snd-slot) s-after-g alloc-after-g)

        abstract
          not-halted-after-snd-store : halted s-after-snd-store ≡ false
          not-halted-after-snd-store = trans (store-at-slot-halted snd-slot s-after-g alloc-after-g) not-halted-after-g

          frame-after-snd-store : current-frame alloc-after-snd-store ≡ frame
          frame-after-snd-store = trans (exec-abstract-preserves-frame (store-at-slot snd-slot) s-after-g alloc-after-g)
                                        frame-preserved-through

          final-trace-decomp : exec-trace final-trace s-after-g alloc-after-g ≡
                               exec-trace (lea-slot fst-slot ∷ []) s-after-snd-store alloc-after-snd-store
          final-trace-decomp = exec-trace-cons (store-at-slot snd-slot) (lea-slot fst-slot ∷ [])
                                 s-after-g alloc-after-g not-halted-after-g

          lea-single : exec-trace (lea-slot fst-slot ∷ []) s-after-snd-store alloc-after-snd-store ≡
                       exec-abstract (lea-slot fst-slot) s-after-snd-store alloc-after-snd-store
          lea-single = exec-trace-single (lea-slot fst-slot) s-after-snd-store alloc-after-snd-store not-halted-after-snd-store

          s-after-final-eq : s-after-final ≡ proj₁ (exec-abstract (lea-slot fst-slot) s-after-snd-store alloc-after-snd-store)
          s-after-final-eq = cong proj₁ (trans final-trace-decomp lea-single)

          rax-eq : readReg (regs s-final) Output ≡ SV-Ptr (AtStack frame fst-slot)
          rax-eq =
            let eq1 = cong (λ st → readReg (regs st) Output) s-final-eq
                eq2 = cong (λ st → readReg (regs st) Output) s-after-final-eq
                eq3 = lea-slot-result fst-slot s-after-snd-store alloc-after-snd-store
                eq4 = cong (λ fr → SV-Ptr (AtStack fr fst-slot)) frame-after-snd-store
            in trans eq1 (trans eq2 (trans eq3 eq4))

          not-halted-final : halted s-final ≡ false
          not-halted-final = exec-trace-preserves-halted-WF pair-trace s alloc not-halted pair-trace-twf
