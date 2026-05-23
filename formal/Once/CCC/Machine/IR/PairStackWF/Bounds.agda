-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Machine.IR.PairStackWF.Bounds
--
-- Plan 0.17.1 / 0.18 — Cluster B extraction: pair-trace combinatorics
-- and budget bounds.  Pure structural facts about pair-trace's shape;
-- does NOT depend on input state, validity, or memory preservation.
--
-- Exports (used by PairStackWF.run-pair via projections):
--   pair-trace                       — the composed AbstractTrace
--   pair-max-slot                    — max-slot-written for the pair
--   pair-trace-writes-above
--   pair-trace-writes-below
--   pair-trace-slot-reads-above
--   pair-trace-slot-reads-below
--   pair-trace-no-heap-writes
--   pair-max-slot-bound              — max-slot-usage-bound
--   pair-reclaim-size-bound          — slot-stays-in-budget
--   pair-scratch-bounded
--   pair-max-heap-usage-bound
--
-- Nesting layout (matches PairStackWF/Validity.agda):
--   Bounds       — layout (slots, alloc-after-pair-slots).
--   .L2          — adds result-f + f-tnhw; derives reclaim-f,
--                  alloc-after-f-reclaim, f-trace, f-twa/twb/tsra/tsrb.
--   .L3          — adds result-g + g-tnhw; derives pair-trace,
--                  pair-max-slot, and the bound exports.
------------------------------------------------------------------------

module Once.CCC.Machine.IR.PairStackWF.Bounds where

open import Data.Nat using (ℕ; suc; _<_; _≤_; _≥_; s≤s; z≤n; _⊔_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; m≤n+m; n≤1+n; +-comm; +-assoc; +-monoˡ-≤; +-monoʳ-≤; <-≤-trans; m≤m⊔n; m≤n⊔m; ⊔-lub; ≤-reflexive)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; cong)

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

module BoundsImpl {FS : FrameSemantics} (program-bound : ℕ) where
  open FrameSemantics FS
  open AbstractExec {FS}
  open SMP.TracePrimitives {FS}

  open ClosureWellFormedDef {FS} program-bound
    using (IRResultAWF)

  ------------------------------------------------------------------------
  -- Bounds — outermost level: just the alloc-derived layout.
  ------------------------------------------------------------------------
  module Bounds
    (alloc : AllocState {FS})
    where

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

    alloc-after-pair-slots : AllocState {FS}
    alloc-after-pair-slots = record alloc { next-slot = f-start }

    -- Slot ordering facts used by the bound proofs.
    backup≤fst : backup-slot ≤ fst-slot
    backup≤fst = n≤1+n backup-slot

    backup≤snd : backup-slot ≤ snd-slot
    backup≤snd = ≤-trans backup≤fst (n≤1+n fst-slot)

    ----------------------------------------------------------------------
    -- L2 — adds result-f + f-tnhw.
    ----------------------------------------------------------------------
    module L2
      {A B : Type}
      (f : IR A B)
      (x : ⟦ A ⟧)
      (s-after-setup : LocState FS)
      (mF : AllocMode)
      (result-f : IRResultAWF mF f x s-after-setup alloc-after-pair-slots)
      (f-tnhw : TraceNoHeapWrites (IRResultAWF.trace result-f))
      where

      f-trace : AbstractTrace
      f-trace = IRResultAWF.trace result-f

      max-slot-f : ℕ
      max-slot-f = IRResultAWF.max-slot-written result-f

      rf : ℕ
      rf = IRResultAWF.stack-budget result-f

      sf : ℕ
      sf = IRResultAWF.scratch-budget result-f

      reclaim-f : ℕ
      reclaim-f = next-slot (IRResultAWF.final-alloc result-f)

      reclaim-f-above-f-start : f-start ≤ reclaim-f
      reclaim-f-above-f-start = IRResultAWF.slot-monotone result-f

      reclaim-f-bound : reclaim-f ≤ f-start +ℕ rf
      reclaim-f-bound = IRResultAWF.slot-stays-in-budget result-f

      alloc-after-f-reclaim : AllocState {FS}
      alloc-after-f-reclaim = record alloc
        { next-slot     = reclaim-f
        ; next-heap-ref = next-heap-ref (IRResultAWF.final-alloc result-f) }

      f-twa : TraceWritesAbove f-start f-trace
      f-twa = IRResultAWF.trace-writes-above result-f

      f-twb : TraceWritesBelow max-slot-f f-trace
      f-twb = IRResultAWF.trace-writes-below result-f

      f-tsra : TraceSlotReadsAbove f-start f-trace
      f-tsra = IRResultAWF.trace-slot-reads-above result-f

      f-tsrb : TraceSlotReadsBelow max-slot-f f-trace
      f-tsrb = IRResultAWF.trace-slot-reads-below result-f

      fst-slot<reclaim-f : fst-slot < reclaim-f
      fst-slot<reclaim-f = ≤-trans (n≤1+n snd-slot) reclaim-f-above-f-start

      snd-slot<reclaim-f : snd-slot < reclaim-f
      snd-slot<reclaim-f = reclaim-f-above-f-start

      backup≤reclaim-f : backup-slot ≤ reclaim-f
      backup≤reclaim-f = ≤-trans (n≤1+n backup-slot)
                           (≤-trans (n≤1+n fst-slot) (≤-trans (n≤1+n snd-slot) reclaim-f-above-f-start))

      --------------------------------------------------------------------
      -- L3 — adds result-g + g-tnhw; produces pair-trace + bound exports.
      --------------------------------------------------------------------
      module L3
        {C : Type}
        (g : IR A C)
        (s-after-middle : LocState FS)
        (mG : AllocMode)
        (result-g : IRResultAWF mG g x s-after-middle alloc-after-f-reclaim)
        (g-tnhw : TraceNoHeapWrites (IRResultAWF.trace result-g))
        where

        g-trace : AbstractTrace
        g-trace = IRResultAWF.trace result-g

        max-slot-g : ℕ
        max-slot-g = IRResultAWF.max-slot-written result-g

        rg : ℕ
        rg = IRResultAWF.stack-budget result-g

        sg : ℕ
        sg = IRResultAWF.scratch-budget result-g

        reclaim-g : ℕ
        reclaim-g = next-slot (IRResultAWF.final-alloc result-g)

        reclaim-g-bound : reclaim-g ≤ reclaim-f +ℕ rg
        reclaim-g-bound = IRResultAWF.slot-stays-in-budget result-g

        g-twa : TraceWritesAbove reclaim-f g-trace
        g-twa = IRResultAWF.trace-writes-above result-g

        g-twb : TraceWritesBelow max-slot-g g-trace
        g-twb = IRResultAWF.trace-writes-below result-g

        g-tsra : TraceSlotReadsAbove reclaim-f g-trace
        g-tsra = IRResultAWF.trace-slot-reads-above result-g

        g-tsrb : TraceSlotReadsBelow max-slot-g g-trace
        g-tsrb = IRResultAWF.trace-slot-reads-below result-g

        req-pair : ℕ
        req-pair = 1 +ℕ rf +ℕ rg +ℕ pair-slots

        req-pair-scratch : ℕ
        req-pair-scratch = 1 +ℕ sf +ℕ sg +ℕ pair-slots

        pair-max-slot : ℕ
        pair-max-slot = max-slot-f ⊔ max-slot-g

        pair-reclaim : ℕ
        pair-reclaim = reclaim-g

        ------------------------------------------------------------------
        -- The composed trace.
        ------------------------------------------------------------------
        pair-trace : AbstractTrace
        pair-trace = mov-to-output ∷ store-at-slot backup-slot ∷ instr-alloc-stack pair-overhead ∷
                     f-trace ++
                     store-at-slot fst-slot ∷ restore-input backup-slot ∷
                     g-trace ++
                     store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []

        ------------------------------------------------------------------
        -- Max-slot bounds.
        ------------------------------------------------------------------
        max-slot-f≤pair : max-slot-f ≤ pair-max-slot
        max-slot-f≤pair = m≤m⊔n max-slot-f max-slot-g

        max-slot-g≤pair : max-slot-g ≤ pair-max-slot
        max-slot-g≤pair = m≤n⊔m max-slot-f max-slot-g

        pair-max-slot-geq-final : pair-reclaim ≤ pair-max-slot
        pair-max-slot-geq-final = ≤-trans (IRResultAWF.max-slot-geq-final result-g) max-slot-g≤pair

        fst<reclaim-g : fst-slot < reclaim-g
        fst<reclaim-g = <-≤-trans fst-slot<reclaim-f (IRResultAWF.slot-monotone result-g)

        snd<reclaim-g : snd-slot < reclaim-g
        snd<reclaim-g = <-≤-trans snd-slot<reclaim-f (IRResultAWF.slot-monotone result-g)

        ------------------------------------------------------------------
        -- TraceWritesAbove backup-slot pair-trace.
        ------------------------------------------------------------------
        abstract
          f-twa-weak : TraceWritesAbove (suc backup-slot) f-trace
          f-twa-weak = trace-writes-above-mono (suc backup-slot) f-start f-trace
                         (≤-trans (n≤1+n fst-slot) (n≤1+n snd-slot)) f-twa

          final-seg-twa : TraceWritesAbove backup-slot (store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
          final-seg-twa = backup≤snd , tt

          g-plus-final-twa : TraceWritesAbove backup-slot (g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
          g-plus-final-twa = trace-writes-above-append backup-slot g-trace (store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
                               (trace-writes-above-mono backup-slot reclaim-f g-trace backup≤reclaim-f g-twa)
                               final-seg-twa

          middle-plus-twa : TraceWritesAbove backup-slot
                              (store-at-slot fst-slot ∷ restore-input backup-slot ∷ g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
          middle-plus-twa = backup≤fst , g-plus-final-twa

          f-plus-twa : TraceWritesAbove backup-slot
                         (f-trace ++ store-at-slot fst-slot ∷ restore-input backup-slot ∷ g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
          f-plus-twa = trace-writes-above-append backup-slot f-trace
                         (store-at-slot fst-slot ∷ restore-input backup-slot ∷ g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
                         (trace-writes-above-mono backup-slot (suc backup-slot) f-trace (n≤1+n backup-slot) f-twa-weak)
                         middle-plus-twa

          pair-trace-writes-above : TraceWritesAbove backup-slot pair-trace
          pair-trace-writes-above = ≤-refl , f-plus-twa

        ------------------------------------------------------------------
        -- TraceWritesBelow pair-max-slot pair-trace.
        ------------------------------------------------------------------
        abstract
          fst<bound : fst-slot < pair-max-slot
          fst<bound = <-≤-trans fst-slot<reclaim-f
                        (≤-trans (IRResultAWF.max-slot-geq-final result-f) max-slot-f≤pair)

          snd<bound : snd-slot < pair-max-slot
          snd<bound = <-≤-trans snd-slot<reclaim-f
                        (≤-trans (IRResultAWF.max-slot-geq-final result-f) max-slot-f≤pair)

          backup<bound : backup-slot < pair-max-slot
          backup<bound = <-≤-trans (s≤s backup≤fst) fst<bound

          final-seg-twb : TraceWritesBelow pair-max-slot (store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
          final-seg-twb = snd<bound , tt

          g-plus-final-twb : TraceWritesBelow pair-max-slot (g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
          g-plus-final-twb = trace-writes-below-append pair-max-slot g-trace (store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
                               (trace-writes-below-mono max-slot-g pair-max-slot g-trace max-slot-g≤pair g-twb)
                               final-seg-twb

          middle-plus-twb : TraceWritesBelow pair-max-slot
                              (store-at-slot fst-slot ∷ restore-input backup-slot ∷ g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
          middle-plus-twb = fst<bound , g-plus-final-twb

          f-plus-twb : TraceWritesBelow pair-max-slot
                         (f-trace ++ store-at-slot fst-slot ∷ restore-input backup-slot ∷ g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
          f-plus-twb = trace-writes-below-append pair-max-slot f-trace
                         (store-at-slot fst-slot ∷ restore-input backup-slot ∷ g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
                         (trace-writes-below-mono max-slot-f pair-max-slot f-trace max-slot-f≤pair f-twb)
                         middle-plus-twb

          pair-trace-writes-below : TraceWritesBelow pair-max-slot pair-trace
          pair-trace-writes-below = backup<bound , f-plus-twb

        ------------------------------------------------------------------
        -- TraceSlotReadsAbove backup-slot pair-trace.
        ------------------------------------------------------------------
        abstract
          final-seg-rsra : TraceSlotReadsAbove backup-slot (store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
          final-seg-rsra = tt

          g-plus-final-rsra : TraceSlotReadsAbove backup-slot (g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
          g-plus-final-rsra = trace-slot-reads-above-append backup-slot g-trace (store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
                                (trace-slot-reads-above-mono backup-slot reclaim-f g-trace backup≤reclaim-f g-tsra)
                                final-seg-rsra

          middle-plus-rsra : TraceSlotReadsAbove backup-slot
                               (store-at-slot fst-slot ∷ restore-input backup-slot ∷ g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
          middle-plus-rsra = ≤-refl , g-plus-final-rsra

          f-plus-rsra : TraceSlotReadsAbove backup-slot
                          (f-trace ++ store-at-slot fst-slot ∷ restore-input backup-slot ∷ g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
          f-plus-rsra = trace-slot-reads-above-append backup-slot f-trace
                          (store-at-slot fst-slot ∷ restore-input backup-slot ∷ g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
                          (trace-slot-reads-above-mono backup-slot (suc backup-slot) f-trace (n≤1+n backup-slot)
                            (trace-slot-reads-above-mono (suc backup-slot) f-start f-trace
                              (≤-trans (n≤1+n fst-slot) (n≤1+n snd-slot)) f-tsra))
                          middle-plus-rsra

          pair-trace-slot-reads-above : TraceSlotReadsAbove backup-slot pair-trace
          pair-trace-slot-reads-above = f-plus-rsra

        ------------------------------------------------------------------
        -- TraceSlotReadsBelow pair-max-slot pair-trace.
        ------------------------------------------------------------------
        abstract
          final-seg-rsrb : TraceSlotReadsBelow pair-max-slot (store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
          final-seg-rsrb = tt

          g-plus-final-rsrb : TraceSlotReadsBelow pair-max-slot (g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
          g-plus-final-rsrb = trace-slot-reads-below-append pair-max-slot g-trace (store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
                                (trace-slot-reads-below-mono max-slot-g pair-max-slot g-trace max-slot-g≤pair g-tsrb)
                                final-seg-rsrb

          middle-plus-rsrb : TraceSlotReadsBelow pair-max-slot
                               (store-at-slot fst-slot ∷ restore-input backup-slot ∷ g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
          middle-plus-rsrb = backup<bound , g-plus-final-rsrb

          f-plus-rsrb : TraceSlotReadsBelow pair-max-slot
                          (f-trace ++ store-at-slot fst-slot ∷ restore-input backup-slot ∷ g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
          f-plus-rsrb = trace-slot-reads-below-append pair-max-slot f-trace
                          (store-at-slot fst-slot ∷ restore-input backup-slot ∷ g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
                          (trace-slot-reads-below-mono max-slot-f pair-max-slot f-trace max-slot-f≤pair f-tsrb)
                          middle-plus-rsrb

          pair-trace-slot-reads-below : TraceSlotReadsBelow pair-max-slot pair-trace
          pair-trace-slot-reads-below = f-plus-rsrb

        ------------------------------------------------------------------
        -- TraceNoHeapWrites pair-trace.
        ------------------------------------------------------------------
        abstract
          pair-trace-no-heap-writes : TraceNoHeapWrites pair-trace
          pair-trace-no-heap-writes =
            trace-no-heap-writes-append (mov-to-output ∷ store-at-slot backup-slot ∷ [])
              (f-trace ++ store-at-slot fst-slot ∷ restore-input backup-slot ∷ g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
              tt
              (trace-no-heap-writes-append f-trace
                (store-at-slot fst-slot ∷ restore-input backup-slot ∷ g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
                f-tnhw
                (trace-no-heap-writes-append g-trace (store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []) g-tnhw tt))

        ------------------------------------------------------------------
        -- Plan 0.17.3 (frame-op fence): TraceNoFrameOps pair-trace.
        -- Hoisted into Bounds so PairStackWF.agda's mk-IRResultAWF-via-bump
        -- site can pass a single name instead of an inline append tower
        -- (which forced case-tree fusion at the producer site).
        ------------------------------------------------------------------
        abstract
          pair-trace-no-frame-ops : SMP.TraceNoFrameOps pair-trace
          pair-trace-no-frame-ops =
            tt , tt , tt ,
              SMP.trace-no-frame-ops-append f-trace
                (store-at-slot fst-slot ∷ restore-input backup-slot ∷ g-trace ++ store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
                (IRResultAWF.trace-no-frame-ops result-f)
                (tt , tt ,
                  SMP.trace-no-frame-ops-append g-trace (store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])
                    (IRResultAWF.trace-no-frame-ops result-g)
                    (tt , tt , tt))

        ------------------------------------------------------------------
        -- Slot/scratch budget arithmetic.
        ------------------------------------------------------------------
        abstract
          sss-rf-rg≡req-pair : (f-start +ℕ rf) +ℕ rg ≡ backup-slot +ℕ req-pair
          sss-rf-rg≡req-pair =
            let step1 : (((1 +ℕ rf) +ℕ rg) +ℕ 2) ≡ 3 +ℕ (rf +ℕ rg)
                step1 = trans (+-assoc (1 +ℕ rf) rg 2)
                        (trans (cong ((1 +ℕ rf) +ℕ_) (+-comm rg 2))
                        (trans (sym (+-assoc (1 +ℕ rf) 2 rg))
                        (trans (cong (_+ℕ rg) (+-assoc 1 rf 2))
                        (trans (cong (λ y → (1 +ℕ y) +ℕ rg) (+-comm rf 2))
                        (trans (cong (_+ℕ rg) (sym (+-assoc 1 2 rf))) (+-assoc 3 rf rg))))))
                step2 : backup-slot +ℕ (3 +ℕ (rf +ℕ rg)) ≡ suc (suc (suc (backup-slot +ℕ (rf +ℕ rg))))
                step2 = trans (sym (+-assoc backup-slot 3 (rf +ℕ rg)))
                          (trans (cong (_+ℕ (rf +ℕ rg)) (+-comm backup-slot 3))
                            (+-assoc 3 backup-slot (rf +ℕ rg)))
                step3 : (backup-slot +ℕ rf) +ℕ rg ≡ backup-slot +ℕ (rf +ℕ rg)
                step3 = +-assoc backup-slot rf rg
            in trans (cong (λ y → suc (suc (suc y))) step3)
                 (trans (sym step2) (cong (backup-slot +ℕ_) (sym step1)))

          reclaim-g≤-rf-rg : reclaim-g ≤ (f-start +ℕ rf) +ℕ rg
          reclaim-g≤-rf-rg = ≤-trans reclaim-g-bound (+-monoˡ-≤ rg reclaim-f-bound)

          pair-reclaim-size-bound : pair-reclaim ≤ backup-slot +ℕ req-pair
          pair-reclaim-size-bound = ≤-trans reclaim-g≤-rf-rg
            (subst (((f-start +ℕ rf) +ℕ rg) ≤_) sss-rf-rg≡req-pair ≤-refl)

          pair-max-slot-bound : pair-max-slot ≤ backup-slot +ℕ req-pair
          pair-max-slot-bound =
            ⊔-lub max-slot-f-bound max-slot-g-bound
            where
              max-slot-f-usage : max-slot-f ≤ f-start +ℕ rf
              max-slot-f-usage = IRResultAWF.max-slot-usage-bound result-f

              max-slot-g-usage : max-slot-g ≤ reclaim-f +ℕ rg
              max-slot-g-usage = IRResultAWF.max-slot-usage-bound result-g

              max-slot-f-bound : max-slot-f ≤ backup-slot +ℕ req-pair
              max-slot-f-bound = ≤-trans max-slot-f-usage
                (≤-trans (m≤m+n (f-start +ℕ rf) rg)
                         (subst (((f-start +ℕ rf) +ℕ rg) ≤_) sss-rf-rg≡req-pair ≤-refl))

              max-slot-g-bound : max-slot-g ≤ backup-slot +ℕ req-pair
              max-slot-g-bound = ≤-trans max-slot-g-usage
                (≤-trans (+-monoˡ-≤ rg reclaim-f-bound)
                         (subst (((f-start +ℕ rf) +ℕ rg) ≤_) sss-rf-rg≡req-pair ≤-refl))

          sss-sf-sg≡req-pair-scratch : (f-start +ℕ sf) +ℕ sg ≡ backup-slot +ℕ req-pair-scratch
          sss-sf-sg≡req-pair-scratch =
            let step1 : (((1 +ℕ sf) +ℕ sg) +ℕ 2) ≡ 3 +ℕ (sf +ℕ sg)
                step1 = trans (+-assoc (1 +ℕ sf) sg 2)
                        (trans (cong ((1 +ℕ sf) +ℕ_) (+-comm sg 2))
                        (trans (sym (+-assoc (1 +ℕ sf) 2 sg))
                        (trans (cong (_+ℕ sg) (+-assoc 1 sf 2))
                        (trans (cong (λ y → (1 +ℕ y) +ℕ sg) (+-comm sf 2))
                        (trans (cong (_+ℕ sg) (sym (+-assoc 1 2 sf))) (+-assoc 3 sf sg))))))
                step2 : backup-slot +ℕ (3 +ℕ (sf +ℕ sg)) ≡ suc (suc (suc (backup-slot +ℕ (sf +ℕ sg))))
                step2 = trans (sym (+-assoc backup-slot 3 (sf +ℕ sg)))
                          (trans (cong (_+ℕ (sf +ℕ sg)) (+-comm backup-slot 3))
                            (+-assoc 3 backup-slot (sf +ℕ sg)))
                step3 : (backup-slot +ℕ sf) +ℕ sg ≡ backup-slot +ℕ (sf +ℕ sg)
                step3 = +-assoc backup-slot sf sg
            in trans (cong (λ y → suc (suc (suc y))) step3)
                 (trans (sym step2) (cong (backup-slot +ℕ_) (sym step1)))

          -- pair-scratch-bounded uses reclaim-g (= next-slot alloc-final) directly;
          -- when the consumer needs the alloc-final-shape statement, it transports
          -- via the (definitional) equality next-slot alloc-final ≡ reclaim-g.
          pair-scratch-bounded : pair-max-slot ≤ reclaim-g +ℕ req-pair-scratch
          pair-scratch-bounded =
            ⊔-lub f-scratch-bound g-scratch-bound
            where
              alloc₁≤reclaim-g : next-slot (IRResultAWF.final-alloc result-f) ≤ reclaim-g
              alloc₁≤reclaim-g = IRResultAWF.slot-monotone result-g

              f-scratch-bound : max-slot-f ≤ reclaim-g +ℕ req-pair-scratch
              f-scratch-bound =
                ≤-trans (IRResultAWF.scratch-bounded result-f)
                  (≤-trans (+-monoˡ-≤ sf alloc₁≤reclaim-g)
                    (+-monoʳ-≤ reclaim-g
                      (≤-trans (m≤m+n sf sg)
                        (≤-trans (m≤m+n (sf +ℕ sg) pair-slots)
                                 (m≤n+m ((sf +ℕ sg) +ℕ pair-slots) 1)))))

              g-scratch-bound : max-slot-g ≤ reclaim-g +ℕ req-pair-scratch
              g-scratch-bound =
                ≤-trans (IRResultAWF.scratch-bounded result-g)
                  (+-monoʳ-≤ reclaim-g
                    (≤-trans (m≤n+m sg sf)
                      (≤-trans (m≤m+n (sf +ℕ sg) pair-slots)
                               (m≤n+m ((sf +ℕ sg) +ℕ pair-slots) 1))))

        ------------------------------------------------------------------
        -- Heap budget bound.
        ------------------------------------------------------------------
        abstract
          pair-max-heap-usage-bound :
            IRResultAWF.max-heap-ref-written result-g
            ≤ next-heap-ref alloc +ℕ (IRResultAWF.heap-budget result-f +ℕ IRResultAWF.heap-budget result-g)
          pair-max-heap-usage-bound = ≤-trans g-bound (≤-trans step (≤-reflexive (+-assoc (next-heap-ref alloc) _ _)))
            where
              g-bound : IRResultAWF.max-heap-ref-written result-g
                        ≤ next-heap-ref (IRResultAWF.final-alloc result-f) +ℕ IRResultAWF.heap-budget result-g
              g-bound = IRResultAWF.max-heap-usage-bound result-g
              f-bound : next-heap-ref (IRResultAWF.final-alloc result-f)
                        ≤ next-heap-ref alloc +ℕ IRResultAWF.heap-budget result-f
              f-bound = ≤-trans (IRResultAWF.max-heap-ref-geq-final result-f)
                                (IRResultAWF.max-heap-usage-bound result-f)
              step : next-heap-ref (IRResultAWF.final-alloc result-f) +ℕ IRResultAWF.heap-budget result-g
                     ≤ (next-heap-ref alloc +ℕ IRResultAWF.heap-budget result-f) +ℕ IRResultAWF.heap-budget result-g
              step = +-monoˡ-≤ (IRResultAWF.heap-budget result-g) f-bound
