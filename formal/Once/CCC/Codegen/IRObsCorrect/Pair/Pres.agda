-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres
--
-- D207: what the pair's run LEAVES ALONE, and the five-segment event splice.
-- Split from `Pair` for the per-module check cap.
------------------------------------------------------------------------


open import Once.Spec.Name using (CanonicalName)
import Once.CCC.Machine.SMCore as SMCore
import Once.CCC.FrameSemantics as FrameSemantics′

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.Pair.Pres (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtDynamic; AtStack)
open import Once.CCC.Machine.SMCore using (AllocState; AbstractTrace; LocState; StoredValue; mov-to-output; store-at-slot; restore-input; load-from-slot; store-indirect-suc; store-indirect; mov-to-input; instr-alloc-heap; sv-as-loc; readReg; Input1; module LocState; module AllocState)
open AllocState using (current-frame; saved-frames; next-heap-ref)
open LocState using (regs)
open import Once.IRTy using (IRTy)
open import Once.Memory.HeapAddress using (HeapLocation)

import Once.CCC.FrameSemantics
import Once.CCC.Machine.SMPrimitives
import Once.IRTy
import Once.IR
import Once.Semantics.Machine as EvV
import Once.CCC.Machine.ReadTypedAdequate as RTA
import Once.Denotation.DenotTrace as DT
import Once.IR.Semantics.Trace as TM

open import Once.Denotation.Approx using (NotCut; done)
open import Once.Res using (returns)

module PairPresC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}

  -- The prologue and the mid rows as TOP-LEVEL functions, so that `PairPres`'s
  -- own TELESCOPE can name the states its two induction hypotheses run from
  -- (a module parameter cannot mention a definition from the module's body).
  pair-p1 pair-p2 : AbstractTrace → ℕ → ℕ → LocState FS → AllocState {FS}
                  → StoredValue FS → List ℕ → FlatState
  pair-p1 prog base n s alloc cl rs =
    flat-exec-instr mov-to-output prog (entry-flat base s alloc cl rs)
  pair-p2 prog base n s alloc cl rs =
    flat-exec-instr (store-at-slot n) prog (pair-p1 prog base n s alloc cl rs)

  pair-m1 pair-m2 : AbstractTrace → ℕ → FlatState → FlatState
  pair-m1 prog n fsF = flat-exec-instr (store-at-slot (suc n)) prog fsF
  pair-m2 prog n fsF = flat-exec-instr (restore-input n) prog (pair-m1 prog n fsF)

  module PairPres
    {A B C : IRTy} (f : IR A B) (g : IR A C)
    (n l : ℕ) (prog : AbstractTrace) (base : ℕ)
    (s : LocState FS) (alloc : AllocState {FS}) (cl : StoredValue FS) (rs : List ℕ)
    -- `f`'s induction hypothesis, at the state the two prologue rows leave.
    -- Its placement `bf₀` is free: preservation does not care where the
    -- fragment sits, only what frontier it was emitted at (`f-start`).
    {xf : ⟦ A ⟧} {kf bf₀ : ℕ}
    (vrF : ValueRealized prog bf₀ (suc (suc (suc (suc n)))) l f xf
             (floc (pair-p2 prog base n s alloc cl rs)) alloc
             (fclosure (pair-p2 prog base n s alloc cl rs)) rs kf)
    -- …and `f` RETURNED (plan 0.119 D5; D357: `frame-pres` holds of a run
    -- that returned, so the equation is asked for, not only `NotCut`).
    {vF : ⟦ B ⟧} {rF : ℕ}
    (rfF : resultAt (floc (pair-p2 prog base n s alloc cl rs)) (⟪ evalᴰ f xf ⟫ kf) ≡ returns (done vF rF))
    -- `g`'s, at the state the two mid rows leave. `n1`/`l1` are `f`'s output
    -- frontier and label base; all this module needs of them is `n ≤ n1`,
    -- which the caller supplies as `frontier-mono f f-start l` composed with
    -- `n ≤ f-start`.
    (n1 l1 : ℕ) (n≤n1 : n ≤ n1)
    {xg : ⟦ A ⟧} {kg bg : ℕ}
    (vrG : ValueRealized prog bg n1 l1 g xg
             (floc (pair-m2 prog n (ValueRealized.settle vrF)))
             (falloc (pair-m2 prog n (ValueRealized.settle vrF)))
             (fclosure (pair-m2 prog n (ValueRealized.settle vrF))) rs kg)
    (ncG : NotCut (resultAt (floc (pair-m2 prog n (ValueRealized.settle vrF))) (⟪ evalᴰ g xg ⟫ kg)))
    where

    module VR = ValueRealized

    ncF : NotCut (resultAt (floc (pair-p2 prog base n s alloc cl rs)) (⟪ evalᴰ f xf ⟫ kf))
    ncF = subst NotCut (sym rfF) tt

    backup fst-stash snd-stash pair-stash f-start : ℕ
    backup     = n
    fst-stash  = suc n
    snd-stash  = suc (suc n)
    pair-stash = suc (suc (suc n))
    f-start    = suc (suc (suc (suc n)))

    -- The five segments' boundary states.
    p1 p2 : FlatState
    p1 = pair-p1 prog base n s alloc cl rs
    p2 = pair-p2 prog base n s alloc cl rs

    fsF : FlatState
    fsF = VR.settle vrF

    m1 m2 : FlatState
    m1 = pair-m1 prog n fsF
    m2 = pair-m2 prog n fsF

    gs : FlatState
    gs = VR.settle vrG

    -- The two mid rows: a stack write and a stack read. Neither allocates and
    -- neither is a frame op.
    cf-mid : current-frame (falloc m2) ≡ current-frame (falloc fsF)
    cf-mid =
      trans (exec-abstract-preserves-frame (restore-input backup) (floc m1) (falloc m1))
            (exec-abstract-preserves-frame (store-at-slot fst-stash) (floc fsF) (falloc fsF))

    sf-mid : saved-frames (falloc m2) ≡ saved-frames (falloc fsF)
    sf-mid =
      trans (exec-abstract-preserves-saved (restore-input backup) (floc m1) (falloc m1))
            (exec-abstract-preserves-saved (store-at-slot fst-stash) (floc fsF) (falloc fsF))

    heapref-mid : next-heap-ref (falloc m2) ≡ next-heap-ref (falloc fsF)
    heapref-mid =
      trans (exec-abstract-preserves-heap-ref (restore-input backup) (floc m1) (falloc m1) tt)
            (exec-abstract-preserves-heap-ref (store-at-slot fst-stash) (floc fsF) (falloc fsF) tt)

    ------------------------------------------------------------------
    -- Carrying the caller's window `BeforeFrontier (alloc @ n)` forward,
    -- one segment at a time.
    ------------------------------------------------------------------
    n≤f-start : n ≤ f-start
    n≤f-start =
      ≤-trans (n≤1+n n)
              (≤-trans (n≤1+n (suc n))
                       (≤-trans (n≤1+n (suc (suc n))) (n≤1+n (suc (suc (suc n))))))

    -- … to `f`'s own frontier, which is where `f`'s hypothesis speaks.
    bf-f : ∀ (loc : ValueLocation FS)
         → BeforeFrontier (record alloc { next-slot = n }) loc
         → BeforeFrontier (record alloc { next-slot = f-start }) loc
    bf-f = frontier-monotone (record alloc { next-slot = n })
                             (record alloc { next-slot = f-start })
                             refl n≤f-start ≤-refl

    bf-after-f : ∀ (m : ℕ) (loc : ValueLocation FS)
               → BeforeFrontier (record alloc { next-slot = m }) loc
               → BeforeFrontier (record (falloc fsF) { next-slot = m }) loc
    bf-after-f = VR.bf-mono vrF ncF

    bf-mid : ∀ (m : ℕ) (loc : ValueLocation FS)
           → BeforeFrontier (record (falloc fsF) { next-slot = m }) loc
           → BeforeFrontier (record (falloc m2) { next-slot = m }) loc
    bf-mid m = frontier-monotone (record (falloc fsF) { next-slot = m })
                                 (record (falloc m2) { next-slot = m })
                                 (sym cf-mid) ≤-refl (≤-reflexive (sym heapref-mid))

    bf-after-g : ∀ (m : ℕ) (loc : ValueLocation FS)
               → BeforeFrontier (record (falloc m2) { next-slot = m }) loc
               → BeforeFrontier (record (falloc gs) { next-slot = m }) loc
    bf-after-g = VR.bf-mono vrG ncG

    bf-to-m2 : ∀ (m : ℕ) (loc : ValueLocation FS)
             → BeforeFrontier (record alloc { next-slot = m }) loc
             → BeforeFrontier (record (falloc m2) { next-slot = m }) loc
    bf-to-m2 m loc b = bf-mid m loc (bf-after-f m loc b)

    bf-to-gs : ∀ (m : ℕ) (loc : ValueLocation FS)
             → BeforeFrontier (record alloc { next-slot = m }) loc
             → BeforeFrontier (record (falloc gs) { next-slot = m }) loc
    bf-to-gs m loc b = bf-after-g m loc (bf-to-m2 m loc b)

    ------------------------------------------------------------------
    -- plan 0.97: THE SAME CHAIN, STOPPED SHORT. If `g` ends the program the
    -- nine-row tail never executes, so the preservation argument is needed at
    -- `gs` — and at `fsF`, for the run that stops inside `f`. These are the
    -- SAME legs `mem-pres-pair` spends, named at the two earlier boundaries
    -- rather than re-proved. (`mem-pres-to-fsF` does not mention `vrG`; only
    -- this module's telescope does, which is why the `f`-stopped clause
    -- rebuilds it from the prologue instead of instantiating `PairPres`.)
    ------------------------------------------------------------------
    mem-pres-to-fsF : ∀ (loc : ValueLocation FS)
                    → BeforeFrontier (record alloc { next-slot = n }) loc
                    → SMCore.MemOps.readLoc (floc fsF) loc ≡ SMCore.MemOps.readLoc s loc
    mem-pres-to-fsF loc b =
      trans (vr-mem-pres vrF ncF loc (bf-f loc b))
      (trans (store-slot-preserves-before backup (floc p1)
                (record alloc { next-slot = n }) (falloc p1) loc
                (exec-abstract-preserves-frame mov-to-output s alloc) ≤-refl b)
             (mem-untouched mov-to-output s alloc loc nhw-mov-to-output refl))

    w-g-outer : ∀ (loc : ValueLocation FS)
              → BeforeFrontier (record alloc { next-slot = n }) loc
              → BeforeFrontier (record (falloc m2) { next-slot = n1 }) loc
    w-g-outer loc b =
      frontier-monotone (record (falloc m2) { next-slot = n })
                        (record (falloc m2) { next-slot = n1 })
                        refl n≤n1 ≤-refl
                        loc (bf-to-m2 n loc b)

    mem-pres-to-gs : ∀ (loc : ValueLocation FS)
                   → BeforeFrontier (record alloc { next-slot = n }) loc
                   → SMCore.MemOps.readLoc (floc gs) loc ≡ SMCore.MemOps.readLoc s loc
    mem-pres-to-gs loc b =
      trans (vr-mem-pres vrG ncG loc (w-g-outer loc b))
      (trans (mem-untouched (restore-input backup) (floc m1) (falloc m1) loc
                Once.CCC.Machine.SMPrimitives.nhw-restore-input refl)
      (trans (store-slot-preserves-before fst-stash (floc fsF)
                (record alloc { next-slot = n }) (falloc fsF) loc
                (VR.frame-pres vrF rfF) (n≤1+n n) b)
             (mem-pres-to-fsF loc b)))

    frame-pres-to-gs : ∀ {vG rG} → resultAt (floc (pair-m2 prog n (ValueRealized.settle vrF))) (⟪ evalᴰ g xg ⟫ kg) ≡ returns (done vG rG)
                     → current-frame (falloc gs) ≡ current-frame alloc
    frame-pres-to-gs rgG =
      trans (VR.frame-pres vrG rgG) (trans cf-mid (VR.frame-pres vrF rfF))

    ------------------------------------------------------------------
    -- THE WHOLE PAIR: the four segments above, then the tail (`Pair.Build`),
    -- which leaves the slots below `snd-stash` and the heap before its fresh
    -- block alone, keeps the frame and only grows the frontier.
    ------------------------------------------------------------------
    module WithTail
      (settleT : FlatState)
      (cf-t : current-frame (falloc settleT) ≡ current-frame (falloc gs))
      (sf-t : saved-frames (falloc settleT) ≡ saved-frames (falloc gs))
      (bf-t : ∀ (m : ℕ) (loc : ValueLocation FS)
            → BeforeFrontier (record (falloc gs) { next-slot = m }) loc
            → BeforeFrontier (record (falloc settleT) { next-slot = m }) loc)
      (mem-t : ∀ (loc : ValueLocation FS)
             → BeforeFrontier (record (falloc gs) { next-slot = snd-stash }) loc
             → SMCore.MemOps.readLoc (floc settleT) loc ≡ SMCore.MemOps.readLoc (floc gs) loc)
      where

      frame-pres-pair : ∀ {vG rG} → resultAt (floc (pair-m2 prog n (ValueRealized.settle vrF))) (⟪ evalᴰ g xg ⟫ kg) ≡ returns (done vG rG)
                      → current-frame (falloc settleT) ≡ current-frame alloc
      frame-pres-pair rgG = trans cf-t (frame-pres-to-gs rgG)

      frames-pres-pair : ∀ {vG rG} → resultAt (floc (pair-m2 prog n (ValueRealized.settle vrF))) (⟪ evalᴰ g xg ⟫ kg) ≡ returns (done vG rG)
                       → saved-frames (falloc settleT) ≡ saved-frames alloc
      frames-pres-pair rgG =
        trans sf-t (trans (VR.frames-pres vrG rgG) (trans sf-mid (VR.frames-pres vrF rfF)))

      bf-mono-pair : ∀ (m : ℕ) (loc : ValueLocation FS)
                   → BeforeFrontier (record alloc { next-slot = m }) loc
                   → BeforeFrontier (record (falloc settleT) { next-slot = m }) loc
      bf-mono-pair m loc b = bf-t m loc (bf-to-gs m loc b)

      w-gs : ∀ (loc : ValueLocation FS)
           → BeforeFrontier (record alloc { next-slot = n }) loc
           → BeforeFrontier (record (falloc gs) { next-slot = snd-stash }) loc
      w-gs loc b =
        frontier-monotone (record (falloc gs) { next-slot = n })
                          (record (falloc gs) { next-slot = snd-stash })
                          refl (≤-trans (n≤1+n n) (n≤1+n (suc n))) ≤-refl
                          loc (bf-to-gs n loc b)

      mem-pres-pair : ∀ (loc : ValueLocation FS)
                    → BeforeFrontier (record alloc { next-slot = n }) loc
                    → SMCore.MemOps.readLoc (floc settleT) loc ≡ SMCore.MemOps.readLoc s loc
      mem-pres-pair loc b = trans (mem-t loc (w-gs loc b)) (mem-pres-to-gs loc b)

      stack-pres-pair : ∀ (fr : FrameSemantics.Frame FS) (j : ℕ)
                      → BeforeFrontier (record alloc { next-slot = n }) (AtStack fr j)
                      → SMCore.MemOps.readLoc (floc settleT) (AtStack fr j)
                        ≡ SMCore.MemOps.readLoc s (AtStack fr j)
      stack-pres-pair fr j = mem-pres-pair (AtStack fr j)

      heap-pres-pair : ∀ (hl : HeapLocation)
                     → BeforeFrontier (record alloc { next-slot = n }) (AtDynamic hl)
                     → SMCore.MemOps.readLoc (floc settleT) (AtDynamic hl)
                       ≡ SMCore.MemOps.readLoc s (AtDynamic hl)
      heap-pres-pair hl = mem-pres-pair (AtDynamic hl)

  module PairTrace where
    open import Data.List.Properties using (++-identityʳ)

    pair-chain-events :
      ∀ {prog : AbstractTrace} {kP kF kM kG kT : ℕ}
        {e0 s1 s2 s3 s4 : FlatState}
        (preS  : FlatSteps prog kP e0 s1)
        (cF    : FlatSteps prog kF s1 s2)
        (midS  : FlatSteps prog kM s2 s3)
        (cG    : FlatSteps prog kG s3 s4)
        {s5 : FlatState}
        (tailS : FlatSteps prog kT s4 s5)
      → chain-events preS  ≡ []
      → chain-events midS  ≡ []
      → chain-events tailS ≡ []
      → chain-events (FlatSteps-++ preS (FlatSteps-++ cF (FlatSteps-++ midS (FlatSteps-++ cG tailS))))
        ≡ chain-events cF ++ chain-events cG
    pair-chain-events preS cF midS cG tailS pre[] mid[] tail[] =
      trans (chain-events-++ preS after-pre)
            (trans (cong (_++ chain-events after-pre) pre[]) ev-after-pre)
      where
        after-g = FlatSteps-++ cG tailS

        ev-after-g : chain-events after-g ≡ chain-events cG
        ev-after-g =
          trans (chain-events-++ cG tailS)
                (trans (cong (chain-events cG ++_) tail[])
                       (++-identityʳ (chain-events cG)))

        after-f = FlatSteps-++ midS after-g

        ev-after-f : chain-events after-f ≡ chain-events cG
        ev-after-f =
          trans (chain-events-++ midS after-g)
                (trans (cong (_++ chain-events after-g) mid[]) ev-after-g)

        after-pre = FlatSteps-++ cF after-f

        ev-after-pre : chain-events after-pre ≡ chain-events cF ++ chain-events cG
        ev-after-pre =
          trans (chain-events-++ cF after-f)
                (cong (chain-events cF ++_) ev-after-f)

    -- The two shorter runs: `g` stopped (no tail), `f` stopped (no mid, no `g`).
    pair-chain-events-g :
      ∀ {prog : AbstractTrace} {kP kF kM kG : ℕ} {e0 s1 s2 s3 s4 : FlatState}
        (preS : FlatSteps prog kP e0 s1) (cF : FlatSteps prog kF s1 s2)
        (midS : FlatSteps prog kM s2 s3) (cG : FlatSteps prog kG s3 s4)
      → chain-events preS ≡ [] → chain-events midS ≡ []
      → chain-events (FlatSteps-++ preS (FlatSteps-++ cF (FlatSteps-++ midS cG)))
        ≡ chain-events cF ++ chain-events cG
    pair-chain-events-g preS cF midS cG pre[] mid[] =
      trans (chain-events-++ preS (FlatSteps-++ cF (FlatSteps-++ midS cG)))
      (trans (cong (_++ chain-events (FlatSteps-++ cF (FlatSteps-++ midS cG))) pre[])
      (trans (chain-events-++ cF (FlatSteps-++ midS cG))
             (cong (chain-events cF ++_)
                   (trans (chain-events-++ midS cG) (cong (_++ chain-events cG) mid[])))))

    pair-chain-events-f :
      ∀ {prog : AbstractTrace} {kP kF : ℕ} {e0 s1 s2 : FlatState}
        (preS : FlatSteps prog kP e0 s1) (cF : FlatSteps prog kF s1 s2)
      → chain-events preS ≡ []
      → chain-events (FlatSteps-++ preS cF) ≡ chain-events cF
    pair-chain-events-f preS cF pre[] =
      trans (chain-events-++ preS cF) (cong (_++ chain-events cF) pre[])

