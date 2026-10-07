-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres
--
-- D207: what the pair's run LEAVES ALONE, and the five-segment event splice.
-- Split from `Pair` for the per-module check cap.
------------------------------------------------------------------------


open import Once.CanonicalName using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.Pair.Pres (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.LabelResolve o using (module Resolve)
open import Once.CCC.Codegen.LabelScope o using ()
open import Data.Nat.Solver using (module +-*-Solver)

import Once.CCC.FrameSemantics
import Once.CCC.Machine.SMPrimitives
import Once.IRTy
import Once.IR
import Once.Semantics.Machine as EvV
import Once.CCC.Machine.ReadTypedAdequate as RTA
import Once.Denotation.DenotTrace as DT
import Once.Denotation.TraceMonad as TM

module PairPresC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open FlatStepsAPI {FS} using ()
  open Resolve {FS} using ()

  -- The prologue and the mid rows as TOP-LEVEL functions, so that `PairPres`'s
  -- own TELESCOPE can name the states its two induction hypotheses run from
  -- (a module parameter cannot mention a definition from the module's body).
  pair-p1 pair-p2 : AbstractTrace → ℕ → ℕ → LocState FS → AllocState {FS}
                  → StoredValue FS → FlatState
  pair-p1 prog base n s alloc cl =
    flat-exec-instr mov-to-output prog (entry-flat base s alloc cl)
  pair-p2 prog base n s alloc cl =
    flat-exec-instr (store-at-slot n) prog (pair-p1 prog base n s alloc cl)

  pair-m1 pair-m2 : AbstractTrace → ℕ → FlatState → FlatState
  pair-m1 prog n fsF = flat-exec-instr (store-at-slot (suc n)) prog fsF
  pair-m2 prog n fsF = flat-exec-instr (restore-input n) prog (pair-m1 prog n fsF)

  module PairPres
    {A B C : IRTy} (f : IR A B) (g : IR A C)
    (n l : ℕ) (prog : AbstractTrace) (base : ℕ)
    (s : LocState FS) (alloc : AllocState {FS}) (cl : StoredValue FS)
    -- `f`'s induction hypothesis, at the state the two prologue rows leave.
    -- Its placement `bf₀` is free: preservation does not care where the
    -- fragment sits, only what frontier it was emitted at (`f-start`).
    {xf : ⟦ A ⟧} {kf bf₀ : ℕ}
    (vrF : ValueRealized prog bf₀ (suc (suc (suc (suc n)))) l f xf
             (floc (pair-p2 prog base n s alloc cl)) alloc
             (fclosure (pair-p2 prog base n s alloc cl)) kf)
    -- `g`'s, at the state the two mid rows leave. `n1`/`l1` are `f`'s output
    -- frontier and label base; all this module needs of them is `n ≤ n1`,
    -- which the caller supplies as `frontier-mono f f-start l` composed with
    -- `n ≤ f-start`.
    (n1 l1 : ℕ) (n≤n1 : n ≤ n1)
    {xg : ⟦ A ⟧} {kg bg : ℕ}
    (vrG : ValueRealized prog bg n1 l1 g xg
             (floc (pair-m2 prog n (ValueRealized.settle vrF)))
             (falloc (pair-m2 prog n (ValueRealized.settle vrF)))
             (fclosure (pair-m2 prog n (ValueRealized.settle vrF))) kg)
    where

    module VR = ValueRealized

    backup fst-stash snd-stash pair-stash f-start : ℕ
    backup     = n
    fst-stash  = suc n
    snd-stash  = suc (suc n)
    pair-stash = suc (suc (suc n))
    f-start    = suc (suc (suc (suc n)))

    -- The five segments' boundary states.
    p1 p2 : FlatState
    p1 = pair-p1 prog base n s alloc cl
    p2 = pair-p2 prog base n s alloc cl

    fsF : FlatState
    fsF = VR.settle vrF

    m1 m2 : FlatState
    m1 = pair-m1 prog n fsF
    m2 = pair-m2 prog n fsF

    gs : FlatState
    gs = VR.settle vrG

    -- The nine-instruction heap build, measured against `g`'s OWN allocator
    -- (see the header note): both of `NineStepPres`'s premises are then `refl`.
    tail-alloc : AllocState {FS}
    tail-alloc = record (falloc gs) { next-slot = snd-stash }

    -- the literal arguments `WithG` names the tail at (see there)
    module NSP = NineStepPres (suc (suc n))
                   (load-from-slot (suc n))        -- i6: the fst component
                   (load-from-slot (suc (suc n)))  -- i8: the snd component
                   (VR.settle vrG) (floc gs) tail-alloc refl refl

    settle : FlatState
    settle = NSP.u10

    pair-hl : HeapLocation
    pair-hl = NSP.hl

    ------------------------------------------------------------------
    -- The two allocator chains the frame/frontier arguments need. Neither
    -- reduces: `falloc NSP.u10` is a nest of nine `exec-abstract`s and the
    -- `with`-blocks inside the loads and the indirect stores block it.
    ------------------------------------------------------------------
    -- `abstract` (profile 2026-09-29): consumers need only the TYPE; unfolding
    -- the body at every use (through `PairAssemble`'s application of this
    -- module) re-derived the nine-step state and cost gigabytes.
    abstract
      cf-tail : current-frame (falloc NSP.u10) ≡ current-frame (falloc gs)
      cf-tail =
        trans (exec-abstract-preserves-frame (load-from-slot pair-stash) (floc NSP.u9) (falloc NSP.u9))
       (trans (exec-abstract-preserves-frame store-indirect-suc (floc NSP.u8) (falloc NSP.u8))
       (trans (exec-abstract-preserves-frame (load-from-slot snd-stash) (floc NSP.u7) (falloc NSP.u7))
       (trans (exec-abstract-preserves-frame store-indirect (floc NSP.u6) (falloc NSP.u6))
       (trans (exec-abstract-preserves-frame (load-from-slot fst-stash) (floc NSP.u5) (falloc NSP.u5))
       (trans (exec-abstract-preserves-frame mov-to-input (floc NSP.u4) (falloc NSP.u4))
       (trans (exec-abstract-preserves-frame (store-at-slot pair-stash) (floc NSP.u3) (falloc NSP.u3))
       (trans (exec-abstract-preserves-frame (instr-alloc-heap 2) (floc NSP.u2) (falloc NSP.u2))
              (exec-abstract-preserves-frame (store-at-slot snd-stash) (floc gs) (falloc gs)))))))))

    -- Rows 4-10 do not allocate, so the heap frontier they leave is the one
    -- `instr-alloc-heap 2` set at row 3 — one above `u2`'s.
    -- `abstract` (profile 2026-09-29): consumers need only the TYPE; unfolding
    -- the body at every use (through `PairAssemble`'s application of this
    -- module) re-derived the nine-step state and cost gigabytes.
    abstract
      heapref-tail : next-heap-ref (falloc NSP.u10) ≡ suc (next-heap-ref (falloc NSP.u2))
      heapref-tail =
        trans (exec-abstract-preserves-heap-ref (load-from-slot pair-stash) (floc NSP.u9) (falloc NSP.u9) tt)
       (trans (exec-abstract-preserves-heap-ref store-indirect-suc (floc NSP.u8) (falloc NSP.u8) tt)
       (trans (exec-abstract-preserves-heap-ref (load-from-slot snd-stash) (floc NSP.u7) (falloc NSP.u7) tt)
       (trans (exec-abstract-preserves-heap-ref store-indirect (floc NSP.u6) (falloc NSP.u6) tt)
       (trans (exec-abstract-preserves-heap-ref (load-from-slot fst-stash) (floc NSP.u5) (falloc NSP.u5) tt)
       (trans (exec-abstract-preserves-heap-ref mov-to-input (floc NSP.u4) (falloc NSP.u4) tt)
              (exec-abstract-preserves-heap-ref (store-at-slot pair-stash) (floc NSP.u3) (falloc NSP.u3) tt))))))

    heapref-gs≤ : next-heap-ref (falloc gs) ≤ next-heap-ref (falloc NSP.u10)
    heapref-gs≤ =
      ≤-trans (≤-reflexive (sym NSP.heapref-u2))
              (≤-trans (n≤1+n (next-heap-ref (falloc NSP.u2)))
                       (≤-reflexive (sym heapref-tail)))

    -- The two mid rows: a stack write and a stack read. Neither allocates and
    -- neither is a frame op.
    cf-mid : current-frame (falloc m2) ≡ current-frame (falloc fsF)
    cf-mid =
      trans (exec-abstract-preserves-frame (restore-input backup) (floc m1) (falloc m1))
            (exec-abstract-preserves-frame (store-at-slot fst-stash) (floc fsF) (falloc fsF))

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
    bf-after-f = VR.bf-mono vrF

    bf-mid : ∀ (m : ℕ) (loc : ValueLocation FS)
           → BeforeFrontier (record (falloc fsF) { next-slot = m }) loc
           → BeforeFrontier (record (falloc m2) { next-slot = m }) loc
    bf-mid m = frontier-monotone (record (falloc fsF) { next-slot = m })
                                 (record (falloc m2) { next-slot = m })
                                 (sym cf-mid) ≤-refl (≤-reflexive (sym heapref-mid))

    bf-after-g : ∀ (m : ℕ) (loc : ValueLocation FS)
               → BeforeFrontier (record (falloc m2) { next-slot = m }) loc
               → BeforeFrontier (record (falloc gs) { next-slot = m }) loc
    bf-after-g = VR.bf-mono vrG

    bf-to-m2 : ∀ (m : ℕ) (loc : ValueLocation FS)
             → BeforeFrontier (record alloc { next-slot = m }) loc
             → BeforeFrontier (record (falloc m2) { next-slot = m }) loc
    bf-to-m2 m loc b = bf-mid m loc (bf-after-f m loc b)

    bf-to-gs : ∀ (m : ℕ) (loc : ValueLocation FS)
             → BeforeFrontier (record alloc { next-slot = m }) loc
             → BeforeFrontier (record (falloc gs) { next-slot = m }) loc
    bf-to-gs m loc b = bf-after-g m loc (bf-to-m2 m loc b)

    -- `abstract` (profile 2026-09-29): consumers need only the TYPE; unfolding
    -- the body at every use (through `PairAssemble`'s application of this
    -- module) re-derived the nine-step state and cost gigabytes.
    abstract
      bf-tail : ∀ (m : ℕ) (loc : ValueLocation FS)
              → BeforeFrontier (record (falloc gs) { next-slot = m }) loc
              → BeforeFrontier (record (falloc NSP.u10) { next-slot = m }) loc
      bf-tail m = frontier-monotone (record (falloc gs) { next-slot = m })
                                    (record (falloc NSP.u10) { next-slot = m })
                                    (sym cf-tail) ≤-refl heapref-gs≤

    ------------------------------------------------------------------
    -- D210: FRAMEPRES. The frame does not move: nine rows of it in the tail,
    -- `g`'s own `frame-pres`, two rows in the mid, `f`'s own `frame-pres`.
    -- (The prologue's two rows are already inside `f`'s hypothesis, whose
    -- `alloc` index IS the caller's — `falloc p2` reduces to `alloc`.)
    ------------------------------------------------------------------
    frame-pres-pair : current-frame (falloc NSP.u10) ≡ current-frame alloc
    frame-pres-pair =
      trans cf-tail (trans (VR.frame-pres vrG) (trans cf-mid (VR.frame-pres vrF)))

    ------------------------------------------------------------------
    -- D206: BFMONO, at an ARBITRARY slot bound `m` — which is exactly why
    -- each hypothesis' own `bf-mono` is stated that way: they chain.
    ------------------------------------------------------------------
    bf-mono-pair : ∀ (m : ℕ) (loc : ValueLocation FS)
                 → BeforeFrontier (record alloc { next-slot = m }) loc
                 → BeforeFrontier (record (falloc NSP.u10) { next-slot = m }) loc
    bf-mono-pair m loc b = bf-tail m loc (bf-to-gs m loc b)

    ------------------------------------------------------------------
    -- D208: STACKPRES / HEAPPRES. The two halves of ONE five-segment `trans`
    -- chain, so they are derived from it rather than proved twice.
    --
    -- The two freshness read-backs `rdi6`/`rdi8` are the only thing the
    -- memory argument needs that this cluster does not prove: they say the
    -- pointer the two indirect stores write through IS the block row 3
    -- allocated. They are register facts about `NSP.u6`/`NSP.u8` and belong
    -- with the `place` cluster, so they enter here as parameters.
    ------------------------------------------------------------------
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
                    → MemOps.readLoc (floc fsF) loc ≡ MemOps.readLoc s loc
    mem-pres-to-fsF loc b =
      trans (vr-mem-pres vrF loc (bf-f loc b))
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
                   → MemOps.readLoc (floc gs) loc ≡ MemOps.readLoc s loc
    mem-pres-to-gs loc b =
      trans (vr-mem-pres vrG loc (w-g-outer loc b))
      (trans (mem-untouched (restore-input backup) (floc m1) (falloc m1) loc
                Once.CCC.Machine.SMPrimitives.nhw-restore-input refl)
      (trans (store-slot-preserves-before fst-stash (floc fsF)
                (record alloc { next-slot = n }) (falloc fsF) loc
                (VR.frame-pres vrF) (n≤1+n n) b)
             (mem-pres-to-fsF loc b)))

    frame-pres-to-gs : current-frame (falloc gs) ≡ current-frame alloc
    frame-pres-to-gs =
      trans (VR.frame-pres vrG) (trans cf-mid (VR.frame-pres vrF))

    module Fill
      (rdi6 : sv-as-loc (readReg (regs (floc NSP.u6)) Input1) ≡ just (AtDynamic NSP.hl))
      (rdi8 : sv-as-loc (readReg (regs (floc NSP.u8)) Input1) ≡ just (AtDynamic NSP.hl))
      where

      -- the window, at the two allocators the two sub-arguments speak of
      w-gs : ∀ (loc : ValueLocation FS)
           → BeforeFrontier (record alloc { next-slot = n }) loc
           → BeforeFrontier (record (falloc gs) { next-slot = snd-stash }) loc
      w-gs loc b =
        frontier-monotone (record (falloc gs) { next-slot = n })
                          (record (falloc gs) { next-slot = snd-stash })
                          refl (≤-trans (n≤1+n n) (n≤1+n (suc n))) ≤-refl
                          loc (bf-to-gs n loc b)

      w-g : ∀ (loc : ValueLocation FS)
          → BeforeFrontier (record alloc { next-slot = n }) loc
          → BeforeFrontier (record (falloc m2) { next-slot = n1 }) loc
      w-g loc b =
        frontier-monotone (record (falloc m2) { next-slot = n })
                          (record (falloc m2) { next-slot = n1 })
                          refl n≤n1 ≤-refl
                          loc (bf-to-m2 n loc b)

      mem-pres-pair : ∀ (loc : ValueLocation FS)
                    → BeforeFrontier (record alloc { next-slot = n }) loc
                    → MemOps.readLoc (floc NSP.u10) loc ≡ MemOps.readLoc s loc
      mem-pres-pair loc b =
        -- (5) the nine-instruction tail: two stack writes at `snd-stash` and
        --     `pair-stash`, two heap writes into the block it just allocated.
        trans (NSP.mem-pres-from
                 nhw-load-from-slot refl nhw-load-from-slot refl
                 ≤-refl rdi6 rdi8 loc (w-gs loc b))
        -- (4) `g`'s run, at `g`'s own emission frontier `n1`
       (trans (vr-mem-pres vrG loc (w-g loc b))
        -- (3b) `restore-input backup` — a register write; no memory at all
       (trans (mem-untouched (restore-input backup) (floc m1) (falloc m1) loc
                 Once.CCC.Machine.SMPrimitives.nhw-restore-input refl)
        -- (3a) `store-at-slot fst-stash` — slot `suc n`, ABOVE the window
       (trans (store-slot-preserves-before fst-stash (floc fsF)
                 (record alloc { next-slot = n }) (falloc fsF) loc
                 (VR.frame-pres vrF) (n≤1+n n) b)
        -- (2) `f`'s run, at `f`'s own emission frontier `f-start = n + 4`
       (trans (vr-mem-pres vrF loc (bf-f loc b))
        -- (1b) `store-at-slot backup` — slot `n`, the window's own bound
       (trans (store-slot-preserves-before backup (floc p1)
                 (record alloc { next-slot = n }) (falloc p1) loc
                 (exec-abstract-preserves-frame mov-to-output s alloc) ≤-refl b)
        -- (1a) `mov-to-output` — a register write
              (mem-untouched mov-to-output s alloc loc nhw-mov-to-output refl))))))

      stack-pres-pair : ∀ (fr : FrameSemantics.Frame FS) (j : ℕ)
                      → BeforeFrontier (record alloc { next-slot = n }) (AtStack fr j)
                      → MemOps.readLoc (floc NSP.u10) (AtStack fr j)
                        ≡ MemOps.readLoc s (AtStack fr j)
      stack-pres-pair fr j = mem-pres-pair (AtStack fr j)

      heap-pres-pair : ∀ (hl : HeapLocation)
                     → BeforeFrontier (record alloc { next-slot = n }) (AtDynamic hl)
                     → MemOps.readLoc (floc NSP.u10) (AtDynamic hl)
                       ≡ MemOps.readLoc s (AtDynamic hl)
      heap-pres-pair hl = mem-pres-pair (AtDynamic hl)

  ----------------------------------------------------------------------
  -- THE TRACE HALF's machine side: the five-segment SPLICE.
  --
  -- The emitted trace is `pre ++ ft ++ mid ++ gt ++ tail`, and every row
  -- outside the two sub-IR fragments is a register/memory op, emitting
  -- nothing — so the pair's events are `f`'s followed by `g`'s. (Plan 0.105:
  -- the denotation's side is the run of the two binds, `PairAssemble`; the
  -- budget arithmetic that used to live here is gone with the budget.)
  ----------------------------------------------------------------------
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

