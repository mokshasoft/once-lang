-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Call
--
-- D245: a DIRECT CALL of one of the program's functions, `Call f`, lowered to
-- the single instruction `c-call-fn f`. It is `apply`'s argument with the
-- setup gone: `apply` has to build the `(env , arg)` pair and read the code
-- cell before it can call, while a direct call names its callee statically and
-- passes its argument where it already is, in the input register. So the run is ONE step, the call, followed by the callee's
-- run, which `BlockRuns.functions` supplies for every linked call. The
-- denotation needs no transport either: `evalᴰ (Call f) x` IS the table
-- environment's `f` at `B`, definitionally.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)
import Once.CCC.Machine.SMCore as SMCore

import Data.List as DL
open import Once.Denotation.Program using (IRFun; LinkedAt)
module Once.CCC.Codegen.IRObsCorrect.Call (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (AtStack; AtDynamic; ValueLocation)

import Once.CCC.FrameSemantics
open import Once.CCC.Machine.SMCore using (instr-ctrl; c-call-fn; module LocState)
open LocState using (halted)
import Once.IRTy
import Once.IR
open import Once.Internal.Res using (is-stopped)
open import Once.Denotation.Approx using (NotCut; budgetLeft)
open import Data.Nat.Properties using (+-monoʳ-≤)
open import Once.Denotation.Program using (tableCalls)
import Once.Denotation.DenotTrace as DT
import Once.Internal.Trace as TM

module CallC {FS : FrameSemantics} where

  open Core {FS}

  obs-correct-call : ∀ {A B} (f : CanonicalName) → LinkedAt tbl f A B → IRObsCorrectF (Once.IR.Call {A} {B} f)
  obs-correct-call {A} {B} f lk n l prog base _ cr span _ _ mIn x s alloc cl n≤ nh inp k rs = record
    { value-realized =
        realized (1 + CalleeRun.steps crun) (CalleeRun.settle crun)
                 (CalleeRun.out-mode crun) (CalleeRun.cont-alloc crun)
                 run (λ p → CalleeRun.live crun (trans st-eq p))
                 (λ p → CalleeRun.returned crun (trans res-eq p))
                 (λ p → proj₁ (CalleeRun.stops crun (trans st-eq p))
                      , trans (proj₂ (CalleeRun.stops crun (trans st-eq p))) (cong (λ st → LocState.left (floc st)) call-eq))
                 (λ p → CalleeRun.no-ret crun (trans res-eq p)) (λ nc → CalleeRun.no-link crun (nc′ nc))
                 (trans (CalleeRun.log crun) (cong₂ DL._++_ h-eq (cong proj₁ RE)))
                 (λ p → CalleeRun.place crun (trans res-eq p))
                 (progress-≤ (subst (λ r → k ≤ budgetLeft k r + chain-ctrls (CalleeRun.run crun)) res-eq (CalleeRun.progress crun))
                             (ctrls-≤ʳ run1 (CalleeRun.run crun)))
                 (λ nc fr i bf → mem-pres nc (AtStack fr i) bf) (λ nc hl bf → mem-pres nc (AtDynamic hl) bf)
                 (λ p → CalleeRun.frame-pres crun (trans res-eq p) alloc (cong falloc call-eq))
                 (λ nc m loc bf → CalleeRun.bf-mono crun (nc′ nc) alloc m (cong falloc call-eq) loc bf)
                 (λ p → CalleeRun.frames-pres crun (trans res-eq p) alloc (cong falloc call-eq))
    ; traces-agree = trc
    }
    where
      e0 = entry-flat base s alloc cl rs

      finfo  = BlockRuns.functions cr f A B lk
      j      = proj₁ finfo
      feq    = proj₁ (proj₂ finfo)
      runner = proj₂ (proj₂ finfo)

      -- THE CALL: the statically named entry, resolved by the table scan.
      call-eq : flat-exec-instr (instr-ctrl (c-call-fn f)) prog e0
              ≡ record e0 { falloc = enter-call alloc
                          ; fret   = suc base ∷ rs
                          ; flink  = just (suc base)
                          ; fpc    = j }
      call-eq = cong (λ z → do-call-at z e0) feq

      post = flat-exec-instr (instr-ctrl (c-call-fn f)) prog e0

      crun : CalleeRun prog post (suc base) rs B (tableCalls (Once.CCC.FrameSemantics.fs-numerics FS) (TM.pureHalf ιᶠ) tbl f A B x) k
      -- the argument stays where the caller left it: the call writes no memory.
      crun = runner post alloc x (suc base) k rs mIn
               (cong fpc call-eq)
               (trans (cong (λ st → halted (floc st)) call-eq) nh)
               (cong fret call-eq)
               (cong falloc call-eq) n≤
               (subst (λ st → InputAt {prog = prog} {A} mIn alloc x (floc st)) (sym call-eq) inp)

      run1 : FlatSteps prog 1 e0 post
      run1 = (nh , span 0 _ refl) ∷ []

      run : FlatSteps prog (1 + CalleeRun.steps crun) e0 (CalleeRun.settle crun)
      run = FlatSteps-++ run1 (CalleeRun.run crun)

      -- plan 0.105: the call writes nothing but control, so the callee runs
      -- from the caller's log.
      h-eq : SMCore.LocState.ev-log (floc post) ≡ SMCore.LocState.ev-log s
      h-eq = cong (λ st → SMCore.LocState.ev-log (floc st)) call-eq

      RE : runAt (floc post) (⟪ tableCalls (Once.CCC.FrameSemantics.fs-numerics FS) (TM.pureHalf ιᶠ) tbl f A B x ⟫ k)
         ≡ runAt s (⟪ evalᴰ (Once.IR.Call {A} {B} f) x ⟫ k)
      RE = runAt-≡ {st = floc post} {st′ = s}
             {m = ⟪ tableCalls (Once.CCC.FrameSemantics.fs-numerics FS) (TM.pureHalf ιᶠ) tbl f A B x ⟫ k}
             {m′ = ⟪ evalᴰ (Once.IR.Call {A} {B} f) x ⟫ k} h-eq refl

      st-eq : stopsAt (floc post) (⟪ tableCalls (Once.CCC.FrameSemantics.fs-numerics FS) (TM.pureHalf ιᶠ) tbl f A B x ⟫ k)
            ≡ stopsAt s (⟪ evalᴰ (Once.IR.Call {A} {B} f) x ⟫ k)
      st-eq = cong (λ r → is-stopped (proj₂ r)) RE

      res-eq : resultAt (floc post) (⟪ tableCalls (Once.CCC.FrameSemantics.fs-numerics FS) (TM.pureHalf ιᶠ) tbl f A B x ⟫ k)
             ≡ resultAt s (⟪ evalᴰ (Once.IR.Call {A} {B} f) x ⟫ k)
      res-eq = cong proj₂ RE

      nc′ : NotCut (resultAt s (⟪ evalᴰ (Once.IR.Call {A} {B} f) x ⟫ k))
          → NotCut (resultAt (floc post) (⟪ tableCalls (Once.CCC.FrameSemantics.fs-numerics FS) (TM.pureHalf ιᶠ) tbl f A B x ⟫ k))
      nc′ = subst NotCut (sym res-eq)

      trc : chain-events run ≡ eventsAt s (⟪ evalᴰ (Once.IR.Call {A} {B} f) x ⟫ k)
      trc = trans (chain-events-++ run1 (CalleeRun.run crun))
                  (trans (CalleeRun.events crun) (cong proj₁ RE))

      -- The callee preserves the caller's frame at any bound, and the call
      -- itself writes no memory.
      mem-pres : NotCut (resultAt s (⟪ evalᴰ (Once.IR.Call {A} {B} f) x ⟫ k))
               → ∀ (loc : ValueLocation FS)
               → BeforeFrontier (record alloc { next-slot = n }) loc
               → SMCore.MemOps.readLoc (floc (CalleeRun.settle crun)) loc ≡ SMCore.MemOps.readLoc s loc
      mem-pres nc loc bf =
        trans (CalleeRun.mem-pres crun (nc′ nc) alloc n (cong falloc call-eq) loc bf)
              (cong (λ st → SMCore.MemOps.readLoc (floc st) loc) call-eq)
