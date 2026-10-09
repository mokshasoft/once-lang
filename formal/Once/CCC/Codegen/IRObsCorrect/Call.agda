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

open import Once.CanonicalName using (CanonicalName)
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
open import Once.Res using (is-stopped)
open import Once.Denotation.Program using (tableCalls)
import Once.Denotation.DenotTrace as DT
import Once.Denotation.TraceMonad as TM

module CallC {FS : FrameSemantics} where

  open Core {FS}

  obs-correct-call : ∀ {A B} (f : CanonicalName) → LinkedAt tbl f A B → IRObsCorrectF (Once.IR.Call {A} {B} f)
  obs-correct-call {A} {B} f lk n l prog base _ cr span _ _ mIn x s alloc cl n≤ nh inp k = record
    { value-realized =
        realized (1 + CalleeRun.steps crun) (CalleeRun.settle crun)
                 (CalleeRun.out-mode crun) (CalleeRun.cont-alloc crun)
                 run (λ p → CalleeRun.live crun (trans st-eq p))
                 (λ p → CalleeRun.returned crun (trans st-eq p))
                 (λ p → CalleeRun.stops crun (trans st-eq p))
                 (CalleeRun.no-ret crun) (CalleeRun.no-link crun)
                 (trans (CalleeRun.log crun) (cong₂ DL._++_ h-eq (cong proj₁ RE)))
                 (λ p → CalleeRun.place crun (trans (cong proj₂ RE) p))
                 (λ fr i bf → mem-pres (AtStack fr i) bf) (λ hl bf → mem-pres (AtDynamic hl) bf)
                 (CalleeRun.frame-pres crun alloc (cong falloc call-eq))
                 (λ m loc bf → CalleeRun.bf-mono crun alloc m (cong falloc call-eq) loc bf)
    ; traces-agree = trc
    }
    where
      e0 = entry-flat base s alloc cl

      finfo  = BlockRuns.functions cr f A B lk
      j      = proj₁ finfo
      feq    = proj₁ (proj₂ finfo)
      runner = proj₂ (proj₂ finfo)

      -- THE CALL: the statically named entry, resolved by the table scan.
      call-eq : flat-exec-instr (instr-ctrl (c-call-fn f)) prog e0
              ≡ record e0 { falloc = enter-call alloc
                          ; fret   = suc base ∷ []
                          ; flink  = just (suc base)
                          ; fpc    = j }
      call-eq = cong (λ z → do-call-at z e0) feq

      post = flat-exec-instr (instr-ctrl (c-call-fn f)) prog e0

      crun : CalleeRun prog post (suc base) B (tableCalls (Once.CCC.FrameSemantics.fs-numerics FS) (TM.pureHalf ιᶠ) tbl f A B x) k
      -- the argument stays where the caller left it: the call writes no memory.
      crun = runner post alloc x (suc base) k mIn
               (cong fpc call-eq)
               (trans (cong (λ st → halted (floc st)) call-eq) nh)
               (cong fret call-eq)
               (cong falloc call-eq)
               (subst (λ st → InputAt {A} mIn alloc x (floc st)) (sym call-eq) inp)

      run1 : FlatSteps prog 1 e0 post
      run1 = (nh , span 0 _ refl) ∷ []

      run : FlatSteps prog (1 + CalleeRun.steps crun) e0 (CalleeRun.settle crun)
      run = FlatSteps-++ run1 (CalleeRun.run crun)

      -- The callee preserves the caller's frame at any bound, and the call
      -- itself writes no memory.
      mem-pres : ∀ (loc : ValueLocation FS)
               → BeforeFrontier (record alloc { next-slot = n }) loc
               → SMCore.MemOps.readLoc (floc (CalleeRun.settle crun)) loc ≡ SMCore.MemOps.readLoc s loc
      mem-pres loc bf =
        trans (CalleeRun.mem-pres crun alloc n (cong falloc call-eq) loc bf)
              (cong (λ st → SMCore.MemOps.readLoc (floc st) loc) call-eq)

      -- plan 0.105: the call writes nothing but control, so the callee runs
      -- from the caller's log.
      h-eq : SMCore.LocState.ev-log (floc post) ≡ SMCore.LocState.ev-log s
      h-eq = cong (λ st → SMCore.LocState.ev-log (floc st)) call-eq

      RE : runAt (floc post) (tableCalls (Once.CCC.FrameSemantics.fs-numerics FS) (TM.pureHalf ιᶠ) tbl f A B x) ≡ runAt s (evalᴰ (Once.IR.Call {A} {B} f) x)
      RE = runAt-≡ {st = floc post} {st′ = s}
             {m = tableCalls (Once.CCC.FrameSemantics.fs-numerics FS) (TM.pureHalf ιᶠ) tbl f A B x}
             {m′ = evalᴰ (Once.IR.Call {A} {B} f) x} h-eq refl

      st-eq : stopsAt (floc post) (tableCalls (Once.CCC.FrameSemantics.fs-numerics FS) (TM.pureHalf ιᶠ) tbl f A B x) ≡ stopsAt s (evalᴰ (Once.IR.Call {A} {B} f) x)
      st-eq = cong (λ r → is-stopped (proj₂ r)) RE

      trc : chain-events run ≡ eventsAt s (evalᴰ (Once.IR.Call {A} {B} f) x)
      trc = trans (chain-events-++ run1 (CalleeRun.run crun))
                  (trans (CalleeRun.events crun) (cong proj₁ RE))
