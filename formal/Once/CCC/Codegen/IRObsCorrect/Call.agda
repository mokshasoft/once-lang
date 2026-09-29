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

import Data.List as DL
open import Once.Denotation.Program using (IRFun; tableEnv; LinkedAt)
module Once.CCC.Codegen.IRObsCorrect.Call (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl

import Once.CCC.FrameSemantics
open import Once.CCC.Machine.SMCore using (instr-ctrl; c-call-fn)
import Once.IRTy
import Once.IR
import Once.Denotation.DenotTrace as DT
import Once.Denotation.TraceMonad as TM

module CallC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}

  obs-correct-call : ∀ {A B} (f : CanonicalName) → LinkedAt tbl f A B → IRObsCorrectF (Once.IR.Call {A} {B} f)
  obs-correct-call {A} {B} f lk n l prog base _ cr span _ _ mIn x s alloc cl n≤ nh inp k = record
    { value-realized =
        realized (1 + CalleeRun.steps crun) (CalleeRun.settle crun)
                 (CalleeRun.out-mode crun) (CalleeRun.cont-alloc crun)
                 run (CalleeRun.live crun) (CalleeRun.returned crun) (CalleeRun.stops crun)
                 (CalleeRun.no-ret crun) (CalleeRun.no-link crun) (CalleeRun.place crun)
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

      crun : CalleeRun prog post (suc base) B (tableEnv (Once.CCC.FrameSemantics.fs-numerics FS) tbl f A B x) k
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
               → MemOps.readLoc (floc (CalleeRun.settle crun)) loc ≡ MemOps.readLoc s loc
      mem-pres loc bf =
        trans (CalleeRun.mem-pres crun alloc n (cong falloc call-eq) loc bf)
              (cong (λ st → MemOps.readLoc (floc st) loc) call-eq)

      trc : take k (chain-events run)
          ≡ take k (projTrace (tableEnv (Once.CCC.FrameSemantics.fs-numerics FS) tbl f A B x) k)
      trc = trans (cong (take k) (chain-events-++ run1 (CalleeRun.run crun)))
                  (CalleeRun.events crun)
