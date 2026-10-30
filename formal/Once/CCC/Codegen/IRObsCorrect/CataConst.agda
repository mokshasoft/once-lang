-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.CataConst   (plan 0.125 S3, cata M1)
--
-- `cata-correct` AT `strat-const`, PROVED: a fold over a functor with no
-- recursive position is its algebra, called once on the input's own layer.
--
-- The run (`cata-trace-const`):
--
--   1. the setup's eighteen rows (`CataConst.Setup`) split the input pair
--      `(env , μ)`, build the argument pair `pr = [env , _]` and the closure
--      record `cl = [0 , body]`;
--   2. the call's eleven rows (`CataConst.Call`) put the μ cell in `pr[1]`,
--      `cl` in the closure register and `pr` in `Input1`;
--   3. `instr-call-closure` reads the code cell and lands on the body's
--      marker — the one marker of that label (`thunk-found`, from
--      `ThunksUnique`);
--   4. the body is the algebra, emitted once at frontier 0: its run is the
--      block-call lemma (`BlockCall.block-call`) on the algebra's own
--      obligation (the IH), with the pair as its input. The μ cell IS a
--      valid layer (`μ-layer`), and for an `Id`-free functor the layer's
--      type is the algebra's (`Meaning.tyeq`);
--   5. when the call RETURNED, the jump over the body and its end label
--      finish the fragment. When it stopped or was cut, the run ends inside
--      the callee, as `block-call-gen` ends.
--
-- What it means (`Meaning.cata-const-meaning′`): the cata's approximation
-- is the algebra's on that layer, so the callee's run is the cata's
-- (`crun-retarget`).
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)
import Once.CCC.Machine.SMCore as SMCore

import Data.List as DL
open import Once.Denotation.Program using (IRFun; tableEnv)
module Once.CCC.Codegen.IRObsCorrect.CataConst (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Base o tbl using (module ResuspBaseC)
open import Once.CCC.Codegen.IRObsCorrect.CataConst.Layout o tbl using (module CataLayoutC)
open import Once.CCC.Codegen.IRObsCorrect.CataConst.Setup o tbl using (module CataSetupC)
open import Once.CCC.Codegen.IRObsCorrect.CataConst.Call o tbl using (module CataCallC)
open import Once.CCC.Codegen.IRObsCorrect.CataConst.Run o tbl using (module CataRunC)
open import Once.CCC.Codegen.IRToTrace o using (cata-strategy; strat-const)
open import Once.CCC.Machine.SMCore
  using (LocState; module LocState; AbstractTrace; AllocState; module AllocState; StoredValue; readReg; Input1; SV-Ptr; instr-call-closure; instr-ctrl; c-jmp; c-label)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Label using (ℓ)
open import Once.IRTy using (IRTy; IRFunctor; WellFormedFI; ⟦_⟧TI; ⌈_⌉F; μ-type)
import Once.IRTy as IRTy′
import Once.Denotation.ValueDomain as ValueDomain
open import Once.Memory.HeapAddress using (HeapLocation; sucHL; heap-loc; mkHeapRef)
open import Once.Internal.Res using (Res; returns; stopped; is-stopped)
open import Once.Internal.Iterative using (T∞)
open import Once.Denotation.Approx using (Ap; done; cut; NotCut; budgetLeft)
open import Data.List.Properties using (++-identityʳ)
import Once.CCC.FrameSemantics
import Once.Internal.Trace as TM

module CataConstC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open ResuspBaseC {FS} using (loc-ref; at-cf)
  open CataLayoutC {FS} using (module Text)
  open CataSetupC {FS} using (module Setup; SetupOut)
  open CataCallC {FS} using (module Call; CallOut)
  open CataRunC {FS} using (cell-sv; cell-read; module Run)
  open LocState using (regs; halted)
  open AllocState using (next-slot; next-heap-ref; current-frame)

  ------------------------------------------------------------------------
  -- THE THIRTY ROWS BEFORE THE CALL, for one input (the pair at `phl`, its
  -- μ cell pointing at `μhl`), handed to `Run` as facts about their last
  -- state.
  ------------------------------------------------------------------------
  module Glue {F : IRFunctor} (wf : WellFormedFI F) {E C : IRTy} (alg : IR (E IRTy′.* ⟦ F ⟧TI C) C)
              (ih : IRObsCorrectF alg) (st : cata-strategy ⌈ F ⌉F ≡ strat-const)
              (n l : ℕ) (prog : AbstractTrace) (base : ℕ) (ss : AllSlotStable prog) (cr : BlockRuns prog)
              (span : SpanAt prog base (emitted n l (Cata wf alg)))
              (bl : BlocksAt prog (blocks n l (Cata wf alg)))
              (la : LabelsAt prog base (emitted n l (Cata wf alg)))
              (x : ⟦ E IRTy′.* μ-type F ⟧) (s : LocState FS) (alloc : AllocState {FS}) (cl : StoredValue FS)
              (ns0 : next-slot alloc ≡ 0) (nh : halted s ≡ false) (k : ℕ) (rs : List ℕ)
              (phl : HeapLocation) (rdi : readReg (regs s) Input1 ≡ SV-Ptr (AtDynamic phl))
              (c₁ : CellAt {prog = prog} alloc E (proj₁ x) (AtDynamic phl) s)
              (μhl : HeapLocation) (mC : AllocMode)
              (rdμ : readLoc s (AtDynamic (sucHL phl)) ≡ just (SV-Ptr (AtDynamic μhl)))
              (lμ : Live alloc (AtDynamic μhl))
              (vμ : ValidAtWF {prog = prog} mC alloc {μ-type F} (proj₂ x) (AtDynamic μhl) s)
              where

    module T = Text wf alg n l
    module TA = T.At prog base (subst (SpanAt prog base) (T.emitted-eq st) span)
                               (subst (LabelsAt prog base) (T.emitted-eq st) la)

    σ : FlatState
    σ = entry-flat base s alloc cl rs

    env-sv μ-sv : StoredValue FS
    env-sv = cell-sv c₁
    μ-sv   = SV-Ptr (AtDynamic μhl)

    r₀ : ℕ
    r₀ = next-heap-ref alloc

    so : SetupOut n T.l1 prog σ env-sv μ-sv
    so = Setup.out n T.l1 prog σ TA.span-setup nh phl env-sv μ-sv rdi (cell-read c₁) rdμ
    module SO = SetupOut so

    hp : HeapLocation
    hp = heap-loc (mkHeapRef r₀) 0

    shp≢shc : AtDynamic {FS} (sucHL hp) ≢ AtDynamic (sucHL SO.hc)
    shp≢shc e = <-irrefl (trans (cong loc-ref e) SO.ref-hc) (n<1+n r₀)

    span-call′ : SpanAt prog (fpc SO.u) T.call
    span-call′ = subst (λ b → SpanAt prog b T.call) (sym SO.pc) TA.span-call

    co : CallOut n prog SO.u alloc hp SO.hc (ℓ o T.l1) env-sv μ-sv
    co = Call.out n prog SO.u alloc span-call′ SO.nh hp SO.hc (ℓ o T.l1) env-sv μ-sv SO.inμ SO.cl SO.pr SO.hp0 SO.code
                  shp≢shc SO.cf ≤-refl
    module CO = CallOut co

    result : MachineRefinesObsF prog base n l (Cata wf alg) x s alloc cl rs k
    result = Run.result wf alg ih st n l prog base ss cr span bl la x s alloc cl ns0 k rs
               CO.w SO.u SO.runS SO.seg CO.runK CO.seg CO.nh (trans CO.pc (cong (11 +_) SO.pc)) (trans CO.ret SO.ret)
               SO.hc hp μhl mC (AtDynamic phl) CO.clo CO.code CO.inp
               c₁ (trans CO.hp0 (sym (cell-read c₁))) CO.shp refl (≤-reflexive (sym SO.hr)) lμ vμ

  ------------------------------------------------------------------------
  -- THE CLAUSE.
  ------------------------------------------------------------------------
  cata-correct-const : ∀ {F} (wf : WellFormedFI F) {E C} (alg : IR (E IRTy′.* ⟦ F ⟧TI C) C)
                     → IRObsCorrectF alg → cata-strategy ⌈ F ⌉F ≡ strat-const
                     → IRObsCorrectF (Cata wf alg)
  -- the input is a PAIR: no register holds it, and it is not `Unit`
  cata-correct-const wf alg ih st n l prog base ss cr span bl la mIn x s alloc cl ns0 nh (in-reg () _) k rs
  cata-correct-const wf alg ih st n l prog base ss cr span bl la mIn x s alloc cl ns0 nh (in-unit ()) k rs
  cata-correct-const wf alg ih st n l prog base ss cr span bl la mIn x s alloc cl ns0 nh (in-loc (AtStack _ _) _ () _) k rs
  cata-correct-const {F} wf {E} {C} alg ih st n l prog base ss cr span bl la mIn x s alloc cl ns0 nh
    (in-loc (AtDynamic phl) valid lv rdi) k rs =
    go-μ (PairValidWF.snd-cell d)
    where
      d = decomposePairWF valid

      -- a μ is never inline, and its cell points at the heap
      go-μ : CellAt {prog = prog} alloc (μ-type F) (proj₂ x) (AtDynamic (sucHL phl)) s
           → MachineRefinesObsF prog base n l (Cata wf alg) x s alloc cl rs k
      go-μ (cell-inline (rep-prim ()) _)
      go-μ (cell-inline (rep-unit () _) _)
      go-μ (cell-ptr {comp-loc = AtStack _ _} _ () _)
      go-μ (cell-ptr {comp-loc = AtDynamic μhl} {mC = mC} rdμ lμ vμ) =
        Glue.result wf alg ih st n l prog base ss cr span bl la x s alloc cl ns0 nh k rs
                    phl rdi (PairValidWF.fst-cell d) μhl mC rdμ lμ vμ
