-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.CataConst   (plan 0.135 S3, cata M1)
--
-- `cata-correct` AT `strat-const`, PROVED: a fold over a functor with no
-- recursive position is its algebra, called once on the input's own layer.
--
-- The run (`cata-trace-const`):
--
--   1. the setup's thirteen rows (`CataConst.Setup`) split the input pair
--      `(env , μ)` (env into slot `ev`) and build the closure record
--      `cl = [0 , body]`;
--   2. the call's fourteen rows (`CataConst.Call`) allocate a FRESH argument
--      pair `pr = [env , μ cell]` (plan 0.135 D1a: every call has its own),
--      put `cl` in the closure register and `pr` in `Input1`;
--   3. `instr-call-closure` reads the code cell and lands on the body's
--      marker — the one marker of that label (`thunk-found`, from
--      `ThunksUnique`);
--   4. the body is the algebra, emitted once at frontier 0: its run is the
--      block-call lemma (`BlockCall.block-call`) on the algebra's own
--      obligation (the IH), with the pair as its input. The μ cell IS a
--      valid layer (`μ-layer`) — at a BOXED μ (`strat-box`, D366) the call's
--      first row reads the layer out of the box, and the pair gets the box's
--      cell (`μ-box-cell`) — and for an `Id`-free functor the layer's
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
open import Once.CCC.Codegen.IRObsCorrect.CataConst.Layout o tbl using (module CataLayoutC; head-box; strat-box-fun; unboxed-of; boxed-of)
open import Once.CCC.Codegen.IRObsCorrect.CataConst.Steps o tbl using (module CataStepsC; Head; h-mov; h-box; head-strat; head-instr)
open import Once.CCC.Codegen.IRObsCorrect.CataConst.Meaning o using (μ-layer-val)
open import Once.CCC.Codegen.IRToTrace o using (box-fun)
open import Once.CCC.Codegen.IRObsCorrect.CataConst.Setup o tbl using (module CataSetupC)
open import Once.CCC.Codegen.IRObsCorrect.CataConst.Call o tbl using (module CataCallC)
open import Once.CCC.Codegen.IRObsCorrect.CataConst.Run o tbl using (module CataRunC)
open import Once.CCC.Codegen.IRObsCorrect.Get o tbl using (module GetC)
open import Once.CCC.Codegen.IRObsCorrect.Inj o tbl using (module InjC)
import Once.CCC.Machine.FlatPut as FlatPut
open import Once.CCC.Codegen.Size using (size)
open import Once.CCC.Machine.MuRep using (box-fit)
open import Once.CCC.Codegen.IRToTrace o using (cata-strategy; strat-const)
open import Once.CCC.Machine.SMCore
  using (LocState; module LocState; AbstractTrace; AllocState; module AllocState; StoredValue; readReg; Input1; SV-Ptr; instr-call-closure; instr-ctrl; c-jmp; c-label)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Label using (ℓ)
open import Once.IRTy using (IRTy; IRFunctor; WellFormedFI; ⟦_⟧TI; ⌈_⌉F; μ-type)
import Once.IRTy as IRTy′
import Once.Denotation.ValueDomain as ValueDomain
open import Once.Memory.HeapAddress using (HeapLocation; sucHL; heap-loc; mkHeapRef; module HeapLocation; module HeapRef)
open HeapLocation using (heap-ref)
open HeapRef using (ref-id)
open import Once.Res using (Res; returns; stopped; is-stopped)
open import Once.IR.Semantics.Iterative using (T∞)
open import Once.Denotation.Approx using (Ap; done; cut; NotCut; budgetLeft)
open import Data.List.Properties using (++-identityʳ)
import Once.CCC.FrameSemantics
import Once.IR.Semantics.Trace as TM

module CataConstC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open ResuspBaseC {FS} using (loc-ref; at-cf; module SegA; live-from; SRun)
  open CataLayoutC {FS} using (module Text)
  open CataSetupC {FS} using (module Setup; SetupOut)
  open CataCallC {FS} using (module Call; CallOut)
  open CataRunC {FS} using (module Run)
  open CataCallC {FS} using (callK; callA; callB)
  module GetC′ = GetC {FS}
  module InjC′ = InjC {FS}
  open CataStepsC {FS} using (HeadOK; mov-head; box-head)
  open LocState using (regs; halted)
  open AllocState using (next-slot; next-heap-ref; current-frame)

  ------------------------------------------------------------------------
  -- THE ROWS BEFORE THE CALL, for one input (the flat pair at `pl`, its
  -- μ word at `size E` pointing at `μhl`), handed to `Run` as facts about
  -- their last state.
  ------------------------------------------------------------------------
  module Glue {F : IRFunctor} (wf : WellFormedFI F) {E C : IRTy} (alg : IR (E IRTy′.* ⟦ F ⟧TI C) C)
              (ih : IRObsCorrectF alg) (h : Head) (st : cata-strategy ⌈ F ⌉F ≡ head-strat h)
              (n l : ℕ) (prog : AbstractTrace) (base : ℕ) (ss : AllSlotStable prog) (cr : BlockRuns prog)
              (span : SpanAt prog base (emitted n l (Cata wf alg)))
              (bl : BlocksAt prog (blocks n l (Cata wf alg)))
              (la : LabelsAt prog base (emitted n l (Cata wf alg)))
              (x : ⟦ E IRTy′.* μ-type F ⟧) (s : LocState FS) (alloc : AllocState {FS}) (cl : StoredValue FS)
              (ns0 : next-slot alloc ≡ 0) (nh : halted s ≡ false) (k : ℕ) (rs : List ℕ)
              (pl : ValueLocation FS) (rdi : readReg (regs s) Input1 ≡ SV-Ptr pl) (lpl : Live alloc pl)
              (cE : CellAt {prog = prog} alloc E (proj₁ x) (SMCore.offsetLoc pl 0) s)
              (μhl : HeapLocation)
              (rdμ : readLoc s (SMCore.offsetLoc pl (size E)) ≡ just (SV-Ptr (AtDynamic μhl)))
              (lμ : Live alloc (AtDynamic μhl))
              -- D366: the LAYER as a value to put, and what the call's first row makes of the μ's pointer
              (lay-sv : StoredValue FS)
              (srcL : FlatPut.Src {FS} {prog} alloc s (⟦ F ⟧TI (μ-type F)) (μ-layer-val wf (proj₂ x)) lay-sv)
              (mk-hd : ∀ (σ′ : FlatState) → readReg (regs (floc σ′)) Input1 ≡ SV-Ptr (AtDynamic μhl)
                     → readLoc (floc σ′) (AtDynamic μhl) ≡ readLoc s (AtDynamic μhl)
                     → HeadOK prog σ′ h lay-sv)
              where

    module T = Text wf alg n l h
    module TA = T.At prog base (subst (SpanAt prog base) (T.emitted-eq st) span)
                               (subst (LabelsAt prog base) (T.emitted-eq st) la)

    σ : FlatState
    σ = entry-flat base s alloc cl rs

    so : SetupOut E (proj₁ x) n T.l1 prog σ (SV-Ptr (AtDynamic μhl))
    so = Setup.out E n T.l1 prog σ TA.span-setup nh pl rdi lpl cE (SV-Ptr (AtDynamic μhl)) rdμ
    module SO = SetupOut so

    hrU : next-heap-ref alloc ≤ next-heap-ref (falloc SO.u)
    hrU = ≤-trans (n≤1+n _) (≤-reflexive (sym SO.hr))

    co : CallOut n prog SO.u alloc SO.hc (ℓ o T.l1) E T.L (proj₁ x) (μ-layer-val wf (proj₂ x)) (DL.length (callA (head-instr h) E T.L n) + (1 + 2))
    co = Call.out h E T.L n prog SO.u alloc
           (subst (λ b → SpanAt prog b (callK (head-instr h) E T.L n)) (sym SO.pc) TA.span-callK)
           SO.nh SO.hc (ℓ o T.l1) SO.env-sv lay-sv
           (mk-hd SO.u SO.inμ (SO.keep (AtDynamic μhl) lμ))
           SO.cl SO.ev SO.code SO.lhc SO.src
           (FlatPut.src-tr {FS} {prog} SO.keep srcL)
           (live-from alloc (falloc SO.u) hrU) SO.bk SO.cf
    module CO = CallOut co

    lenK : T.CK ≡ DL.length (callA (head-instr h) E T.L n) + (1 + 2)
    lenK = length-++ (callA (head-instr h) E T.L n) {SMCore.instr-save-closure-reg ∷ callB n}

    result : MachineRefinesObsF prog base n l (Cata wf alg) x s alloc cl rs k
    result = Run.result wf alg ih h st n l prog base ss cr span bl la x s alloc cl ns0 k rs
               CO.w SO.u SO.runS SO.seg (subst (λ c → SRun prog c SO.u CO.w) (sym lenK) CO.runK) CO.seg CO.nh
               (trans CO.pc (trans (cong (_+ fpc SO.u) (sym lenK)) (cong (T.CK +_) SO.pc))) (trans CO.ret SO.ret)
               SO.hc CO.hp CO.clo CO.code CO.inp CO.pairV CO.lhp
               (bk-trans {a = alloc} {b = falloc SO.u} {c = falloc CO.w} SO.bk CO.bk (live-from alloc (falloc SO.u) hrU))

  ------------------------------------------------------------------------
  -- THE CLAUSE.
  ------------------------------------------------------------------------
  -- D366: one clause for both strategies with no recursive position; `h`
  -- says whether the μ is the layer's own pointer (`strat-const`) or a box
  -- whose cell holds the layer (`strat-box`).
  cata-correct-const : ∀ {F} (wf : WellFormedFI F) {E C} (alg : IR (E IRTy′.* ⟦ F ⟧TI C) C)
                     → IRObsCorrectF alg → (h : Head) → cata-strategy ⌈ F ⌉F ≡ head-strat h
                     → IRObsCorrectF (Cata wf alg)
  -- the input is a PAIR: no register holds it, and it is not `Unit`
  cata-correct-const wf alg ih h st n l prog base ss cr span bl la mIn x s alloc cl ns0 nh (in-reg () _) k rs
  cata-correct-const wf alg ih h st n l prog base ss cr span bl la mIn x s alloc cl ns0 nh (in-unit ()) k rs
  cata-correct-const {F} wf {E} {C} alg ih h st n l prog base ss cr span bl la mIn x s alloc cl ns0 nh
    (in-loc pl valid lv rdi) k rs =
    go-μ (PairValidWF.snd-cell d)
    where
      d = decomposePairWF valid

      cE : CellAt {prog = prog} alloc E (proj₁ x) (SMCore.offsetLoc pl 0) s
      cE = subst (λ z → CellAt {prog = prog} alloc E (proj₁ x) z s) (sym (GetC′.offset-zero pl)) (PairValidWF.fst-cell d)

      fit-not-node : ∀ {A : IRTy} → FitsInRegI A → IsNode A → ⊥
      fit-not-node fits-int ()
      fit-not-node fits-float ()

      fit-not-flat : ∀ {A : IRTy} → FitsInRegI A → IsFlat A → ⊥
      fit-not-flat fits-int ()
      fit-not-flat fits-float ()

      -- a μ is a node: its cell is a pointer word
      go-μ : CellAt {prog = prog} alloc (μ-type F) (proj₂ x) (SMCore.offsetLoc pl (size E)) s
           → MachineRefinesObsF prog base n l (Cata wf alg) x s alloc cl rs k
      go-μ (cell-inline (rep-prim ()) _)
      go-μ (cell-flat () _ _)
      go-μ (cell-ptr {comp-loc = AtStack _ _} _ _ () _)
      go-μ (cell-ptr {comp-loc = AtDynamic μhl} {mC = mC} _ rdμ lμ vμ) = by h st
        where
          by : (h′ : Head) → cata-strategy ⌈ F ⌉F ≡ head-strat h′ → MachineRefinesObsF prog base n l (Cata wf alg) x s alloc cl rs k
          -- the layer IS the μ's node: the pair's μ word points at it
          by h-mov st′ =
            Glue.result wf alg ih h-mov st′ n l prog base ss cr span bl la x s alloc cl ns0 nh k rs
                        pl rdi lv cE μhl rdμ lμ
                        (SV-Ptr (AtDynamic μhl))
                        (InjC′.src-loc {prog} (⟦ F ⟧TI (μ-type F))
                           (μ-layer {wf = wf} (unboxed-of wf (strat-box-fun ⌈ F ⌉F h-mov st′)) vμ) lμ)
                        (λ σ′ in0 _ → mov-head prog σ′ _ in0)
          -- the layer is the box's cell: a scalar (D366, `box-fit`)
          by h-box st′ = box-cell cμ
            where
              bx = boxed-of wf (strat-box-fun ⌈ F ⌉F h-box st′)
              cμ : CellAt {prog = prog} alloc (⟦ F ⟧TI (μ-type F)) (μ-layer-val wf (proj₂ x)) (AtDynamic μhl) s
              cμ = μ-box-cell {wf = wf} bx vμ
              box-cell : CellAt {prog = prog} alloc (⟦ F ⟧TI (μ-type F)) (μ-layer-val wf (proj₂ x)) (AtDynamic μhl) s
                       → MachineRefinesObsF prog base n l (Cata wf alg) x s alloc cl rs k
              box-cell (cell-ptr nd _ _ _) = ⊥-elim (fit-not-node (box-fit bx) nd)
              box-cell (cell-flat fl _ _)  = ⊥-elim (fit-not-flat (box-fit bx) fl)
              box-cell (cell-inline (rep-prim fit) r) =
                Glue.result wf alg ih h-box st′ n l prog base ss cr span bl la x s alloc cl ns0 nh k rs
                            pl rdi lv cE μhl rdμ lμ
                            (prim-sv fit (μ-layer-val wf (proj₂ x))) (FlatPut.src-scalar fit)
                            (λ σ′ in0 mem → box-head prog σ′ (AtDynamic μhl) _ in0
                                              (trans (cong (readLoc (floc σ′)) (GetC′.offset-zero (AtDynamic μhl))) (trans mem r)))
