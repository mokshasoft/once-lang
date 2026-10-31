-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.CataBr.FoldLoop   (plan 0.135 S3, cata M4 stage D2)
--
-- THE WHOLE FOLD LOOP, PROVED: from the fold head with eval `ns` and val
-- `vs` (`FoldInv.Inv.HeadAt`), the machine runs as stage A's model
-- `PO.runPO ns vs` at every depth — its events, log, budget, stop — and,
-- when the model RETURNED the value stack `ws`, it is back at the fold head
-- with eval empty and val `ws` (`Loop.loop-run`, a `FoldInv.RoundRun`).
--
--   * `FoldBind.bind-rr` / `pure-rr`: RoundRuns compose along `_>>=∞_`,
--     and `return∞` is the empty run;
--   * `Loop.loop`: induction on the eval list; each node is one
--     `FoldRound.Round.round-po` (fill, the algebra's block call, push)
--     followed by the rest (`PO.runPO-step`). The fills succeed on the
--     loop's own run (`FillOk.Ok`, carried by the induction).
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun; tableEnv)
module Once.CCC.Codegen.IRObsCorrect.CataBr.FoldLoop (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Meaning using (module PO)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.FillOk using (module FillOk)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Text o tbl using (module CataBrTextC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.FoldInv o tbl using (module CataFoldInvC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.FoldText o tbl using (module CataFoldTextC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.FoldRound o tbl using (module CataFoldRoundC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.FoldBind o tbl using (module CataFoldBindC)
open import Once.CCC.Machine.SMCore
  using (LocState; module LocState; AbstractTrace; AllocState; module AllocState; StoredValue)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation)
open import Once.Memory.HeapAddress using (HeapLocation)
open import Once.IRTy using (IRTy; IRFunctor; WellFormedFI; ⟦_⟧TI; ⌈_⌉F; μ-type)
import Once.IRTy as IRTy′
open import Once.IRTy.WF using (wf-⌈⌉)
open import Once.Res using (Res; returns; stopped; is-stopped)
open import Once.IR.Semantics.Iterative using (T∞; return∞; _>>=∞_)
open import Once.Denotation.Approx using (Ap; done; cut; NotCut; budgetLeft; thenAp; run-approx-bind)
open import Data.List.Properties using (++-identityʳ)
import Once.IR.Semantics.Trace as TM
open import Once.IR.Semantics.Event using (SigOpEvent)
open import Once.Spec.Word using (Carrier)
open import Once.IR.Semantics.Value Carrier Carrier using (sem-Out; ⟦_⟧F)
open import Data.Product using (Σ)

module CataFoldLoopC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open CataBrTextC {FS} using (module Text)
  open CataFoldInvC {FS} using (module Inv; RoundRun; Same)
  open CataFoldTextC {FS} using (module FoldAt)
  open CataFoldRoundC {FS} using (module Round)
  open CataFoldBindC {FS} using (bind-rr; pure-rr)
  open LocState using (halted)
  open AllocState using (next-slot)

  ------------------------------------------------------------------------
  -- THE FOLD LOOP.
  ------------------------------------------------------------------------
  module Loop (prog : AbstractTrace) {F : IRFunctor} (wf : WellFormedFI F) {E C : IRTy} (alg : IR (E IRTy′.* ⟦ F ⟧TI C) C)
              (ih : IRObsCorrectF alg) (n l base : ℕ) (ss : AllSlotStable prog) (cr : BlockRuns prog)
              (span : SpanAt prog base (Text.text′ wf alg n l))
              (la : LabelsAt prog base (Text.text′ wf alg n l))
              (bl : BlocksAt prog (blocks n l (Cata wf alg)))
              (sn hc : HeapLocation) (e : ⟦ E ⟧) (env-sv : StoredValue FS) where

    -- (no `module … = Round …`: applying it copies the round's whole proof;
    -- its exports are used as functions)
    c bodyL X : ℕ
    c = Text.Pc.cslot wf alg n l
    bodyL = Text.Pc.bodyL wf alg n l
    X = FoldAt.X wf alg n l prog base span la

    alg₀ : ⟦ ⌈ F ⌉F ⟧F ⟦ C ⟧ → T∞ ⟦ C ⟧
    alg₀ = Round.alg₀ prog wf alg ih n l base ss cr span la bl sn hc e env-sv

    open Inv prog F E C n c bodyL X sn hc e env-sv

    module FO = FillOk (wf-⌈⌉ wf) alg₀

    runP : List ⟦ μ-type F ⟧ → List ⟦ C ⟧ → T∞ (List ⟦ C ⟧)
    runP = PO.runPO (wf-⌈⌉ wf) alg₀

    -- back at the head, nothing left to fold, the value stack `ws`
    Done : List ⟦ C ⟧ → FlatState → Set
    Done ws τ = HeadAt τ [] ws

    loop : ∀ (ns : List ⟦ μ-type F ⟧) (vs : List ⟦ C ⟧) (σ : FlatState)
         → FO.Ok ns (length vs) → HeadAt σ ns vs → flink σ ≡ nothing → (k : ℕ)
         → RoundRun prog n σ (runP ns vs) k Done
    loop []       vs σ ok h lk k = pure-rr σ vs k {Done} (HeadAt.nh h) lk h
    loop (t ∷ ns) vs σ ok h lk k = step (FO.step-ok t ns vs ok)
      where
        step : Σ _ (λ l′ → Σ (List ⟦ C ⟧) λ rest
                 → (PO.fill (wf-⌈⌉ wf) alg₀ ⌈ F ⌉F (sem-Out (wf-⌈⌉ wf) t) vs ≡ just (l′ , rest))
                 × FO.Ok ns (suc (length rest)))
             → RoundRun prog n σ (runP (t ∷ ns) vs) k Done
        step (l′ , rest , fq , ok′) =
          subst (λ M → RoundRun prog n σ M k Done) (sym (PO.runPO-step (wf-⌈⌉ wf) alg₀ t ns vs fq))
            (bind-rr {prog} {n} {σ} {⟦ C ⟧} {List ⟦ C ⟧} {alg₀ l′} {λ c → runP ns (c ∷ rest)} {k}
                     {λ v τ → HeadAt τ ns (v ∷ rest)} {Done}
               R1 (λ {c} {r} eq → loop ns (c ∷ rest) (RoundRun.τ R1) ok′ (RoundRun.post R1 eq)
                                       (RoundRun.no-link R1 (subst NotCut (sym eq) tt)) r))
          where
            R1 : RoundRun prog n σ (alg₀ l′) k (λ v τ → HeadAt τ ns (v ∷ rest))
            R1 = Round.round-po prog wf alg ih n l base ss cr span la bl sn hc e env-sv σ t ns vs l′ rest fq h k

    abstract
      loop-run : ∀ (ns : List ⟦ μ-type F ⟧) (vs : List ⟦ C ⟧) (σ : FlatState)
               → FO.Ok ns (length vs) → HeadAt σ ns vs → flink σ ≡ nothing → (k : ℕ)
               → RoundRun prog n σ (runP ns vs) k Done
      loop-run = loop
