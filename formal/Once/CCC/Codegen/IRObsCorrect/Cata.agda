-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Cata   (plan 0.125 S3, cata M1)
--
-- `cata-correct` IS A DEFINITION NOW, dispatching on the strategy the
-- emitter picks (`cata-strategy ⌈ F ⌉F`, IRToTrace's classifier), so each
-- strategy's obligation is about the ONE trace `cata-dispatch` emits for it.
--
--   * `strat-const` (no recursive position) is PROVED: `CataConst`.
--   * `strat-branching` (every recursive functor, the generic post-order
--     walk) is PROVED: `CataBr.Branching` (plan 0.125's cata M4). (The old
--     `strat-nat` / `strat-linear` shape specialisations were deleted
--     2026-10-30: they miscompiled functors outside their shape; see
--     IRToTrace's classifier.)
--
-- So `cata-correct` holds for every cata, with no assumption.
--
-- It lives here rather than in `Interface` (where the single postulate used
-- to be) because the proof needs the clause modules (`BlockCall`, `Apply`,
-- `NuForce`), and those import `Interface`.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.Cata (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.CataConst o tbl using (module CataConstC)
-- M4 (strat-branching), stage A: the cata's meaning as the emitted post-order
-- process (flatten invariant `FI`, fold loop `runPO`, `po-run`, `cata-br-meaning`).
-- M4's fold-loop proof consumes it; imported here so it sits under the apex.
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Meaning using (module PO; cata-alg; cata-br-meaning)
-- M4 stage B: the machine side of the two functor walks and the linked stacks,
-- as abstract `Walk` bundles (`CataBr.Walk`): `push2`/`pop2` (`CataBr.Stack`),
-- `visit-walk` (`CataBr.Visit`), `rebuild-walk` (`CataBr.Rebuild`), and the
-- IR-level layer operations with their bridge to stage A (`CataBr.Layer`:
-- `children-eq`, `fill-enc`, `pushAll-eq`). The M4 loop proof (flatten and
-- fold loops) consumes them; imported here so they sit under the apex.
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Layer o using (kidsI; fillI; enc; children-eq; fill-enc; pushAll-eq)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Stack o tbl using (module CataStackC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Walk o tbl using (module CataWalkC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Visit o tbl using (module CataVisitC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Rebuild o tbl using (module CataRebuildC)
-- M4 stage C: the cata from its entry to the FOLD LOOP'S HEAD as one abstract
-- bundle (`CataBr.ToFold.ToFoldOut`, built by `Build.out`): M1's setup rows at
-- the branching slots, the init rows and the root's push (`CataBr.Init`), and
-- the flatten loop run to its exit (`CataBr.Flatten`, by induction on stage
-- A's measure; one round is `CataBr.Round`), ending with eval = `PO.FI … [ root ] []`.
-- The M4 fold stage consumes it; imported here so it sits under the apex.
open import Once.CCC.Codegen.IRObsCorrect.CataBr.ToFold o tbl using (module CataToFoldC)
-- M4 stage D1b: ONE ROUND of the FOLD loop and its EXIT, over the fold-head
-- invariant `CataBr.FoldInv.Inv.HeadAt` (eval/val stacks, call slots, the
-- closure record, the environment word): `CataBr.FoldRound.Round.round`
-- (pop, rebuild, the call rows with a fresh pair, the algebra's block call,
-- push, back edge — a `FoldInv.RoundRun` whose events/log/budget/stop are the
-- algebra's on the round's layer; `round-po` at stage A's model) and
-- `CataBr.FoldExit.Exit.exit` (eval empty: the top of val into `Output`, over
-- the body to the cata's end; `word→place`). D2's induction over the eval
-- list consumes them; imported here so they sit under the apex.
open import Once.CCC.Codegen.IRObsCorrect.CataBr.FoldRound o tbl using (module CataFoldRoundC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.FoldExit o tbl using (module CataFoldExitC)
-- M4 stage D2: THE WHOLE FOLD LOOP and THE CLAUSE. `CataBr.FillOk` (every fill on
-- the loop's own run succeeds), `CataBr.FoldBind` (round runs compose along a
-- bind), `CataBr.FoldLoop` (the loop runs as stage A's `runPO`, by induction on
-- the eval list), `CataBr.Branching` (entry → fold head → loop → exit, against
-- `cata-br-meaning`): `cata-correct-branching`, PROVED.
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Branching o tbl using (module CataBranchC)
open import Once.CCC.Codegen.IRToTrace o
  using (CataStrategy; cata-strategy; strat-const; strat-branching)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.IRTy using (IRFunctor; WellFormedFI; ⟦_⟧TI; ⌈_⌉F)
import Once.IRTy as IRTy′
open import Once.Internal.Type using (Functor)

module CataC {FS : FrameSemantics} where

  open Core {FS}
  open CataConstC {FS} using (cata-correct-const)
  open CataStackC {FS} using (push2-run; pop2-run; stack-tag; stack-keep)
  open CataVisitC {FS} using (module Visit)
  open CataRebuildC {FS} using (module Rebuild)
  open CataToFoldC {FS} using (ToFoldOut; module Build)
  open CataFoldRoundC {FS} using (module Round)
  open CataFoldExitC {FS} using (module Exit; word→place)

  -- The loop strategy, every functor with a recursive position (the
  -- classifier's `strat-branching`): PROVED, plan 0.125's cata M4.
  open CataBranchC {FS} using (cata-correct-branching)

  -- `cata-correct` RECEIVES the algebra's `IRObsCorrectF` (the IH);
  -- `ir-obs-correct` supplies it by recursing on `alg ⊂ Cata wf alg`.
  cata-correct : ∀ {F} (wf : WellFormedFI F) {E A} (alg : IR (E IRTy′.* ⟦ F ⟧TI A) A)
               → IRObsCorrectF alg
               → IRObsCorrectF (Cata wf alg)
  cata-correct {F} wf alg ih = by (cata-strategy ⌈ F ⌉F) refl
    where
      by : (st : CataStrategy) → cata-strategy ⌈ F ⌉F ≡ st → IRObsCorrectF (Cata wf alg)
      by strat-const         e = cata-correct-const     wf alg ih e
      by (strat-branching G) e = cata-correct-branching wf alg ih e
