-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Cata   (plan 0.135 S3, cata M1)
--
-- `cata-correct` IS A DEFINITION NOW, dispatching on the strategy the
-- emitter picks (`cata-strategy ⌈ F ⌉F`, IRToTrace's classifier), so each
-- strategy's obligation is about the ONE trace `cata-dispatch` emits for it.
--
--   * `strat-const` (no recursive position) is PROVED: `CataConst`.
--   * `strat-branching` (every recursive functor, the generic post-order
--     walk) is PROVED: `CataBr.Branching` (plan 0.135's cata M4). (The old
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
-- The branching clause: `CataBr.Branching` (entry → fold head → loop → exit,
-- against `CataBr.Meaning.cata-br-meaning`), whose import closure holds every
-- other `CataBr.*` module.
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Branching o tbl using (module CataBranchC)
open import Once.CCC.Codegen.IRToTrace o
  using (CataStrategy; cata-strategy; strat-const; strat-branching)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.IRTy using (WellFormedFI; ⟦_⟧TI; ⌈_⌉F)
import Once.IRTy as IRTy′

module CataC {FS : FrameSemantics} where

  open Core {FS}
  open CataConstC {FS} using (cata-correct-const)

  -- The loop strategy, every functor with a recursive position (the
  -- classifier's `strat-branching`): PROVED, plan 0.135's cata M4.
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
