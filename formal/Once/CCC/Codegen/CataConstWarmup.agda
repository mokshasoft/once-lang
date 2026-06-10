-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Codegen.CataConstWarmup — the `strat-const` warmup for the
-- cata-correctness discharge (Plan 0.36, task #8).
--
-- A `strat-const` functor has `rec-count F = 0` (no `Id` positions), so
-- `cata-dispatch strat-const n1 l1 at = (n1 , l1 , at)` passes the
-- algebra's trace through UNCHANGED. Hence the compiled `strat-const`
-- cata IS the compiled algebra — its machine side has no loop, and its
-- correctness reduces to the algebra's (the IH the general discharge
-- supplies) plus a μ↔layer iso at the value/`obs` level.
--
-- This module lands the foundational fact: the codegen identity.
------------------------------------------------------------------------

module Once.CCC.Codegen.CataConstWarmup where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ)

open import Once.Type using (⟦_⟧T; Functor)
open import Once.Functor.Translate using (WellFormedF)
open import Once.CCC.IR using (IR; Cata)
open import Once.CCC.Codegen.IRToTrace
  using (ir-to-trace-at-frontier; cata-strategy; strat-const)

-- The compiled `strat-const` cata's trace IS the algebra's trace (at any
-- frontier `n`): `cata-dispatch strat-const` is the identity on `at`. So
-- `flat-events`/`exec-flat` over the cata equal those over `alg`
-- definitionally, and the `strat-const` branch of `cata-correct` reduces
-- to `alg`'s `IRObsCorrectF` (no loop↔fold needed).
cata-const-trace-eq : ∀ {F} (wf : WellFormedF F) {A} (alg : IR (⟦ F ⟧T A) A) (n : ℕ)
                    → cata-strategy F ≡ strat-const
                    → ir-to-trace-at-frontier n (Cata wf alg)
                        ≡ ir-to-trace-at-frontier n alg
cata-const-trace-eq wf alg n sc rewrite sc = refl
