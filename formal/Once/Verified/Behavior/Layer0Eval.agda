-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Verified.Behavior.Layer0Eval — Layer 0 source projection.
--
-- For Layer 0 the only SigOp programs invoke is `linux.exit`. The
-- intended `⟦_⟧` projection walks a typed Surface expression of
-- `main`'s body looking for `effApp (sigOp "linux.exit") arg`,
-- evaluates `arg` via `evalSurface` (its type is `Int`, fixed by
-- the user's signature declaration in `Strata/Interpretations/...`),
-- and returns the resulting ℤ.
--
-- IMPLEMENTATION STATUS — POSTULATED.
--
-- Writing this concretely runs into Agda dependent-pattern issues:
-- pattern matching `effApp (sigOp "linux.exit") arg` requires
-- explicitly instantiating the implicit `A = Int`, and the catch-all
-- coverage check struggles with `var i` in non-empty contexts (and
-- even in `∅` due to `lookup`'s opacity in the unification). The
-- clean discharge needs a structural-recursion-friendly view, or
-- the existing `SigOpInfo` registry to type-tag the SigOp constructor.
--
-- Marked as a named gap; Layer 0 functionality is well-defined,
-- the implementation is the work.
------------------------------------------------------------------------

module Once.Verified.Behavior.Layer0Eval where

open import Data.Integer using (ℤ)
open import Data.Maybe using (Maybe)

open import Once.Type           using (Type; Unit; _⇒[_]_; mk-kind; Many; eff)
open import Once.Surface.Syntax using (Ctx; Usage; Expr)
open import Once.Surface.Semantics using (Env)

postulate
  -- Find the `linux.exit` argument and evaluate it via evalSurface.
  -- Returns `nothing` if the program doesn't have the canonical
  -- Layer 0 shape.
  --
  -- Discharge: pattern match on the typed Expr; in the canonical
  -- shape `effApp {A = Int} (sigOp "linux.exit") arg`, return
  -- `just (evalSurface ρ arg)`. Catch-all: `nothing`.
  exit-arg : ∀ {n} {Γ : Ctx n} {Ψ : Usage n}
           → Env Γ → Expr Γ Ψ (Unit ⇒[ mk-kind Many eff ] Unit)
           → Maybe ℤ
