-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Verified.Behavior — WHAT THIS COMPILER CLAIMS
--
-- Concrete choices for the abstract `Source`, `Behavior`, and `⟦_⟧`
-- fields of `CorrectCompiler`. A reviewer reads THIS module to
-- answer: "what does correctness mean for THIS compiler?"
--
-- Currently postulated; discharge maps to Plan 0.4.2 (frontend↔
-- backend connector). Once discharged, every entry below is a
-- concrete inspectable definition that imports `Once.Surface.Syntax`
-- and `Once.Surface.Semantics`.
------------------------------------------------------------------------

module Once.Verified.Behavior where

postulate
  -- Source ASTs accepted by the compiler. Discharge: a sigma over
  -- the existing `Once.Surface.Syntax.Expr` family that captures
  -- "well-typed program with main : Eff Unit Unit."
  Source : Set

  -- Observable behaviour of a program. Discharge: whatever
  -- `⟦ Eff Unit Unit ⟧` evaluates to in `Once.Surface.Semantics`
  -- (likely a free monad over `SigOp` events). The shape is opaque
  -- at the spec level — only equality of behaviours matters.
  Behavior : Set

  -- Source semantics. Discharge: `Once.Surface.Semantics.evalSurface`
  -- on the underlying AST.
  ⟦_⟧ : Source → Behavior
