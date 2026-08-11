-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Syntax — the program GRAMMAR (OCP-0006, spec).
--
-- SPEC (trust boundary): what a program IS, at the two stages a reader cares
-- about — `Once.TypeCheck.Raw` (`RawExpr`, the parsed concrete syntax the
-- programmer writes) and `Once.Surface.Syntax` (`Expr`, the intrinsically-typed
-- term grammar the denotation interprets). Both are re-exported.
------------------------------------------------------------------------

module Once.Spec.Syntax where

-- P5: `RawExpr` ONLY — what you may WRITE. The elaborated `Surface.Expr`
-- family is elaborator OUTPUT (implementation), not spec.
open import Once.TypeCheck.Raw    public
