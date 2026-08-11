-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Typing — the STATIC semantics (OCP-0006, spec).
--
-- SPEC (trust boundary): what is well-typed — the declarative typing judgment
-- (`⊢ᵢ`/`⊢ᶜ`/`⊢ᵍ`/`⊢ᵐ`) and the `Typed` predicate. Re-exports
-- `Once.TypeCheck.Judgment` verbatim (the WHOLE module is spec; it is only
-- namespaced under the implementation package `Once.TypeCheck`). The elaborator
-- / classifier / soundness / completeness are IMPLEMENTATION, checked against
-- these rules, and are NOT re-exported.
------------------------------------------------------------------------

module Once.Spec.Typing where

open import Once.TypeCheck.Judgment public
