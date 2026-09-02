-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Typing — the STATIC semantics (OCP-0006, spec).
--
-- SPEC (trust boundary): what is well-typed — the declarative typing judgment
-- (`⊢ᵢ`/`⊢ᶜ`) and the `Typed` predicate. Re-exports
-- `Once.TypeCheck.Judgment` verbatim (the WHOLE module is spec; it is only
-- namespaced under the implementation package `Once.TypeCheck`). The elaborator
-- / classifier / soundness / completeness are IMPLEMENTATION, checked against
-- these rules, and are NOT re-exported.
------------------------------------------------------------------------

module Once.Spec.Typing where

-- EXPLICIT re-export. Every rule is named, so ADDING A TYPING RULE requires
-- touching this list — the language definition cannot grow by accident.
open import Once.TypeCheck.Judgment public
-- `Judgment.Typed` is NOT re-exported: it is a nullary alias for
-- `_⊢_∶_⨾_` that nothing uses, and its name collides with the PROGRAM-level
-- `Typed` in `Once.Spec.Program` — two different notions, one word. The
-- judgment is the one a reader needs; the alias adds nothing.
  using ( _⊢ᵢ_∶_⨾_ ; _⊢ᶜ_∶_⨾_ ; _⊢_∶_⨾_
        -- ⊢ᵢ — synthesis
        ; t-int ; t-float ; t-str ; t-unit ; t-unit-var
        ; t-var-local ; t-var-qualified ; t-var-resolved ; t-var-import
        ; t-var-poly-instantiate-infer
        ; t-annot ; t-pair ; t-neg ; t-neg-float ; t-let ; t-case
        ; t-binop-arith ; t-binop-arith-float
        ; t-binop-arith-float-il ; t-binop-arith-float-ir ; t-binop-cmp
        ; t-id-app ; t-fst-app ; t-snd-app ; t-terminal-app ; t-apply-app-infer
        ; t-app ; t-effApp
        -- ⊢ᶜ — checking (D127: the categorical combinators live here)
        ; t-id-check ; t-fst-check ; t-snd-check
        ; t-terminal-morph-check ; t-initial-morph-check
        ; t-inl-morph-check ; t-inr-morph-check
        ; t-compose-check ; t-case-copair-check ; t-pair-morph-check
        ; t-curry-check ; t-cata-check
        ; t-embed ; t-lam ; t-pair-lit-check
        ; t-In-app-check ; t-apply-check
        ; t-inl-app-check ; t-inr-app-check ; t-initial-app-check
        ; t-subsume ; t-arg-driven-app-check ; t-var-poly-instantiate
        )
