-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Denotation.Realize — the REFERENCE ELABORATION SEMANTICS (Plan 0.49
-- Phase 2 / route 2). This is part of the DENOTATIONAL SPEC, NOT the compiler.
--
-- `realize` turns a typing DERIVATION (`ctx ⊢ᶜ e ∶ A ⨾ Ψ`, which is term-free)
-- into the intrinsically-typed surface term it denotes. The *meaning* of a
-- source program is then `SD.⟦ realize D ⟧ˢ` — "elaborate (the reference way),
-- then denote". `realize` is the surface half of the authored semantics, the
-- companion to `SD.⟦_⟧ˢ` (term → trace).
--
-- ╔══════════════════════════════════════════════════════════════════╗
-- ║  ELABORATOR-FREE BY CONSTRUCTION — the no-cheat constraint.       ║
-- ║  This module MUST NOT import `Once.TypeCheck.Elaborate` (the       ║
-- ║  `checkElab`/`inferElab` algorithm). It reads the term off the    ║
-- ║  declarative derivation's STRUCTURE (built from the raw program +  ║
-- ║  deterministic lookups), never off `checkElab`'s output. If this   ║
-- ║  import line is ever added, the layering breaks and the agreement  ║
-- ║  bridge would cancel (proving the elaborator with the elaborator). ║
-- ║  The reviewer audits ONE thing: this import list excludes the      ║
-- ║  elaborator — exactly as 0.49 keeps the meaning free of the        ║
-- ║  compiler.                                                         ║
-- ╚══════════════════════════════════════════════════════════════════╝
--
-- `realize` is a DEFINITION (a total function); all PROOFS relating it to the
-- real `checkElab` (the agreement bridge) live in the proof layer
-- (`Once.Adequacy.*`), which is the only place allowed to import both.
------------------------------------------------------------------------

module Once.Denotation.Realize where

open import Once.Type using (Type)
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.TypeCheck.Classify using (NamedCtx)
open import Once.TypeCheck.Judgment using (_⊢ᶜ_∶_⨾_)
open import Once.Surface.Syntax using (Expr; Usage)

-- Postulated for now (top-down: the module boundary + the meaning wiring come
-- FIRST, so the elaborator-free constraint is enforced before a single clause
-- is written). Discharged clause-by-clause against the judgment.
postulate
  realize : ∀ {ctx : NamedCtx} {e : RawExpr} {A : Type}
              {Ψ : Usage (NamedCtx.size ctx)} →
            ctx ⊢ᶜ e ∶ A ⨾ Ψ → Expr (NamedCtx.debruijn ctx) Ψ A
