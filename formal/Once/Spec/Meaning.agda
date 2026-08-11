-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Meaning — the DYNAMIC semantics (OCP-0006, spec).
--
-- SPEC (trust boundary): what a program MEANS. The reference meaning is
-- the DERIVATION DENOTATION `⟦_⟧ᵈ` (Plan 0.58 P5):
--   * `Once.Denotation.ValueDomain` — the semantic domain `⟦_⟧ᴰ` (types
--     as sets, `emit-D`, `inject`/`forget`, the functor coercion).
--   * `Once.Denotation.Behavior` — `Behavior = ℕ → List SigOpEvent`:
--     a program's observable is its SigOp trace (programs do not return).
--   * `Once.Denotation.Meaning` — `⟦_⟧ᶜ`/`⟦_⟧ᵢ`: the typing derivation's
--     denotation, defined by direct induction on `_⊢ᶜ_`/`_⊢ᵢ_`.
--   * `Once.Denotation.MainMeaning` — `meaningᵈ`: a typed module's
--     `Behavior` (the denotation of its `main` derivation).
--
-- NOT spec (implementation, checked against this): `realize` (the
-- derivation→IR-morphism bridge), `evalᴰ` (`Once.Denotation.DenotTrace`,
-- the IR-expression trace evaluator), `SD.⟦_⟧ˢ` (`SourceDenote`, related
-- to `⟦_⟧ᵈ` by the proven `bridgeᵈ`), and the elaborator.
--
-- `Once.IR` stays OUTSIDE the spec (OCP option a): it is a pure syntax
-- vocabulary tier (no machine behaviour), shared by spec and implementation
-- like `Once.Type`, so it may appear in leaf imports but is NOT re-exported.
------------------------------------------------------------------------

module Once.Spec.Meaning where

open import Once.Denotation.ValueDomain public
open import Once.Denotation.Behavior    public
open import Once.Denotation.Meaning     public
open import Once.Denotation.MainMeaning public
