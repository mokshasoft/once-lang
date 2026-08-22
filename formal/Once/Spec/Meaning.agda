-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Meaning — the DYNAMIC semantics (OCP-0006, spec).
--
-- SPEC (trust boundary): what a program MEANS. The reference meaning is
-- the DERIVATION DENOTATION `⟦_⟧ᵈ` (Plan 0.58 P5):
--   * `Once.Denotation.ValueDomain` — the semantic domain `⟦_⟧ᴰ` (types
--     as sets, `emit-D`, `inject`/`forget`, the functor coercion).
--   * `Once.Denotation.Admissible` — `AdmissibleM`: WHICH PROGRAMS A TARGET
--     OWES AN ANSWER FOR. `Typed` is target-free; this is the target-relative
--     half, and it is what makes rejecting an out-of-range `Int` literal legal
--     without making "reject everything" legal.
--   * `Once.Denotation.Trace` — `SigOpEvent` and `mkEvent`: WHAT AN
--     OBSERVATION IS. Which part of a SigOp invocation the outside world can
--     see, and therefore which two programs count as behaviourally equal.
--     This is a CHOICE, not a consequence — the same status `Behavior`'s own
--     header claims for itself — so it is reviewed here rather than left in a
--     module the spec merely reaches through. See D114 for what it currently
--     observes, which is LESS than it should.
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

-- D114: the observation vocabulary. `emit-D` (in `ValueDomain`, spec) calls
-- `mkEvent`, and `Behavior` names `SigOpEvent`, so this module was ALREADY
-- load-bearing spec behaviour — it was just not declared, and so not reviewed.
-- Re-exported, not moved: the module is 75 lines and contains nothing but the
-- event vocabulary, so declaring it is the whole fix.
-- D115/D116: which programs a target owes an answer for. In the spec for the
-- same reason the observable is: without it, a compiler that rejects every
-- program satisfies soundness vacuously.
open import Once.Denotation.Admissible  public

open import Once.Denotation.Trace       public

open import Once.Denotation.ValueDomain public
open import Once.Denotation.Behavior    public
open import Once.Denotation.Meaning     public
open import Once.Denotation.MainMeaning public
