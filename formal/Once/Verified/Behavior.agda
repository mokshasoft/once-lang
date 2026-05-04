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

open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ)

import Once.Grammar as G

------------------------------------------------------------------------
-- Behavior — the chosen observable.
--
-- For Layer 0, the only effect a program can perform is `exit N`.
-- The observable phenomenon we promise to preserve is: "what exit
-- code did the program produce, if any?" This is the narrowest
-- interesting Behavior — sufficient for `exit ((id . id . id) 42)`
-- but coarse enough to be vacuous for programs that do I/O before
-- exiting (a `hello world; exit 0` program would be observably
-- equivalent to a silent `exit 0` under this Behavior).
--
-- Widening: when richer effects come online (read, write, …), this
-- becomes `List SigOpEvent × Maybe ℕ` (a syscall trace plus exit
-- code) or a free-monad denotation. Until then, exit code suffices.
--
-- This is a CHOICE, not a derived consequence of CCC / structural
-- laws. Those laws prove equalities between source terms; this
-- definition declares what counts as observably-equivalent to the
-- outside world.
------------------------------------------------------------------------

Behavior : Set
Behavior = Maybe ℕ

------------------------------------------------------------------------
-- Source — anchored at the formal grammar.
--
-- `Source = GModule` is the most natural anchor: the parser produces
-- it, the rest of the compiler consumes it. Choosing this point
-- means `compile` carries responsibility for typechecking and
-- codegen; parsing itself is upstream (its correctness is a separate
-- claim handled in `Once.Parser` / `Once.Grammar.Roundtrip`).
--
-- A type-correct program is a `GModule` whose decls satisfy the
-- well-formedness predicates already in `Once.Grammar`
-- (`ValidMainType`, `ValidDeclPair`, …). For ill-typed modules
-- `compile` returns `nothing`, satisfying the witness vacuously.
------------------------------------------------------------------------

Source : Set
Source = G.GModule

------------------------------------------------------------------------
-- ⟦_⟧ — denotation. Postulated until Once.Surface.Semantics is
-- connected to GModule (typecheck + evalSurface + extract-exit-code).
-- The shape is forced by Source + Behavior; only the wiring is gap.
------------------------------------------------------------------------

postulate
  -- ⟦ m ⟧ = if (typecheck m) succeeds and `main : Eff Unit Unit` is
  -- well-typed, evaluate via evalSurface and read the exit code from
  -- the resulting effect tree. Else `nothing`.
  ⟦_⟧ : Source → Behavior
