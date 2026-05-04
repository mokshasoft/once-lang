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
-- The only real gap here is the connector that bridges the parser
-- output (Module / RawExpr) to a closed, well-typed Surface
-- expression with `main : Eff Unit Unit`. Once that's concrete
-- (Plan 0.4.2), `⟦_⟧` is forced: it is `evalSurface ε (ast-of pc)`
-- composed with the exit-code projection. There's no choice in it
-- — the shape is determined by `Source` and `Behavior` together.
--
-- We postulate `⟦_⟧` here only because `Source` is postulated; both
-- are filled in together when the connector lands.
------------------------------------------------------------------------

postulate
  -- Source ASTs accepted by the compiler. Discharge: a sigma over
  -- the existing `Once.Surface.Syntax.Expr` family that captures
  -- "well-typed program with main : Eff Unit Unit."
  Source : Set

  -- Forced once `Source` is concrete:
  --   ⟦ pc ⟧ = extract-exit-code (evalSurface ε (ast-of pc))
  -- where `extract-exit-code : ⟦ Eff Unit Unit ⟧Type → Maybe ℕ`
  -- reads the `exit N` event from the effect-tree denotation.
  ⟦_⟧ : Source → Behavior
