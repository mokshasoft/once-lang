-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Verified.Behavior — WHAT THIS COMPILER CLAIMS
--
-- ╔══════════════════════════════════════════════════════════════════╗
-- ║  CRITICAL READING NOTE — DO NOT GET THIS WRONG.                  ║
-- ║                                                                  ║
-- ║  Once programs DO NOT RETURN A VALUE.                            ║
-- ║                                                                  ║
-- ║  `main : Eff Unit Unit` is fixed by `validateMain`. The trailing ║
-- ║  `Unit` is meaningless — there is nothing for a program to       ║
-- ║  return because there is no caller above `main`. What a program  ║
-- ║  *does* is INVOKE SIGNATURE OPERATIONS (SigOps): `linux.exit`,   ║
-- ║  `linux.write`, `arith.add.int`, etc. The observable behaviour   ║
-- ║  is THE SEQUENCE OF SIGOP CALLS the program performs and their  ║
-- ║  arguments — i.e. an EFFECT TRACE.                               ║
-- ║                                                                  ║
-- ║  The exit code (Layer 0's only observable) is not a "return      ║
-- ║  value." It is *the argument* to the program's final             ║
-- ║  `linux.exit` SigOp call. There is no other channel by which     ║
-- ║  exit codes leave the program; "the program returns 42" is       ║
-- ║  shorthand for "the program calls `linux.exit 42`."              ║
-- ║                                                                  ║
-- ║  Anyone tempted to project a "return value" from `evalSurface`   ║
-- ║  is reading the semantics wrong. `evalSurface ε e : ⟦ T ⟧Type`   ║
-- ║  collapses effectful arrows to plain function arrows             ║
-- ║  (⟦ A ⇒[_] B ⟧ = ⟦ A ⟧ → ⟦ B ⟧); for `Eff Unit Unit` this is     ║
-- ║  `⊤ → ⊤`, which carries NO INFORMATION. The actual effect        ║
-- ║  semantics flows through `generic-semI`, which is the SigOp      ║
-- ║  dispatcher.                                                     ║
-- ║                                                                  ║
-- ║  Therefore `Behavior` MUST be effect-trace-shaped (or a          ║
-- ║  projection thereof), not "exit-code-shaped" thought of as a     ║
-- ║  return value.                                                   ║
-- ║                                                                  ║
-- ║  COMPILER CORRECTNESS IS TRACE PRESERVATION ONLY.                ║
-- ║                                                                  ║
-- ║  The compile-correct theorem says: the compiled bytes invoke    ║
-- ║  the same SigOp calls (same name, args, order) as the source    ║
-- ║  intends. It DOES NOT say anything about what those SigOp       ║
-- ║  calls *do* — whether `linux.exit` actually terminates, whether ║
-- ║  `linux.write` actually outputs bytes, etc. That is the         ║
-- ║  INTERPRETATION's responsibility, proven separately per SigOp   ║
-- ║  (or postulated by the Once programmer using their interpretation║
-- ║  layer in `Strata/Interpretations/...`).                         ║
-- ║                                                                  ║
-- ║  End-to-end behavioural correctness is the COMPOSITION of:       ║
-- ║    - compiler's trace preservation (this module)                 ║
-- ║    - interpretation's protocol conformance (separate, per impl) ║
-- ║                                                                  ║
-- ║  Don't conflate the two. Don't put protocol obligations on the   ║
-- ║  compiler. Don't put trace obligations on the interpretation.    ║
-- ╚══════════════════════════════════════════════════════════════════╝
--
-- For Layer 0 the only SigOp a program can call is `linux.exit`,
-- so the trace is always `[("linux.exit", N)]`. The argument N is
-- what humans call "the exit code." We could pick any of these
-- equivalent shapes for `Behavior`:
--
--   (a) `Behavior = List SigOpEvent`
--       — the full trace; richest, future-proof for richer effects.
--   (b) `Behavior = Maybe ℕ`
--       — the argument of the final `linux.exit` event, or `nothing`
--         if the program didn't call exit. Coarser but matches what
--         Layer 0 cares about.
--
-- We pick (b) for Layer 0 since it's the smallest correct observable.
-- Layer-1+ work will widen to (a).
--
-- This is a CHOICE of observable, not a derived consequence of CCC
-- / structural-recursion laws. Those laws prove equalities between
-- source terms; this declares what counts as observably-equivalent
-- to the outside world.
------------------------------------------------------------------------

module Once.Verified.Behavior where

open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ)

import Once.Grammar as G

------------------------------------------------------------------------
-- Behavior — Layer 0 observable: the argument of the final
-- `linux.exit` SigOp call (if any). NOT a "return value."
------------------------------------------------------------------------

Behavior : Set
Behavior = Maybe ℕ

------------------------------------------------------------------------
-- Source — anchored at the formal grammar.
------------------------------------------------------------------------

Source : Set
Source = G.GModule

------------------------------------------------------------------------
-- ⟦_⟧ — extracts the `linux.exit` argument from a program's
-- effect-tree denotation. Postulated until the connector to the
-- effect-tracking interpreter lands.
--
-- IMPORTANT: this CANNOT be `extract-from-evalSurface ∘ evalSurface ε`
-- because `evalSurface` flattens `Eff Unit Unit` to `⊤ → ⊤` and
-- discards SigOp arguments via the postulated `generic-semI`.
-- Discharging this requires a richer effect-tracking interpreter
-- (free monad over SigOp, or similar) — substantive new work,
-- NOT just connector plumbing.
------------------------------------------------------------------------

postulate
  ⟦_⟧ : Source → Behavior
