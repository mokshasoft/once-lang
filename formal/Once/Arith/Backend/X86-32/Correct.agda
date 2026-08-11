-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.Backend.X86-32.Correct
--
-- Plan 0.54 — X86-32 instantiation of the shared width-parametric,
-- PROVEN refinement module (`Once.Arith.Backend.Correct`) at width 32.
-- Re-exports the proven concrete machine (`exec-x86`), the discharged
-- `refine`/`refine-program`, and `block-correct` — no postulates.
------------------------------------------------------------------------

module Once.Arith.Backend.X86-32.Correct where

open import Once.Arith.Backend.Correct 32 public
