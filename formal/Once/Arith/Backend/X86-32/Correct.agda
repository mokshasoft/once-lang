-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Arith.Backend.X86-32.Correct
--
-- Plan 0.53 — x86-32 instantiation of the shared width-parametric
-- refinement scaffold (`Once.Arith.Backend.Correct`) at width 32.
--
-- Before the split this arch had NO refinement module at all (the sole
-- `Correct` opened `Exec 64`), so the 32-bit arith path was outside even
-- the postulated obligation. It is now covered on the same footing as
-- x86-64/riscv64: `step` compares at width 32, and the concrete machine
-- (postulated until discharge) reuses `Once.CCC.Target.X86-32.Semantics`.
------------------------------------------------------------------------

module Once.Arith.Backend.X86-32.Correct where

open import Once.Arith.Machine.AbsState using (ArithAbsState; InputShape)
open import Once.Arith.Backend.XInstr.Syntax using (XProgram)

-- x86-32 concrete machine (SCAFFOLD — postulated until discharge).
postulate
  XState     : InputShape → Set
  concretise : ∀ {sh} → ArithAbsState sh → XState sh
  exec-x86   : ∀ {sh} → XProgram → XState sh → XState sh

-- x86-32 word width = 32. Instantiate the shared scaffold; re-export
-- `refine` + the per-ctor obligations.
open import Once.Arith.Backend.Correct 32 XState concretise exec-x86 public
