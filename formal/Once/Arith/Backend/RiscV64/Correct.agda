-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Arith.Backend.RiscV64.Correct
--
-- Plan 0.53 — riscv64 instantiation of the shared width-parametric
-- refinement scaffold (`Once.Arith.Backend.Correct`) at width 64.
--
-- Like x86-32, riscv64 previously had no refinement module. It is now
-- covered: `step` compares at width 64 and the concrete machine
-- (postulated until discharge) reuses `Once.CCC.Target.RiscV64.Semantics`.
-- Distinct from x86-64's machine despite the shared width 64 — hence the
-- machine is an explicit parameter of the shared scaffold, not baked in.
------------------------------------------------------------------------

module Once.Arith.Backend.RiscV64.Correct where

open import Once.Arith.Machine.AbsState using (ArithAbsState; InputShape)
open import Once.Arith.Backend.XInstr.Syntax using (XProgram)

-- riscv64 concrete machine (SCAFFOLD — postulated until discharge).
postulate
  XState     : InputShape → Set
  concretise : ∀ {sh} → ArithAbsState sh → XState sh
  exec-x86   : ∀ {sh} → XProgram → XState sh → XState sh

-- riscv64 word width = 64. Instantiate the shared scaffold; re-export
-- `refine` + the per-ctor obligations.
open import Once.Arith.Backend.Correct 64 XState concretise exec-x86 public
