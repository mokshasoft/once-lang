-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.CPU.X86-32 — X86-32 ArchSemantics instance
--
-- Same pattern as RiscV64 / X86-64: wires the simple-shape semantics
-- into the portable `ArchSemantics` interface. Trust point is the
-- body of `X86-32.Semantics.execInstr`.
------------------------------------------------------------------------

module Once.Adequacy.CPU.X86-32 where

open import Data.List using (List)
open import Data.Maybe using (Maybe)
open import Data.String using (String)
open import Data.Nat using (ℕ)

open import Once.Denotation.Behavior      using (Behavior)
open import Once.Adequacy.CPU.Interface using (Byte; ArchSemantics)

import Once.CCC.Target.X86-32.Semantics as X32
import Once.CCC.Target.X86-32.Syntax    as X32S

-- Plan 0.54 Phase B / Option 2: the emit-and-continue trace over the REAL
-- x86-32 machine, instanced from `Arith.Backend.RunTraceCore` like x86-64/riscv64.
-- DERIVES `run-trace` from `X32.run`'s step semantics, replacing the old opaque
-- observable postulate with the real machine + three small named sub-gaps.
import Once.Arith.Backend.X86-32.RunTrace as RT
open import Once.Adequacy.ArchCorrectness.ArithSimX86-32 using (val-x86-32)

------------------------------------------------------------------------
-- run-trace-x86-32 — DERIVED (no longer an opaque observable postulate). Its
-- remaining ingredients are the SAME named gaps x86-64/riscv64 carry:
--   * `val-x86-32`        — the concrete XInstr arith interpreter (DEFINED).
--   * `arith-env-x86-32`  — the arith-block table (label ↦ block).
--   * `ev-x86-32`         — label→SigOp resolution (inverse of symbol lowering).
--   * `step-budget-x86-32`— adequate fuel (event-count ↦ machine steps).
------------------------------------------------------------------------

postulate
  step-budget-x86-32 : ℕ → ℕ
  ev-x86-32          : RT.EvExtractor val-x86-32
  arith-env-x86-32   : X32S.Program → RT.ArithEnv val-x86-32

run-trace-x86-32 : X32S.Program → X32.State → Behavior
run-trace-x86-32 prog s =
  RT.run-trace val-x86-32 step-budget-x86-32 ev-x86-32 (arith-env-x86-32 prog) prog s

postulate
  decode-x86-32 : List Byte → Maybe X32S.Program
  -- GNU `as --target=x86-32` trust point; removed by B1.
  assemble-x86-32 : String → List Byte

arch-semantics : ArchSemantics
arch-semantics = record
  { Program      = X32S.Program
  ; State        = X32.State
  ; initialState = X32.initState
  ; run          = X32.run
  ; run-trace    = run-trace-x86-32
  ; decode       = decode-x86-32
  ; assemble     = assemble-x86-32
  }
