-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.CPU.RiscV64 — RiscV64 ArchSemantics instance
--
-- Wires the existing `Once.CCC.Target.RiscV64.Semantics` (clean
-- step / exec / run shape, RISC-V ISA Manual conformance) into the
-- portable `ArchSemantics` interface.
--
-- Concrete fields:
--   - Program      = List Instr  (from Once.CCC.Target.RiscV64.Syntax)
--   - State        = the existing record (regs, memory, pc, halted)
--   - initialState = RV.Semantics.initState
--   - run          = RV.Semantics.run  ← THE TRUST POINT.
--                    Reviewers verify each clause of `run` (which calls
--                    `step` → `execInstr`) against the RISC-V ISA Manual.
--   - observe      = read exit code from `a0` after halt.
--
-- Postulated:
--   - decode   : byte-encoding-of-Instr decoder.
------------------------------------------------------------------------

module Once.Adequacy.CPU.RiscV64 where

open import Data.List using (List)
open import Data.Maybe using (Maybe)
open import Data.String using (String)
open import Data.Nat using (ℕ)

open import Once.Denotation.Behavior      using (Behavior)
open import Once.Adequacy.CPU.Interface using (Byte; ArchSemantics)

import Once.CCC.Target.RiscV64.Semantics as RV
import Once.CCC.Target.RiscV64.Syntax    as RVS

-- Plan 0.54 Phase B / Option 2: the emit-and-continue trace over the REAL
-- riscv64 machine (arith blocks dispatched, Pure ⇒ no event), instanced from
-- the arch-generic `Arith.Backend.RunTraceCore` exactly like x86-64. This
-- DERIVES `run-trace` from `RV.run`'s step semantics, replacing the old opaque
-- observable postulate with the real machine + three small named sub-gaps.
import Once.Arith.Backend.RiscV64.RunTrace as RT
open import Once.Adequacy.ArchCorrectness.ArithSimRiscV64 using (val-riscv64)

------------------------------------------------------------------------
-- run-trace-riscv64 — DERIVED (no longer an opaque observable postulate).
-- Its remaining ingredients are the SAME named gaps x86-64 carries:
--   * `val-riscv64`        — the concrete XInstr arith interpreter (DEFINED).
--   * `arith-env-riscv64`  — the arith-block table (label ↦ block × N),
--                            recoverable from the compiled program.
--   * `ev-riscv64`         — label→SigOp resolution (the inverse of the
--                            per-arch symbol lowering; correctness = conc-flat-sim).
--   * `step-budget-riscv64`— adequate fuel (event-count ↦ machine steps).
------------------------------------------------------------------------

postulate
  step-budget-riscv64 : ℕ → ℕ
  ev-riscv64          : RT.EvExtractor val-riscv64
  arith-env-riscv64   : RVS.Program → RT.ArithEnv val-riscv64

run-trace-riscv64 : RVS.Program → RV.State → Behavior
run-trace-riscv64 prog s =
  RT.run-trace val-riscv64 step-budget-riscv64 ev-riscv64 (arith-env-riscv64 prog) prog s

postulate
  -- decode-riscv64 — POSTULATED. The RISC-V instruction encoding (32
  -- bits per instruction in the base ISA) is straightforward but
  -- mechanical work; left as a named gap for now (closed by B1).
  decode-riscv64 : List Byte → Maybe RVS.Program
  -- GNU `as` (RISC-V) trust point; removed by B1.
  assemble-riscv64 : String → List Byte

------------------------------------------------------------------------
-- The instance.
------------------------------------------------------------------------

arch-semantics : ArchSemantics
arch-semantics = record
  { Program      = RVS.Program
  ; State        = RV.State
  ; initialState = RV.initState
  ; run          = RV.run
  ; run-trace    = run-trace-riscv64
  ; decode       = decode-riscv64
  ; assemble     = assemble-riscv64
  }
