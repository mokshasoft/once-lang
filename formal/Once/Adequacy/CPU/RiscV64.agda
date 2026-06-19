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

open import Once.Denotation.Behavior      using (Behavior)
open import Once.Adequacy.CPU.Interface using (Byte; ArchSemantics)

import Once.CCC.Target.RiscV64.Semantics as RV
import Once.CCC.Target.RiscV64.Syntax    as RVS

------------------------------------------------------------------------
-- Postulated gaps (named).
------------------------------------------------------------------------

postulate
  -- run-trace-riscv64 — the OBSERVABLE (Plan 0.44): step-indexed SigOp
  -- trace of executing `prog`. Replaces the value-shaped `observe`
  -- (final `a0` exit code). Derived from RV.run's step semantics once
  -- syscalls emit-and-continue; postulated until then.
  run-trace-riscv64 : RVS.Program → RV.State → Behavior
  -- decode-riscv64 — POSTULATED. The RISC-V instruction encoding (32
  -- bits per instruction in the base ISA) is straightforward but
  -- mechanical work; left as a named gap for now.
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
