-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Verified.CPU.RiscV64 — RiscV64 ArchSemantics instance
--
-- Wires the existing `Once.CCC.Target.RiscV64.Semantics` (clean
-- step / exec / run shape, RISC-V ISA Manual conformance) into the
-- portable `ArchSemantics` interface.
--
-- Concrete fields (no postulates, real ISA semantics):
--   - Program      = List Instr  (from Once.CCC.Target.RiscV64.Syntax)
--   - State        = the existing record (regs, memory, pc, halted)
--   - initialState = RV.Semantics.initState
--   - run          = RV.Semantics.run  ← THE TRUST POINT.
--                    Reviewers verify each clause of `run` (which calls
--                    `step` → `execInstr`) against the RISC-V ISA Manual.
--
-- Postulated bridges (will be discharged):
--   - observe  : Maybe State → Behavior   (waiting for `Behavior`)
--   - decode   : List Byte → Maybe Program (byte-encoding of Instr)
------------------------------------------------------------------------

module Once.Verified.CPU.RiscV64 where

open import Data.List using (List)
open import Data.Maybe using (Maybe)

open import Once.Verified.Behavior      using (Behavior)
open import Once.Verified.CPU.Interface  using (Byte; ArchSemantics)

import Once.CCC.Target.RiscV64.Semantics as RV
import Once.CCC.Target.RiscV64.Syntax    as RVS

postulate
  -- Decode raw bytes into a structured RISC-V program. Discharge:
  -- a concrete instruction-encoding function per the RISC-V manual's
  -- 32-bit instruction format, then a list-decoder that consumes
  -- 4-byte chunks until exhausted (or fails on malformed bytes).
  decode-riscv64 : List Byte → Maybe RVS.Program

  -- Project a final State to the universal Behavior. Discharge:
  -- once `Behavior` becomes concrete (Plan 0.4.2), this reads the
  -- exit code (or syscall trace) from the State and produces the
  -- corresponding Behavior value.
  observe-riscv64 : Maybe RV.State → Behavior

------------------------------------------------------------------------
-- The instance.
------------------------------------------------------------------------

arch-semantics : ArchSemantics
arch-semantics = record
  { Program      = RVS.Program
  ; State        = RV.State
  ; initialState = RV.initState
  ; run          = RV.run
  ; observe      = observe-riscv64
  ; decode       = decode-riscv64
  }
