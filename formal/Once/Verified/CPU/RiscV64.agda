-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Verified.CPU.RiscV64 — RiscV64 ArchSemantics instance
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

module Once.Verified.CPU.RiscV64 where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)

open import Once.Verified.Behavior      using (Behavior)
open import Once.Verified.CPU.Interface using (Byte; ArchSemantics)

import Once.CCC.Target.RiscV64.Semantics as RV
import Once.CCC.Target.RiscV64.Syntax    as RVS

------------------------------------------------------------------------
-- observe-riscv64 — concrete.
--
-- RISC-V Linux ABI: `exit N` puts N in `a0` (return-value register)
-- then invokes the exit syscall. After halt, `a0` holds the exit
-- code.
------------------------------------------------------------------------

observe-riscv64 : Maybe RV.State → Behavior
observe-riscv64 nothing  = nothing
observe-riscv64 (just s) with RV.State.halted s
... | false = nothing
... | true  = just (RV.readReg (RV.State.regs s) RVS.a0)

------------------------------------------------------------------------
-- decode-riscv64 — POSTULATED. The RISC-V instruction encoding (32
-- bits per instruction in the base ISA) is straightforward but
-- mechanical work; left as a named gap for now.
------------------------------------------------------------------------

postulate
  decode-riscv64 : List Byte → Maybe RVS.Program

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
