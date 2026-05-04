-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Verified.CPU.X86-64 — X86-64 ArchSemantics instance
--
-- Wires `Once.CCC.Target.X86-64.Semantics` (clean step / exec / run
-- shape, restored from history) into the portable `ArchSemantics`
-- interface.
--
-- Concrete fields (no postulates, real ISA semantics):
--   - Program      = List Instr  (from Once.CCC.Target.X86-64.Syntax)
--   - State        = the existing record (regs, memory, flags, pc, halted)
--   - initialState = X86-64.Semantics.initState
--   - run          = X86-64.Semantics.run  ← THE TRUST POINT.
--                    Reviewers verify each clause of `execInstr` against
--                    the Intel SDM.
--
-- Postulated bridges (will be discharged):
--   - observe  : Maybe State → Behavior   (waiting for `Behavior`)
--   - decode   : List Byte → Maybe Program (byte-encoding of Instr)
--
-- DirectSimulation remains the lower-level proof tool used to discharge
-- arch-specific lemmas about `run`.
------------------------------------------------------------------------

module Once.Verified.CPU.X86-64 where

open import Data.List using (List)
open import Data.Maybe using (Maybe)

open import Once.Verified.Behavior      using (Behavior)
open import Once.Verified.CPU.Interface using (Byte; ArchSemantics)

import Once.CCC.Target.X86-64.Semantics as X64
import Once.CCC.Target.X86-64.Syntax    as X64S

postulate
  -- Decode raw bytes into a structured x86-64 program. Discharge:
  -- a concrete instruction-encoding function per the Intel SDM,
  -- consuming variable-length opcodes until exhausted (or fails on
  -- malformed bytes).
  decode-x86-64 : List Byte → Maybe X64S.Program

  -- Project a final State to the universal Behavior. Discharge:
  -- once `Behavior` becomes concrete (Plan 0.4.2), this reads the
  -- exit code (or syscall trace) from the State and produces the
  -- corresponding Behavior value.
  observe-x86-64 : Maybe X64.State → Behavior

------------------------------------------------------------------------
-- The instance.
------------------------------------------------------------------------

arch-semantics : ArchSemantics
arch-semantics = record
  { Program      = X64S.Program
  ; State        = X64.State
  ; initialState = X64.initState
  ; run          = X64.run
  ; observe      = observe-x86-64
  ; decode       = decode-x86-64
  }
