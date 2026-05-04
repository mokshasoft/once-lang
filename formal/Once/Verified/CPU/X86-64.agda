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

open import Data.Bool using (Bool; true; false)
open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)

open import Once.Verified.Behavior      using (Behavior)
open import Once.Verified.CPU.Interface using (Byte; ArchSemantics)

import Once.CCC.Target.X86-64.Semantics as X64
import Once.CCC.Target.X86-64.Syntax    as X64S

------------------------------------------------------------------------
-- observe-x86-64 — concrete projection.
--
-- Linux/SysV calling convention: `exit N` puts N in `%rdi` then
-- invokes the `linux.exit` SigOp (which our abstract semantics
-- handles by halting). So at halt, `%rdi` holds the exit code.
--
-- Reads:
--   - `nothing`  if no final state (run failed / out of fuel)
--   - `nothing`  if halted = false (didn't terminate)
--   - `just (rdi-value)`  otherwise
------------------------------------------------------------------------

observe-x86-64 : Maybe X64.State → Behavior
observe-x86-64 nothing  = nothing
observe-x86-64 (just s) with X64.State.halted s
... | false = nothing
... | true  = just (X64.readReg (X64.State.regs s) X64S.rdi)

------------------------------------------------------------------------
-- decode-x86-64 — POSTULATED. Concrete byte-encoder/decoder per the
-- Intel SDM is significant work; left as a named gap for now.
------------------------------------------------------------------------

postulate
  decode-x86-64 : List Byte → Maybe X64S.Program

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
