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
open import Data.String using (String)

open import Once.Verified.Behavior      using (Behavior)
open import Once.Verified.CPU.Interface using (Byte; ArchSemantics)

import Once.CCC.Target.X86-64.Semantics as X64
import Once.CCC.Target.X86-64.Syntax    as X64S

------------------------------------------------------------------------
-- Postulated gaps (named, alongside the existing decode/assemble ones).
------------------------------------------------------------------------

postulate
  -- run-trace-x86-64 — the OBSERVABLE (Plan 0.44): the step-indexed SigOp
  -- trace produced by executing `prog` from `state`. Replaces the old
  -- value-shaped `observe` (final `%rdi` at halt — an exit code, which
  -- cannot represent a multi-SigOp trace). To be DERIVED from `X64.run`'s
  -- step semantics once syscall/call-sym record the invocation and
  -- continue (the emit-and-continue machine); postulated until then.
  run-trace-x86-64 : X64S.Program → X64.State → Behavior

  -- decode-x86-64 — POSTULATED. Concrete byte-encoder/decoder per the
  -- Intel SDM is significant work; left as a named gap for now.
  decode-x86-64 : List Byte → Maybe X64S.Program

  -- assemble-x86-64 — POSTULATED. GNU `as --target=x86-64` trust point;
  -- removed when the in-Agda assembler (B1) lands.
  assemble-x86-64 : String → List Byte

------------------------------------------------------------------------
-- The instance.
------------------------------------------------------------------------

arch-semantics : ArchSemantics
arch-semantics = record
  { Program      = X64S.Program
  ; State        = X64.State
  ; initialState = X64.initState
  ; run          = X64.run
  ; run-trace    = run-trace-x86-64
  ; decode       = decode-x86-64
  ; assemble     = assemble-x86-64
  }
