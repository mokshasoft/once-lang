-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Verified.CPU.X86-32 — X86-32 ArchSemantics instance
--
-- Same pattern as RiscV64 / X86-64: wires the simple-shape semantics
-- into the portable `ArchSemantics` interface. Trust point is the
-- body of `X86-32.Semantics.execInstr`.
------------------------------------------------------------------------

module Once.Verified.CPU.X86-32 where

open import Data.List using (List)
open import Data.Maybe using (Maybe)
open import Data.String using (String)

open import Once.Verified.Behavior      using (Behavior)
open import Once.Verified.CPU.Interface using (Byte; ArchSemantics)

import Once.CCC.Target.X86-32.Semantics as X32
import Once.CCC.Target.X86-32.Syntax    as X32S

------------------------------------------------------------------------
-- Postulated gaps (named).
------------------------------------------------------------------------

postulate
  -- run-trace-x86-32 — the OBSERVABLE (Plan 0.44): step-indexed SigOp
  -- trace of executing `prog`. Replaces the value-shaped `observe`
  -- (final `%ebx` exit code). Derived from X32.run's step semantics once
  -- syscalls emit-and-continue; postulated until then.
  run-trace-x86-32 : X32S.Program → X32.State → Behavior
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
