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

open import Data.Bool using (Bool; true; false)
open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)

open import Once.Verified.Behavior      using (Behavior)
open import Once.Verified.CPU.Interface using (Byte; ArchSemantics)

import Once.CCC.Target.X86-32.Semantics as X32
import Once.CCC.Target.X86-32.Syntax    as X32S

------------------------------------------------------------------------
-- observe-x86-32 — concrete.
--
-- Linux i386 syscall ABI: `exit N` puts N in `%ebx` then invokes
-- int 0x80 / sysenter. After halt, `%ebx` holds the exit code.
-- Our `call-sym "linux.exit"` halts; whatever was in ebx is the
-- exit code.
------------------------------------------------------------------------

observe-x86-32 : Maybe X32.State → Behavior
observe-x86-32 nothing  = nothing
observe-x86-32 (just s) with X32.State.halted s
... | false = nothing
... | true  = just (X32.readReg (X32.State.regs s) X32S.ebx)

postulate
  decode-x86-32 : List Byte → Maybe X32S.Program

arch-semantics : ArchSemantics
arch-semantics = record
  { Program      = X32S.Program
  ; State        = X32.State
  ; initialState = X32.initState
  ; run          = X32.run
  ; observe      = observe-x86-32
  ; decode       = decode-x86-32
  }
