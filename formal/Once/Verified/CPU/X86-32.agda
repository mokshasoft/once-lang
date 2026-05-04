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

open import Once.Verified.Behavior      using (Behavior)
open import Once.Verified.CPU.Interface using (Byte; ArchSemantics)

import Once.CCC.Target.X86-32.Semantics as X32
import Once.CCC.Target.X86-32.Syntax    as X32S

postulate
  decode-x86-32  : List Byte → Maybe X32S.Program
  observe-x86-32 : Maybe X32.State → Behavior

arch-semantics : ArchSemantics
arch-semantics = record
  { Program      = X32S.Program
  ; State        = X32.State
  ; initialState = X32.initState
  ; run          = X32.run
  ; observe      = observe-x86-32
  ; decode       = decode-x86-32
  }
