-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Extract.Root — what the CLI runs, and nothing else: the root of the
-- MAlonzo extraction (`make malonzo`).
--
-- The CLI (`compiler/src/Once/Compile/Bridge.hs`) calls the compiler
-- (`Once.Compile`), the parser and the import resolver, the warnings, the type
-- printer, and the arithmetic IR its evaluator reads, through the stable names
-- of `Once.Extract.Names`. The correctness theorem about these functions
-- (`Once.Certified`) and its proofs are not extracted: they are not run.
------------------------------------------------------------------------

module Once.Extract.Root where

import Once.Compile
import Once.IR
import Once.Target.Arch
import Once.Parser
import Once.Parser.Module.Core
import Once.Parser.Module.Resolve
import Once.Type
import Once.Warnings
import Once.Extract.Names
import Once.Arith.IR
import Once.Arith.Type
import Once.Format
import Once.Compile.Dump
