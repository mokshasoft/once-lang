-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Compiler — ASSEMBLY POINT
--
-- This module wires together:
--   - the abstract spec     (`Once.Verified`)
--   - the meaning           (`Once.Verified.Behavior`)
--   - the trusted CPU base  (`Once.Verified.CPU`)
--   - the proof + compile   (`Once.Verified.Compile`)
--
-- and constructs a single `CorrectCompiler` value the CLI consumes.
-- This file should be one record literal — no logic, no postulates
-- of its own. If the assembly typechecks, the compiler is correct
-- (modulo the postulates listed in the participating modules).
------------------------------------------------------------------------

module Once.Compiler where

open import Data.List using (List)

open import Once.Verified
open import Once.Verified.Behavior using (Source; Behavior; ⟦_⟧)
open import Once.Verified.CPU      using (Arch; Byte; exec)
open import Once.Verified.Compile  using (compile; correct)

once-compiler : CorrectCompiler
once-compiler = record
  { Arch     = Arch
  ; Source   = Source
  ; Bytes    = List Byte
  ; Behavior = Behavior
  ; ⟦_⟧      = ⟦_⟧
  ; exec     = exec
  ; compile  = compile
  ; correct  = correct
  }
