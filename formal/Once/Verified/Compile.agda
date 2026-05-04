-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Verified.Compile — the compile function + correctness witness.
--
-- Wires `Once.Compile.compileFromModule` (the existing pipeline)
-- into the verified type. Concrete `compile` body: convert the
-- `GModule` source to the parser's `Module` type, dispatch to
-- `compileFromModule` for the Build stage, project the assembly
-- bytes from the result.
--
-- `correct` is still postulated wholesale — discharging it is the
-- substantive proof work that surfaces codegen bugs (the closure
-- bug for `(id . id . id) 42` will surface here).
------------------------------------------------------------------------

module Once.Verified.Compile where

open import Data.Bool using (Bool; false)
open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Verified.Behavior using (Source; Behavior; ⟦_⟧)
open import Once.Verified.CPU      using (Arch; Byte; exec)
open import Once.Verified.CPU      using () renaming
  (x86-64 to Va-x86-64; x86-32 to Va-x86-32; riscv64 to Va-riscv64)

import Once.Compile as C
import Once.Grammar as G
import Once.Parser.Module.Core as P

------------------------------------------------------------------------
-- Connectors
------------------------------------------------------------------------

-- Architecture coercion. The two `Arch` types are structurally
-- identical but live in different modules.
toLegacyArch : Arch → C.Arch
toLegacyArch Va-x86-64  = C.x86-64
toLegacyArch Va-x86-32  = C.x86-32
toLegacyArch Va-riscv64 = C.riscv64

postulate
  -- GModule (formal grammar) → Module (parser output type with
  -- RawExpr / PolyType). Discharge: a structural conversion using
  -- the `gexprToRaw` family from `Once.Grammar.ExprConvert` plus
  -- a Decl-level walker. Same direction as the existing parser's
  -- `parse : String → Maybe Module` (which side-steps GModule today).
  gmoduleToModule : G.GModule → Maybe P.Module

  -- ╔══════════════════════════════════════════════════════════════╗
  -- ║ TRUSTED BASE — current B2 stance.                            ║
  -- ║                                                              ║
  -- ║ `string-to-bytes` is THE GNU assembler trust postulate. We  ║
  -- ║ trust that the asm text produced by `compileFromModule`,    ║
  -- ║ when fed to GNU `as`, yields bytes whose CPU execution      ║
  -- ║ matches running our structured-Program model on the same    ║
  -- ║ instructions.                                                ║
  -- ║                                                              ║
  -- ║ This is the deliberately-chosen B2 stance: practical now,   ║
  -- ║ replaceable by an in-Agda assembler (B1) without spec       ║
  -- ║ changes — the postulate goes away, nothing else.             ║
  -- ║                                                              ║
  -- ║ One axiom per arch eventually (linker conformance is        ║
  -- ║ separate). For now, single string-to-bytes covers all       ║
  -- ║ arches uniformly through the asm-text intermediate.          ║
  -- ╚══════════════════════════════════════════════════════════════╝
  string-to-bytes : String → List Byte

------------------------------------------------------------------------
-- The compile function — concrete body via the existing pipeline.
------------------------------------------------------------------------

compile : Arch → Source → Maybe (List Byte)
compile arch gmod with gmoduleToModule gmod
... | nothing = nothing
... | just m  with C.compileFromModule C.Build false (toLegacyArch arch) m
...   | C.Built asm = just (string-to-bytes asm)
...   | _           = nothing

------------------------------------------------------------------------
-- CLI entry point — asm-producing variant (B2 pragmatic path).
--
-- CLI/Bridge.hs currently consumes asm text (passed to GNU `as`),
-- not raw bytes. Until we have an in-Agda assembler (B1), the CLI
-- path goes through this asm-producing function which delegates to
-- the same underlying `compileFromModule` pipeline.
--
-- This function is THE function CLI must call (Plan 0.10 — extracted
-- = verified). The bytes-producing `compile` above remains the
-- spec-side anchor; the link between them is `string-to-bytes`,
-- which is the assembler trust postulate (B2's irreducible item).
------------------------------------------------------------------------

compile-asm : Arch → Source → C.CompileResult
compile-asm arch gmod with gmoduleToModule gmod
... | nothing = C.Error "GModule → Module conversion failed"
... | just m  = C.compileFromModule C.Build false (toLegacyArch arch) m

-- Module-input variant for the CLI/Bridge path. The CLI parses
-- source text to a `Module` (via Once.Parser.parseStrict / equivalent)
-- and calls this function to get assembly. Architecturally identical
-- to going through compile-asm; the GModule round-trip is skipped
-- since the parser already produced the typed-pipeline `Module`.
--
-- This is THE function Bridge.hs must call (Plan 0.10).
compile-cli-asm : C.Stage → Bool → Arch → P.Module → C.CompileResult
compile-cli-asm stage doOpt arch m =
  C.compileFromModule stage doOpt (toLegacyArch arch) m

------------------------------------------------------------------------
-- Correctness — POSTULATED. Discharging this is the substantive
-- proof work; it forces codegen bugs to surface as proof failures.
-- For programs with escaping closures (the `(id . id . id) 42`
-- pattern), the proof obligation cannot be filled with the current
-- codegen — that's how the architecture catches the closure bug.
------------------------------------------------------------------------

postulate
  correct :
    ∀ (arch : Arch) (src : Source) (bytes : List Byte) →
    compile arch src ≡ just bytes →
    exec arch bytes ≡ ⟦ src ⟧
