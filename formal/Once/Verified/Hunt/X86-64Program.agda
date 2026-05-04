-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Verified.Hunt.X86-64Program
--
-- Bridges the existing pipeline to a structured X86-64 Program (List
-- Instr) — bypassing the asm-text/bytes layer. This lets us run the
-- output of `compile` directly on our Once.CCC.Target.X86-64.Semantics
-- (the simple-shape `step / exec / run` we restored), with no
-- assembler trust in the chain.
--
-- Purpose: hunt the closure-codegen bug at a level our semantics can
-- model. The bug — compose returning a stack pointer that's freed by
-- the next `leave; ret` — IS visible at the structured X86 Program
-- level (memory + rsp + frame discipline are all modelled). It is
-- NOT visible at higher abstractions (where eval gives `tt : ⊤` for
-- effectful programs and "Represents tt" is trivially true).
--
-- Pipeline:
--   GModule → Module (postulated converter)
--          → [CompiledFun] (Once.Compile.compileAllFuns + extract decls)
--          → IR per fun
--          → X86 Program (Once.CCC.Target.X86-64.CodeGen.compile-ir)
--          → concatenated Program
------------------------------------------------------------------------

module Once.Verified.Hunt.X86-64Program where

open import Data.Bool using (Bool; false; true)
open import Data.List using (List; []; _∷_; _++_; foldr)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String)

open import Once.Verified.Behavior using (Source)

import Once.Compile as C
import Once.Grammar as G
import Once.Parser.Module.Core as P
import Once.CCC.Target.X86-64.Syntax as X64S
import Once.CCC.Target.X86-64.CodeGen.Compile as X64Codegen

-- Reuse the postulated GModule → Module converter from Verified.Compile.
open import Once.Verified.Compile using (gmoduleToModule)

------------------------------------------------------------------------
-- Per-function compiler: CompiledFun → X86 Program.
-- Skips primitives (their bodies live in Strata/Interpretations).
------------------------------------------------------------------------

compile-fun-to-program : C.CompiledFun → X64S.Program
compile-fun-to-program cf with C.CompiledFun.cfIsPrimitive cf
... | true  = []                                            -- primitive: no body
... | false = X64Codegen.compile-ir (C.CompiledFun.cfIR cf)

------------------------------------------------------------------------
-- Concatenate per-function programs.
------------------------------------------------------------------------

concat-programs : List C.CompiledFun → X64S.Program
concat-programs = foldr (λ cf p → compile-fun-to-program cf ++ p) []

------------------------------------------------------------------------
-- Top-level: GModule → X86 Program (or `nothing` if compilation fails).
------------------------------------------------------------------------

postulate
  -- Extract [CompiledFun] from a Module without going to asm text.
  -- compileFromModule's interior already does this; we expose the
  -- intermediate here. Discharge: factor `compileFromModule`'s body
  -- so this projection is a real definition.
  compileFromModuleToFuns : P.Module → String ⊎ List C.CompiledFun

compile-to-x86-program : Source → Maybe X64S.Program
compile-to-x86-program gmod with gmoduleToModule gmod
... | nothing = nothing
... | just m  with compileFromModuleToFuns m
...   | inj₁ _    = nothing
...   | inj₂ funs = just (concat-programs funs)
