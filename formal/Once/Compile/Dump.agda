-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Compile.Dump — EACH COMPILED FUNCTION'S IR, as the CLI's
-- `elaborate` (`doOpt = false`) and `optimize` (`doOpt = true`) stages print
-- it (plan 0.39).
--
-- The functions are `compileResolvedModule`'s, the ones the build compiles:
-- with `doOpt` each body is the optimized one (`OptimizedModule.crm-opt`).
------------------------------------------------------------------------

module Once.Compile.Dump where

open import Data.Bool using (Bool)
open import Data.List using (List; []; _∷_)
open import Data.String using (String; _++_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Once.IR using (Heap)
open import Once.IR.Show using (showIR)
open import Once.Name using (showCanonical)
open import Once.Type using (showType)
open import Once.Compile using (CompiledFun; compileResolvedModule)
open import Once.Parser.Module.Core using (Resolved)

-- | `name : type` and the body on the next line.
showCompiledFun : CompiledFun → String
showCompiledFun cf =
  showCanonical (CompiledFun.cfName cf) ++ " : " ++ showType (CompiledFun.cfType cf) ++ "\n  = "
    ++ showIR (CompiledFun.cfIR cf) ++ "\n"

private
  showAll : List CompiledFun → String
  showAll []         = ""
  showAll (cf ∷ cfs) = showCompiledFun cf ++ showAll cfs

-- | The module's functions, unoptimized or optimized, or the error.
dumpIR : Bool → Resolved → String ⊎ String
dumpIR doOpt mod with compileResolvedModule Heap doOpt mod
... | inj₁ err = inj₁ err
... | inj₂ cfs = inj₂ (showAll cfs)
