-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Inspect — what the CLI's inspection commands print: `parse`
-- (signatures), `check`, `elaborate` and `optimize` (each function's IR).
--
-- A tool beside the compiler, as `Once.Format` and `Once.Measure` are
-- (D352): each command is one pure function over the resolved module, and the
-- compiler does not import this module. The IR shown is `compileResolvedModule`'s
-- in `Heap`, the IR the build emits (`Once.Inspect.Proof.build-factors`).
------------------------------------------------------------------------

module Once.Inspect where

open import Data.Bool using (Bool; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.String using (String; _++_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)

open import Once.IR using (Heap)
open import Once.IR.Show using (showIR)
open import Once.Name using (showCanonical)
open import Once.Type using (showType; showPolyType)
open import Once.Compile using (CompiledFun; compileResolvedModule)
open import Once.Parser using (Entry; FunInfo; PolyFunInfo; funsOf; polysOf; extractFunctions)
open import Once.Parser.Module.Core using (Resolved)

------------------------------------------------------------------------
-- `parse`: the declarations the typechecker sees, after resolution

-- | `name : type`, one per line; `<inferred>` for a definition without one.
showFunInfo : FunInfo → String
showFunInfo fi with FunInfo.funType fi
... | just ty = FunInfo.funName fi ++ " : " ++ showType ty ++ "\n"
... | nothing = FunInfo.funName fi ++ " : <inferred>\n"

showPolyFunInfo : PolyFunInfo → String
showPolyFunInfo pfi = PolyFunInfo.pfunName pfi ++ " : " ++ showPolyType (PolyFunInfo.pfunType pfi) ++ "\n"

private
  showFuns : List FunInfo → String
  showFuns []         = ""
  showFuns (fi ∷ fis) = showFunInfo fi ++ showFuns fis

  showPolys : List PolyFunInfo → String
  showPolys []           = ""
  showPolys (pfi ∷ pfis) = showPolyFunInfo pfi ++ showPolys pfis

  showEntries : String ⊎ List Entry → String ⊎ String
  showEntries (inj₁ err) = inj₁ err
  showEntries (inj₂ es)  = inj₂ (showFuns (funsOf es) ++ showPolys (polysOf es))

-- | The ground signatures, then the polymorphic ones, or the error.
signatures : Resolved → String ⊎ String
signatures mod = showEntries (extractFunctions mod)

------------------------------------------------------------------------
-- `check`: the module typechecks (and elaborates) or the error

accepted : String ⊎ List CompiledFun → String ⊎ ⊤
accepted (inj₁ err) = inj₁ err
accepted (inj₂ _)   = inj₂ tt

-- | Typing does not depend on the target; whether a literal fits does, and that
-- is `build`'s to refuse (`Compile.litRangeError`).
check : Resolved → String ⊎ ⊤
check mod = accepted (compileResolvedModule Heap false mod)

------------------------------------------------------------------------
-- `elaborate` (`doOpt = false`) and `optimize` (`doOpt = true`)

-- | `name : type` and the body on the next line.
showCompiledFun : CompiledFun → String
showCompiledFun cf =
  showCanonical (CompiledFun.cfName cf) ++ " : " ++ showType (CompiledFun.cfType cf) ++ "\n  = "
    ++ showIR (CompiledFun.cfIR cf) ++ "\n"

showCompiledFuns : List CompiledFun → String
showCompiledFuns []         = ""
showCompiledFuns (cf ∷ cfs) = showCompiledFun cf ++ showCompiledFuns cfs

showCompiled : String ⊎ List CompiledFun → String ⊎ String
showCompiled (inj₁ err) = inj₁ err
showCompiled (inj₂ cfs) = inj₂ (showCompiledFuns cfs)

-- | The module's functions, unoptimized or optimized, or the error.
dumpIR : Bool → Resolved → String ⊎ String
dumpIR doOpt mod = showCompiled (compileResolvedModule Heap doOpt mod)
