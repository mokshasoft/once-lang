-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Extract.Root — what the CLI runs, and nothing else: the root of the
-- MAlonzo extraction (`make malonzo`).
--
-- The CLI calls exactly the fields of `runs` (below): the front end, the
-- compiler, and the tools beside it — `Once.Inspect` (parse, check, elaborate,
-- optimize), `Once.Measure` (stats), `Once.Format` (fmt) — each through its own
-- Haskell bridge. The correctness theorem about these functions
-- (`Once.Certified`) and its proofs are not extracted: they are not run.
------------------------------------------------------------------------

module Once.Extract.Root where

open import Data.Bool using (Bool)
open import Data.List using (List)
open import Data.Maybe using (Maybe)
open import Data.Product using (_×_)
open import Data.String using (String)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤)

open import Once.Target.Arch using (Arch)
open import Once.Spec.Surface.Syntax using (Module)
open import Once.Parser.Module.Core using (Resolved)
open import Once.Parser.Module.Resolve using (ModuleMap)
import Once.Compile as Compile
import Once.Parser as Parser
import Once.Parser.Module.Core as Core
import Once.Parser.Module.Resolve as Resolve
import Once.Warnings as Warnings
import Once.Extract.Names as Names
import Once.Format as Format
import Once.Inspect as Inspect
import Once.Measure as Measure

-- The datatypes the Haskell side builds or reads directly (the arith IR the
-- test evaluator walks, the IR and type modules' constructors).
import Once.IR
import Once.Type
import Once.Arith.IR
import Once.Arith.Type

------------------------------------------------------------------------
-- WHAT RUNS (plan 0.132): every function the Haskell side calls, and nothing
-- else. The bridges (`Once.Compile.Bridge`, `Once.Inspect.Bridge`,
-- `Once.Measure.Bridge`, `Once.Format.Bridge`) call through these fields, so a
-- function the CLI runs is a field here; `run-ast-dumps.sh` dumps from `runs`
-- beside `Once.Certified.once-certified` and reports what runs unproved.
------------------------------------------------------------------------

record Runs : Set₁ where
  field
    -- the front end the tools share
    parse-source    : String → String ⊎ Module
    module-imports  : Module → List (List String × Maybe String)
    import-path     : (List String × Maybe String) → List String
    import-alias    : (List String × Maybe String) → Maybe String
    module-has-main : Module → Bool
    resolve-imports : ModuleMap → Module → String ⊎ Resolved
    resolved-module : Resolved → Module
    warnings        : Arch → String → Resolved → List String
    -- the compiler (`once build`)
    assembly        : Bool → Arch → Resolved → String ⊎ String
    -- the tools beside it (D352)
    signatures      : Resolved → String ⊎ String
    check           : Resolved → String ⊎ ⊤
    dump-ir         : Bool → Resolved → String ⊎ String
    stats           : Bool → Resolved → String ⊎ String
    format          : String → String ⊎ String

runs : Runs
runs = record
  { parse-source    = Parser.parseStrict
  ; module-imports  = Names.module-imports
  ; import-path     = Names.import-path
  ; import-alias    = Names.import-alias
  ; module-has-main = Names.module-has-main
  ; resolve-imports = Resolve.resolveImports
  ; resolved-module = Core.Resolved.rmodule
  ; warnings        = Warnings.warningsFor
  ; assembly        = Compile.assemblyFromModule
  ; signatures      = Inspect.signatures
  ; check           = Inspect.check
  ; dump-ir         = Inspect.dumpIR
  ; stats           = Measure.statsOf
  ; format          = Format.formatSource
  }
