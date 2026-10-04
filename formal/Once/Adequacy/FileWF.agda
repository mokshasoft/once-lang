-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.FileWF — plan 0.107 phase d: THE FILE IS WHAT `as`/`ld` ACCEPT.
--
-- `as-faithful` (`Once.Adequacy.CPU.Interface`) is the ONLY trust about turning
-- a program into bytes, and it is preconditioned on `AsmWF`: every symbol the
-- file defines is defined once, every symbol it references is defined in it or
-- is an interpretation's, and the entry point is an instruction of it.
--
-- RESIDUAL, class **deferred proof / codegen** — ONE statement, over the FILE,
-- replacing three over the text (`LabelClash.program-labels-distinct`,
-- `program-labels-resolvable`, `SymbolClash.program-symbols-resolvable`; D100,
-- D167, D169). Unlike the loader axiom it carries NO run claim: everything about
-- what the file DOES is proved (`file-flat-<arch>`); this says only that the
-- toolchain will accept it.
--
-- Plan 0.108 (D264) removed the shapes it was false for: a comparison's call
-- names its arith block, which the rewrite registers, and a BARE arithmetic
-- primitive (operands not arithmetic) is lifted as `SigOp si ∘ id` — so every
-- arithmetic call names a block the file defines. Discharging it (the label windows of `LabelScope`,
-- `LabelsUnique`, the block table) is the rest of phase d.
------------------------------------------------------------------------

module Once.Adequacy.FileWF where

open import Data.Bool using (false)
open import Data.Sum using (inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Target.Arch using (Arch)
open import Once.Parser.Module.Core using (Module)
import Once.Compile as C
open import Once.Adequacy.Compile using (AsmWF-of)

postulate
  file-wf : ∀ (arch : Arch) (m : Module) (F : C.FileOf arch)
          → C.compileFileFromModule C.Heap false arch m ≡ inj₂ F
          → AsmWF-of arch F
