-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.Loader — plan 0.146 (D458–D460): A BASE VALUE'S WORDS AND A
-- LITERAL'S LOADER, one definition for the compiler (`Emit`) and its proof
-- (`MachineLit`, `Apex`), so the image the compiler writes is the image the
-- proof is about.
------------------------------------------------------------------------

module Once.LinCore.Loader where

open import Data.Nat using (ℕ)
open import Once.Type using (fits-int; fits-float)
open import Once.CCC.Machine.SMCore using (AbstractInstr; instr-load-const)
open import Once.LinCore.Flat using (Base; int; float; Lit)

-- a base value is one word on every arch (`Spec.ABI`)
bw : Base → ℕ
bw int   = 1
bw float = 1

-- a literal's loader: an `instr-load-const`
ldConst : ∀ {b} → Lit b → AbstractInstr
ldConst {int}   z = instr-load-const fits-int z
ldConst {float} d = instr-load-const fits-float d
