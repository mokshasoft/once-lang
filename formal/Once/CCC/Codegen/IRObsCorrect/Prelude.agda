-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Prelude
--
-- What the IRObsCorrect parts share at one definition (`o`, `tbl`):
-- `fits-erase`, and the instances `ValidAtWFHalted`, `IRToTrace` and
-- `SlotBudget′`, which the parts open through `Interface`.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

open import Data.List using (List)
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.Prelude (o : CanonicalName) (tbl : List IRFun) where
-- SigOpInfo is over SURFACE Type (`SigOp : SigOpInfo A B → IR ⌊A⌋ ⌊B⌋`), so the
-- surface `FitsInReg`/`fits-in-reg?` stay; the μ/functor + value-domain layer is IRTy.
open import Once.Type using (FitsInReg) renaming (fits-int to fits-intˢ; fits-float to fits-floatˢ)
open import Once.IRTy using (FitsInRegI; ⌊_⌋; fits-int; fits-float)
open import Data.Unit using (tt)

-- Surface `FitsInReg B` ⇒ erased `FitsInRegI ⌊B⌋`: `⌊Int⌋=Int`, `⌊Float⌋=Float`
-- definitionally, so this is a match-to-refl coherence.
fits-erase : ∀ {B} → FitsInReg B → FitsInRegI ⌊ B ⌋
fits-erase fits-intˢ   = fits-int
fits-erase fits-floatˢ = fits-float
import Once.CCC.Machine.ValidAtWFHalted
module ValidAtWFHalted = Once.CCC.Machine.ValidAtWFHalted o tbl using (validAtWF-set-halted)
import Once.CCC.Codegen.IRToTrace
module IRToTrace = Once.CCC.Codegen.IRToTrace o using (ir-to-trace; ir-to-trace')
import Once.CCC.Codegen.SlotBudget
module SlotBudget′ = Once.CCC.Codegen.SlotBudget o using (frontier-mono; budget-of)

