-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Target.RegConvention
--
-- The SHARED register-convention signature (Plan 0.55/0.56). Each arch
-- INSTANTIATES this record with its own physical register set + partition,
-- instead of re-declaring the structure per arch. Wiring `RegConvention`
-- into a generic consumer (or the `Target` record) forces every new arch
-- to declare — and prove valid — how it lends registers to the arith block.
--
--   * `RegClass` — the shared four-way ownership partition.
--   * `owner`    — every physical register's class.
--   * `arith-budget` — the arith-owned registers the block may use, in
--                      priority order; `budget-owned` PROVES each is
--                      `arith`-owned, so a bad budget (e.g. a CCC register)
--                      fails to typecheck at instantiation.
------------------------------------------------------------------------

module Once.Target.RegConvention where

open import Data.String using (String)
open import Data.List using (List)
open import Data.List.Relation.Unary.All using (All)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- Ownership partition across a SigOp (arith-block) boundary.
data RegClass : Set where
  io    : RegClass   -- shared calling-convention (input / output)
  ccc   : RegClass   -- live in CCC across the call
  arith : RegClass   -- the arith block's private working set
  free  : RegClass   -- emitted by neither

-- One arch's register convention. `Set₁` because `Reg` is a `Set` field.
record RegConvention : Set₁ where
  field
    Reg          : Set
    showReg      : Reg → String
    owner        : Reg → RegClass
    arith-budget : List Reg
    budget-owned : All (λ r → owner r ≡ arith) arith-budget
