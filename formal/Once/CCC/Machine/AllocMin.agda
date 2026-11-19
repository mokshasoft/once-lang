-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Machine.AllocMin — an allocation is of at least one word (plan
-- 0.123 B.4 α, D388: the arch layer's heap correspondence reads a block's
-- first word).
--
-- The predicate the arch layer reads of an image (`RunContext.Emitted.em-alloc`).
-- It stood beside master's emitter's proof of it (`Codegen.AllocMin`); plan
-- 0.146 step 4 (D465) keeps the predicate here, the emitter's half went with
-- master's lowering (the linear core's image: `LinCore.ImageAll.em-alloc`).
------------------------------------------------------------------------

module Once.CCC.Machine.AllocMin where

open import Data.Nat using (_≤_)
open import Data.Unit using (⊤)
open import Data.List.Relation.Unary.All using (All)
open import Once.CCC.Machine.SMCore using (AbstractInstr; AbstractTrace; instr-alloc-heap)

AllocMinI : AbstractInstr → Set
AllocMinI (instr-alloc-heap n) = 1 ≤ n
{-# CATCHALL #-}
AllocMinI _                    = ⊤

AllocMinTrace : AbstractTrace → Set
AllocMinTrace = All AllocMinI
