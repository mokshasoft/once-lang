-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.IR.Semantics.Boundary — the implementation's side of D397.
--
-- `Spec.Boundary.readAt` reads what the world gives at the target, over the
-- Spec's answer types. This is the same reading over the implementation's
-- value domain (`M.⟦_⟧`, at a `Type`): an `Int` as the word at the target's
-- width, a `Float` as a value of its format (on its encoding), a compound value leaf by leaf.
-- Every place a world value enters the implementation — a pure FFI value, a
-- call's answer, the register an external call returns in — reads it here.
------------------------------------------------------------------------

module Once.IR.Semantics.Boundary where

open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Once.Spec.Word using (Carrier)
import Once.Spec.Word as SW
import Once.IR.Semantics.Value Carrier Carrier as M
open import Once.Spec.Type using (Ty; Int; Float; _*_; _+_)
open import Once.Spec.Numerics using (TargetNum; module TargetNum)
open TargetNum
import Once.Float.Word as FW

atTarget : TargetNum → ∀ {m} (B : Ty m) → M.⟦ B ⟧ → M.⟦ B ⟧
atTarget tn Int      v        = SW.Width.norm (int-bits tn) v
atTarget tn Float    v        = FW.fit (float-format tn) v
atTarget tn (A * B)  (x , y)  = atTarget tn A x , atTarget tn B y
atTarget tn (A + B)  (inj₁ x) = inj₁ (atTarget tn A x)
atTarget tn (A + B)  (inj₂ y) = inj₂ (atTarget tn B y)
{-# CATCHALL #-}
atTarget tn _        v        = v
