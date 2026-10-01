-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.CallOK — the per-instruction fact behind `CallsLinked`:
-- a direct call (`c-call-fn f`) names an entry of the table at some objects.
-- Unparameterised, so the fact is ONE predicate across every unit's owner.
------------------------------------------------------------------------

module Once.CCC.Codegen.CallOK where

open import Data.List using (List)
open import Data.Product using (Σ)
open import Data.Unit using (⊤)
open import Once.IRTy using (IRTy)
open import Once.CCC.Machine.SMCore using (AbstractInstr; instr-ctrl; c-call-fn)
open import Once.Denotation.Program using (IRFun; LinkedAt)

-- CATCHALL: only a direct call is constrained.
CallOKI : List IRFun → AbstractInstr → Set
CallOKI tbl (instr-ctrl (c-call-fn f)) = Σ IRTy (λ A → Σ IRTy (λ B → LinkedAt tbl f A B))
{-# CATCHALL #-}
CallOKI tbl _                          = ⊤
