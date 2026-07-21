-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Target.RiscV64.PhysReg
--
-- The SINGLE RV64 physical-register declaration, shared by the CCC and
-- arith backends (Plan 0.55). `owner` partitions the file so CCC/arith
-- register disjointness is definitional (a `refl`).
--
-- Partition (from the 0.55 audit of CCC's RV64 codegen):
--   * io   — t0 (Input1 / arith block input pointer), a0 (Output / arith
--            result; also the arith block's path-walk scratch).
--   * ccc  — live in CCC across a SigOp call: its address-computation
--            temporaries t1-t4 (CCC emits t1 ~45×), the argument regs
--            a1 a2 a6 a7, the saved regs s1-s4, and sp ra fp (+ zero).
--   * arith— a3 a4: the caller-saved argument registers CCC never emits.
--            (`compile-go` is a 2-register + stack-spill discipline, so the
--            arith reg file `XReg` = {XR0, XR1} maps to just a3/a4.)
------------------------------------------------------------------------

module Once.Target.RiscV64.PhysReg where

open import Data.String using (String)

data Reg : Set where
  zero : Reg
  ra   : Reg
  sp   : Reg
  fp   : Reg
  a0 a1 a2 a3 a4 a5 a6 a7 : Reg
  s1 s2 s3 s4 : Reg
  t0 t1 t2 t3 t4 : Reg

showReg : Reg → String
showReg zero = "zero"
showReg ra   = "ra"
showReg sp   = "sp"
showReg fp   = "fp"
showReg a0   = "a0"
showReg a1   = "a1"
showReg a2   = "a2"
showReg a3   = "a3"
showReg a4   = "a4"
showReg a5   = "a5"
showReg a6   = "a6"
showReg a7   = "a7"
showReg s1   = "s1"
showReg s2   = "s2"
showReg s3   = "s3"
showReg s4   = "s4"
showReg t0   = "t0"
showReg t1   = "t1"
showReg t2   = "t2"
showReg t3   = "t3"
showReg t4   = "t4"

open import Once.Target.RegConvention public
  using (RegClass; io; ccc; arith; free; RegConvention)

owner : Reg → RegClass
owner t0 = io
owner a0 = io
owner a3 = arith
owner a4 = arith
owner a5 = arith
owner zero = ccc
owner ra = ccc
owner sp = ccc
owner fp = ccc
owner a1 = ccc
owner a2 = ccc
owner a6 = ccc
owner a7 = ccc
owner s1 = ccc
owner s2 = ccc
owner s3 = ccc
owner s4 = ccc
owner t1 = ccc
owner t2 = ccc
owner t3 = ccc
owner t4 = ccc

------------------------------------------------------------------------
-- Arith register budget (Plan 0.56).
------------------------------------------------------------------------

open import Data.List using (List; []; _∷_)
import Data.List.Relation.Unary.All as All
open import Relation.Binary.PropositionalEquality using (refl)

arith-budget : List Reg
arith-budget = a3 ∷ a4 ∷ a5 ∷ []

convention : RegConvention
convention = record
  { Reg = Reg ; showReg = showReg ; owner = owner ; arith-budget = arith-budget
  ; budget-owned = refl All.∷ refl All.∷ refl All.∷ All.[] }
