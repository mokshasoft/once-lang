-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Arith.Backend.RiscV64.RunTrace  (Plan 0.54 Phase B / Option 2)
--
-- riscv64 instance of the arch-generic `Arith.Backend.RunTraceCore`. Same
-- machine logic as x86-64; the ONLY arch difference is the arith `Payload`,
-- which threads the frame size `N`: `List XInstr × ℕ`, dispatched by
-- `uncurry (dispatch-arith val)`.
------------------------------------------------------------------------

module Once.Arith.Backend.RiscV64.RunTrace where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; uncurry)
open import Data.List using (List)

open import Once.Arith.Backend.XInstr.Syntax using (XInstr)
open import Once.Target.RiscV64.PhysReg using (Reg)
open import Once.CCC.Target.RiscV64.Syntax using (Program; Instr; call-sym)
open import Once.CCC.Target.RiscV64.Semantics using (State; fetch; execInstr; Word)
open State using (halted; pc)
open import Once.Arith.Backend.RiscV64.Dispatch using (dispatch-arith)
import Once.Arith.Backend.RunTraceCore as Core

matchCall : Instr → Maybe String
matchCall (call-sym lbl) = just lbl
matchCall _              = nothing

ret-past : State → State
ret-past s = record s { pc = suc (pc s) }

module _ (val : XInstr → State → Reg → Word) where
  open Core.RunTrace State Program Instr (List XInstr × ℕ)
    halted pc fetch execInstr matchCall ret-past (uncurry (dispatch-arith val)) public
