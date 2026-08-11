-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.Backend.X86-64.RunTrace  (Plan 0.54 Phase B / Option 2)
--
-- x86-64 instance of the arch-generic `Arith.Backend.RunTraceCore`: the
-- emit-and-continue SigOp-event trace over the concrete x86-64 machine with
-- arith-block dispatch. All machine logic lives in the core; this module only
-- supplies the x86-64 telescope (State/Program/Instr, fetch/execInstr, the
-- `call-sym` classifier, `ret-past`) + the arith payload (`List XInstr`, with
-- `val` baked into `dispatch-arith`).
------------------------------------------------------------------------

module Once.Arith.Backend.X86-64.RunTrace where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String)
open import Data.Nat using (ℕ; suc)
open import Data.List using (List)

open import Data.Product using (_×_; uncurry)

open import Once.Arith.Backend.XInstr.Syntax using (XInstr)
open import Once.Target.X86-64.PhysReg using (Reg)
open import Once.CCC.Target.X86-64.Syntax using (Program; Instr; call-sym)
open import Once.CCC.Target.X86-64.Semantics using (State; fetch; execInstr; Word)
open State using (halted; pc)
open import Once.Arith.Backend.X86-64.Dispatch using (dispatch-arith)
import Once.Arith.Backend.RunTraceCore as Core

-- Classify a `call-sym` (the generic core's `matchCall`): reduces on the
-- `call-sym` constructor, so the trace loop still reduces definitionally.
matchCall : Instr → Maybe String
matchCall (call-sym lbl) = just lbl
matchCall _              = nothing

-- Return past a `call` (the SigOp/subroutine returns to the next instruction).
ret-past : State → State
ret-past s = record s { pc = suc (pc s) }

module _ (val : XInstr → State → Reg → Word) where
  open Core.RunTrace State Program Instr (List XInstr × ℕ)
    halted pc fetch execInstr matchCall ret-past (uncurry (dispatch-arith val)) public
