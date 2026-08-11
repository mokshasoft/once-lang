-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.Backend.X86-32.RunTrace  (Plan 0.54 Phase B / Option 2)
--
-- x86-32 instance of the arch-generic `Arith.Backend.RunTraceCore`: the
-- emit-and-continue SigOp-event trace over the concrete x86-32 machine with
-- arith-block dispatch. All machine logic lives in the core; this module only
-- supplies the x86-32 telescope (State/Program/Instr, fetch/execInstr, the
-- `call-sym` classifier, `ret-past`) + the arith payload.
--
-- Unlike x86-64/riscv64 the payload is `List XInstr` (no reserved-frame size `N`):
-- x86-32's `dispatch-arith` runs its self-contained borrow/restore
-- `exec-arith-block val blk s` (edx/edi are CCC-borrowed, restored by the block's
-- own push/pop), so no frame size is threaded into the dispatch.
------------------------------------------------------------------------

module Once.Arith.Backend.X86-32.RunTrace where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String)
open import Data.Nat using (ℕ; suc)
open import Data.List using (List)

open import Once.Arith.Backend.XInstr.Syntax using (XInstr)
open import Once.Target.X86-32.PhysReg using (Reg)
open import Once.CCC.Target.X86-32.Syntax using (Program; Instr; call-sym)
open import Once.CCC.Target.X86-32.Semantics using (State; fetch; execInstr; Word)
open State using (halted; pc)
open import Once.Arith.Backend.X86-32.Dispatch using (dispatch-arith)
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
  open Core.RunTrace State Program Instr (List XInstr)
    halted pc fetch execInstr matchCall ret-past (dispatch-arith val) public
