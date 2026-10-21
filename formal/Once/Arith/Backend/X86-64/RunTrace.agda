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
open import Data.Bool using (true)
open import Data.String using (String)
open import Data.Nat using (ℕ; suc)
open import Data.List using (List)

open import Data.Product using (_×_; uncurry)

open import Once.Arith.Backend.XInstr.Syntax using (XInstr)
open import Once.Target.X86-64.PhysReg using (Reg; rax)
open import Once.CCC.Target.X86-64.Syntax using (Program; Instr; call-sym)
open import Once.CCC.Target.X86-64.Semantics using (State; fetch; execInstr; Word; writeReg)
open import Once.Internal.Event using (SigOpEvent)
open State using (halted; pc; regs)
open import Once.Arith.Backend.X86-64.Dispatch using (dispatch-arith)
import Once.Arith.Backend.RunTraceCore as Core
import Once.Arith.Backend.RunTraceMachine as RTM

-- Classify a `call-sym` (the generic core's `matchCall`): reduces on the
-- `call-sym` constructor, so the trace loop still reduces definitionally.
matchCall : Instr → Maybe String
matchCall (call-sym lbl) = just lbl
{-# CATCHALL #-}
matchCall _              = nothing

-- Return past a `call` (the SigOp/subroutine returns to the next instruction).
ret-past : State → State
ret-past s = record s { pc = suc (pc s) }

-- Plan 0.105: the ABI's half of an EXTERNAL call. The callee leaves its
-- answer in the return register (`rax`, the `Output` role) and control
-- returns past the `call`. `answer` is what the world answered, as a word
-- (`CallAnswer.answer-at`), at the binary's log `h` before the call.
-- D320: a call with NO answer (its answer type is empty: an `exit`, the Host's
-- `leave`) does not return — the machine halts at it.
ret-with : Maybe Word → State → State
ret-with (just w) s = record (ret-past s) { regs = writeReg (regs s) rax w }
ret-with nothing  s = record s { halted = true }

ret-call : (List SigOpEvent → String → State → Maybe Word) → List SigOpEvent → String → State → State
ret-call answer h lbl s = ret-with (answer h lbl s) s

module _ (val : XInstr → State → Reg → Word) (answer : List SigOpEvent → String → State → Maybe Word) where
  open Core.RunTrace State Program Instr (List XInstr × ℕ)
    halted pc fetch execInstr matchCall (ret-call answer) (uncurry (dispatch-arith val)) public
  -- D320: the same machine as a machine whose trace is read off by corecursion.
  module Run = RTM.RunMachine State Program Instr (List XInstr × ℕ)
    halted pc fetch execInstr matchCall (ret-call answer) (uncurry (dispatch-arith val))
