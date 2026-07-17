-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Arith.Backend.X86-64.Dispatch  (Plan 0.54 Phase B / Option 2)
--
-- Whole-program dispatch: the exec loop, on a `call once_arith.block.*`, runs
-- the arith subroutine (`exec-arith-block`) and returns past the call; every
-- other instruction — including a `call-sym` that lowers an external SigOp
-- invocation — falls through to the CCC `execInstr`.
--
-- The key fact: an arith-block dispatch PRESERVES CCC state (registers +
-- memory), so the continuation runs exactly as if the arith block were the
-- atomic operation the flat model treats it as. The `pc`-update (return address)
-- is transparent to `PreservesCCCState`, which reads only regs + memory.
--
-- (A SigOp is a SigOp — `call-sym` is merely how a SigOp invocation is LOWERED;
-- the arith blocks handled here are Pure and emit no SigOp event.)
------------------------------------------------------------------------

module Once.Arith.Backend.X86-64.Dispatch where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String)
open import Data.Nat using (ℕ; suc; _<_)
open import Data.List using (List)
open import Data.Bool using (true)
open import Relation.Binary.PropositionalEquality using (refl)

open import Once.Arith.Backend.XInstr.Syntax using (XInstr)
open import Once.Target.X86-64.PhysReg using (Reg; rsp)
open import Once.CCC.Target.X86-64.Syntax using (Program; Instr; call-sym)
open import Once.CCC.Target.X86-64.Semantics
  using (State; readReg; fetch; execInstr; Word)
open State
open import Once.Arith.Backend.X86-64.StatePreserve using (PreservesCCCState; mkPresState)
open import Once.Arith.Backend.X86-64.ExecArith using (exec-arith-block; exec-arith-block-preserves)

module _ (val : XInstr → State → Reg → Word) where

  -- Which call labels name arith subroutines (vs external SigOp invocations).
  ArithEnv : Set
  ArithEnv = String → Maybe (List XInstr)

  -- Dispatch a `call once_arith.block.*`: run the block, return past the call.
  dispatch-arith : List XInstr → State → State
  dispatch-arith blk s = record (exec-arith-block val blk s) { pc = suc (pc s) }

  -- Resolve one fetched instruction: arith-block call → dispatch; else CCC.
  step-instr : ArithEnv → Program → State → Instr → Maybe State
  step-instr env prog s (call-sym lbl) with env lbl
  ... | just blk = just (dispatch-arith blk s)
  ... | nothing  = execInstr prog s (call-sym lbl)
  step-instr env prog s i = execInstr prog s i

  -- One whole-program step.
  step-wp : ArithEnv → Program → State → Maybe State
  step-wp env prog s with fetch prog (pc s)
  ... | just i  = step-instr env prog s i
  ... | nothing = just (record s { halted = true })

  ------------------------------------------------------------------------
  -- Dispatching to an arith block preserves CCC state.
  -- `dispatch-arith` = `exec-arith-block` with a transparent `pc` update, so
  -- its regs/memory equal the block's, and `exec-arith-block-preserves` applies.
  ------------------------------------------------------------------------

  dispatch-arith-preserves : ∀ blk s → 0 < readReg (regs s) rsp →
                             PreservesCCCState (readReg (regs s) rsp) s (dispatch-arith blk s)
  dispatch-arith-preserves blk s 0<r =
    mkPresState (PreservesCCCState.regs≈ P) (PreservesCCCState.mem≈ P)
    where
      -- regs/memory of `dispatch-arith blk s` equal the block's (pc is transparent),
      -- so the fields transport even though the record TYPE is indexed by full State.
      P : PreservesCCCState (readReg (regs s) rsp) s (exec-arith-block val blk s)
      P = exec-arith-block-preserves val blk (readReg (regs s) rsp) s refl 0<r
