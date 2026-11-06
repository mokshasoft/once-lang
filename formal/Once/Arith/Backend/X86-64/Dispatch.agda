-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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
open import Data.Nat using (ℕ; suc; _+_; _*_; _∸_)
open import Data.List using (List)
open import Data.List.Relation.Unary.All using (All)
open import Data.Product using (_×_; _,_)
open import Data.Bool using (true)
open import Relation.Binary.PropositionalEquality using (refl)

open import Once.Arith.Backend.XInstr.Syntax using (XInstr)
open import Once.Target.X86-64.PhysReg using (Reg; rsp)
open import Once.CCC.Target.X86-64.Syntax using (Program; Instr; call-sym)
open import Once.CCC.Target.X86-64.Semantics
  using (State; readReg; writeReg; writeMem; fetch; execInstr; Word)
open State
open import Once.Arith.Backend.X86-64.ExecArith using (exec-arith-block)

module _ (val : XInstr → State → Reg → Word) where

  -- Call labels → (arith block, reserved frame size N).
  ArithEnv : Set
  ArithEnv = String → Maybe (List XInstr × ℕ)

  -- D393: what `call <block>` and the block's prologue do before its body —
  -- the call pushes the return address (`pc + 1`, as `execInstr`'s `call`
  -- does) and `subq $8n, %rsp` reserves the scratch frame below it, so the
  -- body's `8·slot(%rsp)` lands in `[sp − 8 − 8n, sp − 8)`, never at or above
  -- the caller's stack pointer.
  call-frame : ℕ → State → State
  call-frame n s = record s { regs   = writeReg (regs s) rsp (ra ∸ 8 * n)
                            ; memory = writeMem (memory s) ra (suc (pc s)) }
    where ra = readReg (regs s) rsp ∸ 8

  -- Dispatch a `call once_arith.block.*`: enter the frame, run the body, and
  -- the epilogue's `addq $8n, %rsp` + `ret` give the caller back its stack
  -- pointer and the instruction after the call (the body writes only below
  -- the return address, `InFrame`).
  dispatch-arith : List XInstr → ℕ → State → State
  dispatch-arith blk n s =
    let s′ = exec-arith-block val (8 * n) blk (call-frame n s)
    in record s′ { regs = writeReg (regs s′) rsp (readReg (regs s) rsp) ; pc = suc (pc s) }

  -- Resolve one fetched instruction: arith-block call → dispatch; else CCC.
  step-instr : ArithEnv → Program → State → Instr → Maybe State
  step-instr env prog s (call-sym lbl) with env lbl
  ... | just (blk , N) = just (dispatch-arith blk N s)
  ... | nothing        = execInstr prog s (call-sym lbl)
  {-# CATCHALL #-}
  step-instr env prog s i = execInstr prog s i

  -- One whole-program step.
  step-wp : ArithEnv → Program → State → Maybe State
  step-wp env prog s with fetch prog (pc s)
  ... | just i  = step-instr env prog s i
  ... | nothing = just (record s { halted = true })
