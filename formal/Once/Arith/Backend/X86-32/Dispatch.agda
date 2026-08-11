-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.Backend.X86-32.Dispatch  (Plan 0.54 rung B / B2.4)
--
-- x86-32 whole-program arith dispatch (the value half). `run-events`, on a
-- `call once_arith.block.*`, runs the block and returns past the call.
--
-- NOTE (borrow/restore): unlike x86-64/riscv64 there is NO `dispatch-arith-
-- preserves` here. x86-32's arith registers edx/edi are CCC-BORROWED, so
-- `exec-arith-block` (the fold over the arith instructions) does NOT preserve
-- CCC state — it clobbers edx/edi. The EMITTED subroutine preserves CCC by
-- bracketing the body with push/pop (Emit.emit-arith-block), so CCC-preservation
-- is a property of the FULL bracketed subroutine, not this fold. Proving it is
-- the BorrowRestoreCore residual. The value (result register) is unaffected by
-- the framing, so the value slice below is complete.
------------------------------------------------------------------------

module Once.Arith.Backend.X86-32.Dispatch where

open import Data.Nat using (suc)
open import Data.List using (List)

open import Once.Arith.Backend.XInstr.Syntax using (XInstr)
open import Once.Target.X86-32.PhysReg using (Reg)
open import Once.CCC.Target.X86-32.Semantics using (State; Word)
open State using (pc)
open import Once.Arith.Backend.X86-32.ExecArith using (exec-arith-block)

module _ (val : XInstr → State → Reg → Word) where

  -- Dispatch a `call once_arith.block.*`: run the block, return past the call
  -- (the pc bump is a record update on pc only — regs/memory = the block's).
  dispatch-arith : List XInstr → State → State
  dispatch-arith blk s = record (exec-arith-block val blk s) { pc = suc (pc s) }
