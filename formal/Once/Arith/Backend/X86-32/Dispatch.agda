-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.Backend.X86-32.Dispatch  (Plan 0.54 rung B / B2.4)
--
-- x86-32 whole-program arith dispatch (the value half). `run-events`, on a
-- `call once_arith.block.*`, runs the block and returns past the call.
--
-- D394: the dispatch is the WHOLE subroutine the emitter prints
-- (`Emit.emit-payload`): `call` pushes the return address, the prologue pushes
-- the four borrowed registers (%ebx %esi %edx %edi) and `subl $4n, %esp`
-- reserves the scratch frame; the body runs there; the epilogue's `addl`, pops
-- and `ret` give the caller back %esp, those four registers and the
-- instruction after the call. The body writes only inside its frame
-- (`InFrame`), so what the pops and `ret` read back is what was pushed.
------------------------------------------------------------------------

module Once.Arith.Backend.X86-32.Dispatch where

open import Data.Nat using (ℕ; suc; _*_; _∸_)
open import Data.List using (List)

open import Once.Arith.Backend.XInstr.Syntax using (XInstr)
open import Once.Target.X86-32.PhysReg using (Reg; ebx; esi; edx; edi; esp)
open import Once.CCC.Target.X86-32.Semantics using (State; Word; readReg; writeReg; writeMem)
open State using (pc; regs; memory)
open import Once.Arith.Backend.X86-32.ExecArith using (exec-arith-block)

module _ (val : XInstr → State → Reg → Word) where

  -- the five words the call and the prologue push, in order, below `sp`
  call-frame : ℕ → State → State
  call-frame n s =
    record s { regs   = writeReg (regs s) esp (sp ∸ 20 ∸ 4 * n)
             ; memory = writeMem (writeMem (writeMem (writeMem (writeMem (memory s)
                          (sp ∸ 4)  (suc (pc s)))
                          (sp ∸ 8)  (readReg (regs s) ebx))
                          (sp ∸ 12) (readReg (regs s) esi))
                          (sp ∸ 16) (readReg (regs s) edx))
                          (sp ∸ 20) (readReg (regs s) edi) }
    where sp = readReg (regs s) esp

  -- the epilogue: %esp and the borrowed registers back, past the call
  restore : State → State → State
  restore s s′ =
    record s′ { regs = writeReg (writeReg (writeReg (writeReg (writeReg (regs s′)
                         esp (readReg (regs s) esp))
                         ebx (readReg (regs s) ebx))
                         esi (readReg (regs s) esi))
                         edx (readReg (regs s) edx))
                         edi (readReg (regs s) edi)
              ; pc   = suc (pc s) }

  -- Dispatch a `call once_arith.block.*` (n: the block's scratch words).
  dispatch-arith : List XInstr → ℕ → State → State
  dispatch-arith blk n s = restore s (exec-arith-block val blk (call-frame n s))
