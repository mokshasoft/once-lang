-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.Backend.RiscV64.Dispatch  (Plan 0.54 Phase B / Option 2)
--
-- riscv64 whole-program dispatch. Mirrors x86-64: the ArithEnv maps a call
-- label to (block, n), n its scratch words; the dispatch enters the block's
-- frame below the caller's sp (D388).
------------------------------------------------------------------------

module Once.Arith.Backend.RiscV64.Dispatch where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String)
open import Data.Nat using (ℕ; suc; _+_; _*_; _∸_)
open import Data.Product using (_×_; _,_)
open import Data.List using (List)
open import Data.List.Relation.Unary.All using (All)
open import Data.Bool using (true)
open import Relation.Binary.PropositionalEquality using (refl)

open import Once.Arith.Backend.XInstr.Syntax using (XInstr)
open import Once.Target.RiscV64.PhysReg using (Reg; sp; ra)
open import Once.CCC.Target.RiscV64.Syntax using (Program; Instr; call-sym)
open import Once.CCC.Target.RiscV64.Semantics using (State; readReg; writeReg; fetch; execInstr; Word)
open State
open import Once.Arith.Backend.RiscV64.ExecArith using (exec-arith-block)

module _ (val : XInstr → State → Reg → Word) where

  -- Call labels → (arith block, reserved frame size N).
  ArithEnv : Set
  ArithEnv = String → Maybe (List XInstr × ℕ)

  -- D388: what `call <block>` and the block's prologue do before its body —
  -- `call` links the return address into `ra` (as `execInstr`'s `call` does)
  -- and `addi sp, sp, −8n` reserves the scratch frame, so the body's
  -- `8·slot(sp)` lands in `[sp − 8n, sp)`, never at or above the caller's sp.
  call-frame : ℕ → State → State
  call-frame n s = record s { regs = writeReg (writeReg (regs s) ra (suc (pc s))) sp (readReg (regs s) sp ∸ 8 * n) }

  -- the epilogue's `addi sp, sp, 8n` + `ret` give the caller back its stack
  -- pointer and the instruction after the call.
  dispatch-arith : List XInstr → ℕ → State → State
  dispatch-arith blk n s =
    let s′ = exec-arith-block val (8 * n) blk (call-frame n s)
    in record s′ { regs = writeReg (regs s′) sp (readReg (regs s) sp) ; pc = suc (pc s) }

  step-instr : ArithEnv → Program → State → Instr → Maybe State
  step-instr env prog s (call-sym lbl) with env lbl
  ... | just (blk , N) = just (dispatch-arith blk N s)
  ... | nothing        = execInstr prog s (call-sym lbl)
  {-# CATCHALL #-}
  step-instr env prog s i = execInstr prog s i

  step-wp : ArithEnv → Program → State → Maybe State
  step-wp env prog s with fetch prog (pc s)
  ... | just i  = step-instr env prog s i
  ... | nothing = just (record s { halted = true })
