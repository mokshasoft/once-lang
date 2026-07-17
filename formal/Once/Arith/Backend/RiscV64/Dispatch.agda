-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Arith.Backend.RiscV64.Dispatch  (Plan 0.54 Phase B / Option 2)
--
-- riscv64 whole-program dispatch. Mirrors x86-64 but threads the frame size `N`
-- (the arith block's reserved scratch, in bytes) and the block's in-frame
-- witnesses — the ArithEnv maps a call label to (block, N). Dispatching an arith
-- block preserves CCC state (registers + memory ≥ entry sp), given the block's
-- slots fit the frame (`All (InFrame N) blk`).
------------------------------------------------------------------------

module Once.Arith.Backend.RiscV64.Dispatch where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String)
open import Data.Nat using (ℕ; suc; _+_; _<_)
open import Data.Product using (_×_; _,_)
open import Data.List using (List)
open import Data.List.Relation.Unary.All using (All)
open import Data.Bool using (true)
open import Relation.Binary.PropositionalEquality using (refl)

open import Once.Arith.Backend.XInstr.Syntax using (XInstr)
open import Once.Target.RiscV64.PhysReg using (Reg; sp)
open import Once.CCC.Target.RiscV64.Syntax using (Program; Instr; call-sym)
open import Once.CCC.Target.RiscV64.Semantics using (State; readReg; fetch; execInstr; Word)
open State
open import Once.Arith.Backend.RiscV64.StatePreserve using (PreservesCCCState; mkPresState)
open import Once.Arith.Backend.RiscV64.ExecArith using (exec-arith-block; exec-arith-block-preserves; InFrame)

module _ (val : XInstr → State → Reg → Word) where

  -- Call labels → (arith block, reserved frame size N).
  ArithEnv : Set
  ArithEnv = String → Maybe (List XInstr × ℕ)

  dispatch-arith : List XInstr → ℕ → State → State
  dispatch-arith blk N s = record (exec-arith-block val N blk s) { pc = suc (pc s) }

  step-instr : ArithEnv → Program → State → Instr → Maybe State
  step-instr env prog s (call-sym lbl) with env lbl
  ... | just (blk , N) = just (dispatch-arith blk N s)
  ... | nothing        = execInstr prog s (call-sym lbl)
  step-instr env prog s i = execInstr prog s i

  step-wp : ArithEnv → Program → State → Maybe State
  step-wp env prog s with fetch prog (pc s)
  ... | just i  = step-instr env prog s i
  ... | nothing = just (record s { halted = true })

  dispatch-arith-preserves : ∀ blk N s → 0 < readReg (regs s) sp + N → All (InFrame N) blk →
                             PreservesCCCState (readReg (regs s) sp + N) s (dispatch-arith blk N s)
  dispatch-arith-preserves blk N s 0<fr allInf =
    mkPresState (PreservesCCCState.regs≈ P) (PreservesCCCState.mem≈ P)
    where
      P : PreservesCCCState (readReg (regs s) sp + N) s (exec-arith-block val N blk s)
      P = exec-arith-block-preserves val N blk (readReg (regs s) sp + N) s refl 0<fr allInf
