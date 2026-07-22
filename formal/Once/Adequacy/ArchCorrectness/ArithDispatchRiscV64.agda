-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.ArithDispatchRiscV64  (Plan 0.54 rung B / B2.4)
--
-- The ARITH SLICE of conc-flat-sim for riscv64 — the mirror of
-- `ArithDispatchX86-64`. `dispatch-arith` runs `exec-arith-block val N` with a
-- transparent pc bump and emits no event; this proves it behaves as the flat
-- model's atomic Pure op, combining the two proven halves (value + CCC).
--
-- riscv threads the frame size `N` (reserved scratch bytes) and needs the block's
-- in-frame witness `All (InFrame N) blk` (its `sp + 8·slot` addressing needs the
-- slot bound, where x86-64's subtract-addressing did not) — taken as a precondition,
-- like x86-64's `0 < rsp`. The result reg is `a0` (riscv's out-reg).
------------------------------------------------------------------------

module Once.Adequacy.ArchCorrectness.ArithDispatchRiscV64 where

open import Data.Nat using (ℕ; _+_; _<_)
open import Data.Product using (_×_; _,_)
open import Data.List using (List)
open import Data.List.Relation.Unary.All using (All)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Arith.Machine.Shape using (InputShape; ⟦_⟧S)
open import Once.Arith.Machine.AbsState using (init)
open import Once.Arith.Machine.IR using (MArithIR)
open import Once.Arith.Backend.XInstr.CodeGen using (emit-program)
open import Once.Arith.Machine.Compile using (compile-abs)
open import Once.Arith.SigOp.Block using (block-semM)
open import Once.Arith.SigOp.BlockSemBridge using (toWord)

open import Once.Target.RiscV64.PhysReg using (sp; a0)
open import Once.CCC.Target.RiscV64.Semantics using (State; readReg)
open State using (regs)
open import Once.Arith.Backend.RiscV64.StatePreserve using (PreservesCCCState)
open import Once.Arith.Backend.RiscV64.ExecArith using (InFrame)
open import Once.Arith.Backend.RiscV64.Dispatch using (dispatch-arith; dispatch-arith-preserves)
import Once.Adequacy.ArchCorrectness.ArithSimRiscV64 as ASR

arith-dispatch-correct :
    ∀ (N : ℕ) {sh} (e : MArithIR sh) (env : ⟦ sh ⟧S) (s : State)
  → 0 < readReg (regs s) sp + N
  → All (InFrame N) (emit-program (compile-abs e))
  → ASR.R-input N (init env) s
  → PreservesCCCState (readReg (regs s) sp + N) s
      (dispatch-arith ASR.val-riscv64 (emit-program (compile-abs e)) N s)
  × ( readReg (regs (dispatch-arith ASR.val-riscv64 (emit-program (compile-abs e)) N s)) a0
        ≡ block-semM e (toWord sh env) )
arith-dispatch-correct N e env s 0<fr inf ri =
    dispatch-arith-preserves ASR.val-riscv64 (emit-program (compile-abs e)) N s 0<fr inf
  , ASR.arith-block-correct N e env s ri
