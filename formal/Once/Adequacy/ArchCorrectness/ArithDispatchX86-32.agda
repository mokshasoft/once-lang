-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.ArithDispatchX86-32  (Plan 0.54 rung B / B2.4)
--
-- The ARITH SLICE of conc-flat-sim for x86-32 — the VALUE half. `dispatch-arith`
-- runs `exec-arith-block val-x86-32` with a transparent pc bump and emits no
-- event; the result register `eax` holds the real block value.
--
-- CCC-preservation is NOT here (see X86-32.Dispatch): x86-32's edx/edi are
-- CCC-BORROWED, so the fold clobbers them and the emit restores them by push/pop
-- — a property of the bracketed subroutine (the BorrowRestoreCore residual), not
-- this fold. So x86-32 completes the VALUE slice; its CCC slice is the honest
-- borrow/restore residual, unlike x86-64/riscv64 whose arith regs are disjoint.
------------------------------------------------------------------------

module Once.Adequacy.ArchCorrectness.ArithDispatchX86-32 where

open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Arith.Machine.Shape using (InputShape; ⟦_⟧S)
open import Once.Arith.Machine.AbsState using (init)
open import Once.Arith.Machine.IR using (MArithIR)
open import Once.Arith.Backend.XInstr.CodeGen using (emit-program)
open import Once.Arith.Machine.Compile using (compile-abs)
open import Once.Arith.SigOp.Block using (block-semM)
open import Once.Arith.SigOp.BlockSemBridge using (toWord)

open import Once.Target.X86-32.PhysReg using (eax)
open import Once.CCC.Target.X86-32.Semantics using (State; readReg)
open State using (regs)
open import Once.Arith.Backend.X86-32.Dispatch using (dispatch-arith)
open import Once.Adequacy.ArchCorrectness.ArithSimX86-32 using (val-x86-32; arith-block-correct; R-input)

-- The arith dispatch leaves the real block value in eax. The pc bump is a record
-- update on pc only, so `regs (dispatch-arith …) = regs (exec-arith-block …)` and
-- `arith-block-correct` transfers by defeq.
arith-dispatch-value :
    ∀ {sh} (e : MArithIR sh) (env : ⟦ sh ⟧S) (s : State)
  → R-input (init env) s
  → readReg (regs (dispatch-arith val-x86-32 (emit-program (compile-abs e)) s)) eax
      ≡ block-semM e (toWord sh env)
arith-dispatch-value e env s ri = arith-block-correct e env s ri
