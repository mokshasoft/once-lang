-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.ArithDispatchX86-64  (Plan 0.54 rung B / B2.4)
--
-- The ARITH SLICE of `conc-flat-sim`, at the whole-program DISPATCH layer.
-- `run-events`, on a `call once_arith.block.*`, runs `dispatch-arith` (=
-- `exec-arith-block` with a transparent pc bump) and emits NO event. The flat
-- model treats that block as one atomic Pure op. This module proves the arith
-- dispatch behaves exactly as that atomic op requires — combining the two
-- already-proven halves:
--   * VALUE  — `arith-block-correct` (the block leaves `block-semM (toWord env)`
--              in rax; regs are pc-transparent so it transfers to the dispatch);
--   * CCC    — `dispatch-arith-preserves` (registers + memory that CCC keeps
--              live across the call site are preserved).
-- (NO EVENT is structural in `run-events`: the arith-call branch emits `[]`.)
--
-- So the whole-program simulation's arith case is DISCHARGED here; the remaining
-- `conc-flat-sim` content is the NON-arith per-instruction correspondence (the
-- fuel-induction frame + the honest ISA axiom) — the large residual.
------------------------------------------------------------------------

module Once.Adequacy.ArchCorrectness.ArithDispatchX86-64 where

open import Data.Nat using (ℕ; _<_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Arith.Machine.Shape using (InputShape; ⟦_⟧S)
open import Once.Arith.Machine.AbsState using (init)
open import Once.Arith.Machine.IR using (MArithIR)
open import Once.Arith.Backend.XInstr.CodeGen using (emit-program)
open import Once.Arith.Machine.Compile using (compile-abs)
open import Once.Arith.SigOp.Block using (block-semM)
open import Once.Arith.SigOp.BlockSemBridge using (toWord)

open import Once.Target.X86-64.PhysReg using (rsp; rax)
open import Once.CCC.Target.X86-64.Semantics using (State; readReg)
open State using (regs)
open import Once.Adequacy.CPU.X86-64 using (val-x86-64)
open import Once.Arith.Backend.X86-64.StatePreserve using (PreservesCCCState)
open import Once.Arith.Backend.X86-64.Dispatch using (dispatch-arith; dispatch-arith-preserves)
open import Once.Adequacy.ArchCorrectness.ArithSimX86-64 using (arith-block-correct; R-input)

------------------------------------------------------------------------
-- The arith dispatch is CORRECT: it preserves CCC state AND leaves the real
-- block value in rax. Both halves at the SAME `exec-arith-block val-x86-64`
-- (dispatch's regs = the block's — the pc bump is a record update on pc only),
-- so `arith-block-correct` transfers to the dispatch by `regs`-transparency.
--
-- Precondition `R-input (init env) s` = the call-site laid the Int input out at
-- rdi (the CCC arg-passing convention); `0 < rsp` = the block has stack headroom.
------------------------------------------------------------------------

arith-dispatch-correct :
    ∀ {sh} (e : MArithIR sh) (env : ⟦ sh ⟧S) (s : State)
  → 0 < readReg (regs s) rsp
  → R-input (init env) s
  → PreservesCCCState (readReg (regs s) rsp) s
      (dispatch-arith val-x86-64 (emit-program (compile-abs e)) s)
  × ( readReg (regs (dispatch-arith val-x86-64 (emit-program (compile-abs e)) s)) rax
        ≡ block-semM e (toWord sh env) )
arith-dispatch-correct e env s 0<rsp ri =
    dispatch-arith-preserves val-x86-64 (emit-program (compile-abs e)) s 0<rsp
  , arith-block-correct e env s ri
