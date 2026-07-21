-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.ArithSimX86-64  (Plan 0.54 rung B / B2.3 pieces 1-2)
--
-- The representation relation `R` between the abstract arith machine
-- (`ArithAbsState`, machine 2) and the concrete x86-64 machine (`X64.State`,
-- machine 3), and the block simulation over it.
--
-- `val-x86-64` was DEFINED to mirror `exec-xinstr` (same ops/reads), so the
-- per-instruction step (`R-step`) is near-definitional for the arithmetic
-- instructions; the memory instructions (spill/reload/arg) additionally need the
-- scratch/input correspondence (to be folded into `R`). `R-sim` composes the
-- step over a whole block by induction (PROVED), reducing B2.3's simulation to
-- `R-step`.
--
-- Combined with `block-value-semM` (the abstract output = `block-semM (toWord
-- env)`), `R` transfers that value to the concrete result register — the
-- arith-block case of `conc-flat-sim` (B2.4).
------------------------------------------------------------------------

module Once.Adequacy.ArchCorrectness.ArithSimX86-64 where

open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Arith.Backend.XInstr.Syntax using (XInstr; XReg)
open import Once.Arith.Machine.Shape using (InputShape)
open import Once.Arith.Machine.AbsState using (ArithAbsState; Store; _[_])
import Once.Arith.Backend.Correct as Correct
open Correct 64 using (exec-xinstr; exec-xprog; xreg-idx)
open import Once.Target.X86-64.PhysReg using (Reg)
open import Once.Arith.Backend.X86-64.Emit using (arith-reg)
import Once.CCC.Target.X86-64.Semantics as X64
open X64 using (State; readReg)
open X64.State using (regs)
open import Once.Adequacy.CPU.X86-64 using (val-x86-64)
import Once.Arith.Backend.X86-64.ExecArith as EA

------------------------------------------------------------------------
-- R — the register correspondence (piece 1, register part).
--
-- Every DEFINED abstract register cell matches the concrete register, via the
-- `xreg-idx` (abstract store index) ↔ `arith-reg` (physical reg) mapping.
-- (Scratch + input correspondence are the reload/arg extensions, TODO.)
------------------------------------------------------------------------

R : ∀ {sh} → ArithAbsState sh → State → Set
R s-abs s-conc =
  ∀ (x : XReg) (w : ℕ)
  → (ArithAbsState.regs s-abs [ xreg-idx x ]) ≡ just w
  → w ≡ readReg (regs s-conc) (arith-reg x)

------------------------------------------------------------------------
-- The per-instruction step (piece 2). NEAR-DEFINITIONAL for arithmetic
-- instructions (`val` mirrors `exec-xinstr`); memory instructions need R's
-- scratch/input extension. Named obligation for now.
------------------------------------------------------------------------

postulate
  R-step : ∀ {sh} (i : XInstr) (s-abs : ArithAbsState sh) (s-conc : State)
         → R s-abs s-conc → R (exec-xinstr i s-abs) (EA.exec1 val-x86-64 i s-conc)

------------------------------------------------------------------------
-- The block simulation — PROVED by induction, reducing to `R-step`. Both folds
-- (`exec-xprog` abstract, `exec-arith-block` concrete) peel the head instruction
-- in lockstep, so the cons case threads `R-step` then recurses.
------------------------------------------------------------------------

R-sim : ∀ {sh} (xs : List XInstr) (s-abs : ArithAbsState sh) (s-conc : State)
      → R s-abs s-conc
      → R (exec-xprog xs s-abs) (EA.exec-arith-block val-x86-64 xs s-conc)
R-sim []       s-abs s-conc r = r
R-sim (i ∷ is) s-abs s-conc r =
  R-sim is (exec-xinstr i s-abs) (EA.exec1 val-x86-64 i s-conc) (R-step i s-abs s-conc r)
