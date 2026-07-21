-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.ArithSimX86-64  (Plan 0.54 rung B / B2.3)
--
-- The x86-64 INSTANCE of the arch-generic arith concrete↔abstract simulation
-- (`ArithSimCore.Core`). All the content — R / R-scratch / R-input, the 16
-- R-step cases, R-sim / Rf-sim, the Rf assembly, `result-correct` / `R-init`,
-- and the `arith-block-correct` capstone — lives in the core and is re-exported
-- here (`open Core … public`). This module supplies only the x86-64 surface:
--   * the concrete machine (`X64.State` / readReg / writeReg / readMem / def /
--     scratch-addr / path-load / val-x86-64's exec1 & block fold);
--   * the arch's frame lemmas (the 4×4 analysis on r8–r11);
--   * the block-fold reductions and the 16 `ce-*` val-mirror equations — all
--     `refl`, since `val-x86-64` was DEFINED to mirror `exec-xinstr`.
------------------------------------------------------------------------

module Once.Adequacy.ArchCorrectness.ArithSimX86-64 where

open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim)

open import Once.Arith.Backend.XInstr.Syntax as XI using (XInstr; XReg; XScratch)
open XI using (XR0; XR1; XR2; XR3)
open import Once.Target.X86-64.PhysReg using (Reg; rax; rdx; r8; r9; r10; r11)
open import Once.Arith.Backend.X86-64.Emit using (arith-reg)
import Once.CCC.Target.X86-64.Semantics as X64
open X64 using (State; readReg; writeReg; readMem; RegFile; Word)
open X64.State using (regs; memory)
open import Once.Adequacy.CPU.X86-64 using (val-x86-64; scratch-addr; def; path-load)
import Once.Arith.Backend.X86-64.ExecArith as EA

------------------------------------------------------------------------
-- Frame machinery for the arithmetic R-step cases. R only ever reads
-- `arith-reg` registers (r8-r11), so `writeReg-other` is a 4×4 analysis.
------------------------------------------------------------------------

readReg-wr-arith-other : ∀ (rf : RegFile) (x y : XReg) (v : Word)
                       → ¬ (x ≡ y)
                       → readReg (writeReg rf (arith-reg x) v) (arith-reg y)
                           ≡ readReg rf (arith-reg y)
readReg-wr-arith-other rf XR0 XR0 v ¬eq = ⊥-elim (¬eq refl)
readReg-wr-arith-other rf XR0 XR1 v _ = refl
readReg-wr-arith-other rf XR0 XR2 v _ = refl
readReg-wr-arith-other rf XR0 XR3 v _ = refl
readReg-wr-arith-other rf XR1 XR0 v _ = refl
readReg-wr-arith-other rf XR1 XR1 v ¬eq = ⊥-elim (¬eq refl)
readReg-wr-arith-other rf XR1 XR2 v _ = refl
readReg-wr-arith-other rf XR1 XR3 v _ = refl
readReg-wr-arith-other rf XR2 XR0 v _ = refl
readReg-wr-arith-other rf XR2 XR1 v _ = refl
readReg-wr-arith-other rf XR2 XR2 v ¬eq = ⊥-elim (¬eq refl)
readReg-wr-arith-other rf XR2 XR3 v _ = refl
readReg-wr-arith-other rf XR3 XR0 v _ = refl
readReg-wr-arith-other rf XR3 XR1 v _ = refl
readReg-wr-arith-other rf XR3 XR2 v _ = refl
readReg-wr-arith-other rf XR3 XR3 v ¬eq = ⊥-elim (¬eq refl)

readReg-wr-arith-same : ∀ (rf : RegFile) (x : XReg) (v : Word)
                      → readReg (writeReg rf (arith-reg x) v) (arith-reg x) ≡ v
readReg-wr-arith-same rf XR0 v = refl
readReg-wr-arith-same rf XR1 v = refl
readReg-wr-arith-same rf XR2 v = refl
readReg-wr-arith-same rf XR3 v = refl

readReg-wr-rax-arith : ∀ (rf : RegFile) (x : XReg) (v : Word)
                     → readReg (writeReg rf rax v) (arith-reg x) ≡ readReg rf (arith-reg x)
readReg-wr-rax-arith rf XR0 v = refl
readReg-wr-rax-arith rf XR1 v = refl
readReg-wr-rax-arith rf XR2 v = refl
readReg-wr-rax-arith rf XR3 v = refl

readReg-wr-rdx-arith : ∀ (rf : RegFile) (x : XReg) (v : Word)
                     → readReg (writeReg rf rdx v) (arith-reg x) ≡ readReg rf (arith-reg x)
readReg-wr-rdx-arith rf XR0 v = refl
readReg-wr-rdx-arith rf XR1 v = refl
readReg-wr-rdx-arith rf XR2 v = refl
readReg-wr-rdx-arith rf XR3 v = refl

readReg-wr-rax-same : ∀ (rf : RegFile) (v : Word) → readReg (writeReg rf rax v) rax ≡ v
readReg-wr-rax-same rf v = refl

------------------------------------------------------------------------
-- The instance. Every `ce-*` / `eb-*` / `def-just` is `refl` — `val-x86-64`
-- mirrors `exec-xinstr` and the block fold peels the head in lockstep.
------------------------------------------------------------------------

open import Once.Adequacy.ArchCorrectness.ArithSimCore using (module Core)

open Core
  State RegFile Reg
  regs readReg writeReg
  (λ s addr → readMem (memory s) addr)
  arith-reg rax rdx
  def (λ _ → refl)
  scratch-addr path-load
  (EA.exec1 val-x86-64) (EA.exec-arith-block val-x86-64)
  (λ _ → refl) (λ _ _ _ → refl)
  readReg-wr-arith-same readReg-wr-arith-other
  readReg-wr-rax-arith readReg-wr-rdx-arith readReg-wr-rax-same
  -- ce-mov-imm ce-mov-rr ce-spill ce-reload
  (λ _ _ _ → refl) (λ _ _ _ → refl) (λ _ _ _ → refl) (λ _ _ _ → refl)
  -- ce-arg ce-add ce-sub ce-imul
  (λ _ _ _ → refl) (λ _ _ _ → refl) (λ _ _ _ → refl) (λ _ _ _ → refl)
  -- ce-neg ce-shl
  (λ _ _ → refl) (λ _ _ _ _ → refl)
  -- ce-div ce-rem ce-div-safe ce-rem-safe
  (λ _ _ _ _ → refl) (λ _ _ _ _ → refl) (λ _ _ _ _ → refl) (λ _ _ _ _ → refl)
  -- ce-sdiv ce-out
  (λ _ _ _ _ → refl) (λ _ _ → refl)
  public
