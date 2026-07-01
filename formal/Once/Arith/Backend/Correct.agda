-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Arith.Backend.Correct  (width-parametric refinement scaffold)
--
-- Plan 0.53 — the per-AbstractInstr refinement obligation, factored out
-- of the (previously x86-64-only) Correct module so ALL arches share ONE
-- scaffold. Parameterised by:
--   * width  : the machine word width — x86-64/riscv64 → 64, x86-32 → 32;
--     threads into the abstract executor `Exec width` (so `step` compares
--     at the right word size — the gap that left x86-32 uncovered);
--   * the concrete machine  (XState / concretise / exec-x86), supplied per
--     arch by its Emit's (word-width, reg-map). Kept as parameters so each
--     backend instantiates with its own machine (x86-64 and riscv64 are
--     both width 64 but distinct machines), and so a later discharge can
--     replace the postulated triple with a real per-arch definition.
--
-- Obligation shape (per AbstractInstr):
--   ∀ s i. exec-x86 (emit i) (concretise s) ≡ concretise (step i s)
--
-- STATUS: SCAFFOLD (refine-* postulated). The `emit` compiler is the
-- arch-neutral `XInstr` one shared by all three backends; only `step`'s
-- width and the concrete machine vary — exactly the parameters here.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Arith.Machine.AbsState using (ArithAbsState; InputShape)
open import Once.Arith.Backend.XInstr.Syntax using (XProgram)

module Once.Arith.Backend.Correct
  (width      : ℕ)
  (XState     : InputShape → Set)
  (concretise : ∀ {sh} → ArithAbsState sh → XState sh)
  (exec-x86   : ∀ {sh} → XProgram → XState sh → XState sh)
  where

open import Data.Integer using (ℤ)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Arith.Machine.AbsState using (InputPath)
open import Once.Arith.Machine.AbsInstr
  using (AbstractInstr; load-input; load-imm; add-rrr; sub-rrr;
         mul-rrr; neg-rr; spill; reload; move-to-out; module Exec)
-- L1: executor `step` is width-parameterised at the module's `width`.
open Exec width using (step)
open import Once.Arith.Backend.XInstr.CodeGen using (emit)

------------------------------------------------------------------------
-- Per-AbstractInstr refinement (postulated until I-arith-4 discharge).
--
-- The top-level `refine` case-splits on `AbstractInstr` and dispatches to
-- per-ctor postulates. Adding an `AbstractInstr` constructor breaks
-- coverage of the dispatcher, forcing a matching scaffold entry in
-- lock-step with `emit` (CodeGen) and `step` (AbsInstr).
------------------------------------------------------------------------

postulate
  refine-load-input  : ∀ {sh} (p : InputPath) (r : ℕ) (s : ArithAbsState sh) →
    exec-x86 (emit (load-input p r))   (concretise s) ≡ concretise (step (load-input p r)   s)
  refine-load-imm    : ∀ {sh} (z : ℤ) (r : ℕ) (s : ArithAbsState sh) →
    exec-x86 (emit (load-imm z r))     (concretise s) ≡ concretise (step (load-imm z r)     s)
  refine-add-rrr     : ∀ {sh} (d a b : ℕ) (s : ArithAbsState sh) →
    exec-x86 (emit (add-rrr d a b))    (concretise s) ≡ concretise (step (add-rrr d a b)    s)
  refine-sub-rrr     : ∀ {sh} (d a b : ℕ) (s : ArithAbsState sh) →
    exec-x86 (emit (sub-rrr d a b))    (concretise s) ≡ concretise (step (sub-rrr d a b)    s)
  refine-mul-rrr     : ∀ {sh} (d a b : ℕ) (s : ArithAbsState sh) →
    exec-x86 (emit (mul-rrr d a b))    (concretise s) ≡ concretise (step (mul-rrr d a b)    s)
  refine-neg-rr      : ∀ {sh} (d a : ℕ) (s : ArithAbsState sh) →
    exec-x86 (emit (neg-rr d a))       (concretise s) ≡ concretise (step (neg-rr d a)       s)
  refine-spill       : ∀ {sh} (src sl : ℕ) (s : ArithAbsState sh) →
    exec-x86 (emit (spill src sl))     (concretise s) ≡ concretise (step (spill src sl)     s)
  refine-reload      : ∀ {sh} (sl dst : ℕ) (s : ArithAbsState sh) →
    exec-x86 (emit (reload sl dst))    (concretise s) ≡ concretise (step (reload sl dst)    s)
  refine-move-to-out : ∀ {sh} (src : ℕ) (s : ArithAbsState sh) →
    exec-x86 (emit (move-to-out src))  (concretise s) ≡ concretise (step (move-to-out src)  s)

refine :
  ∀ {sh} (i : AbstractInstr) (s : ArithAbsState sh) →
  exec-x86 (emit i) (concretise s) ≡ concretise (step i s)
refine (load-input p r)  s = refine-load-input  p r s
refine (load-imm z r)    s = refine-load-imm    z r s
refine (add-rrr d a b)   s = refine-add-rrr     d a b s
refine (sub-rrr d a b)   s = refine-sub-rrr     d a b s
refine (mul-rrr d a b)   s = refine-mul-rrr     d a b s
refine (neg-rr d a)      s = refine-neg-rr      d a s
refine (spill src sl)    s = refine-spill       src sl s
refine (reload sl dst)   s = refine-reload      sl dst s
refine (move-to-out src) s = refine-move-to-out src s
