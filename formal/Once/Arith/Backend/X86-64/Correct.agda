-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Arith.Backend.X86-64.Correct
--
-- Plan 0.20 Phase D — per-AbstractInstr refinement.
--
-- *** STATUS: SCAFFOLD (signatures only) ***
--
-- D-arith-4 (Refinement layer): for each `AbstractInstr` and each
-- target arch, the concrete instructions emitted refine the abstract
-- transition. Statement shape:
--
--   ∀ s i. exec-x86 (emit i) (concretise s) ≡ concretise (step i s)
--
-- This file lays out the obligation. Per I-arith-4 the discharge
-- reuses + extends `Once.CCC.Target.X86-64.Semantics` rather than
-- shipping a parallel arith-only semantics; that follows the CPU-
-- semantics-extraction plan.
------------------------------------------------------------------------

module Once.Arith.Backend.X86-64.Correct where

open import Data.Nat using (ℕ)
open import Data.Integer using (ℤ)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Arith.Machine.AbsState using (ArithAbsState; InputShape; ⟦_⟧S; InputPath)
open import Once.Arith.Machine.AbsInstr
  using (AbstractInstr; load-input; load-imm; add-rrr; sub-rrr;
         mul-rrr; neg-rr; spill; reload; move-to-out; module Exec)
-- L1: executor `step` is width-parameterised; x86-64 backend → 64.
open Exec 64 using (step)
open import Once.Arith.Backend.XInstr.Syntax using (XInstr; XProgram)
open import Once.Arith.Backend.XInstr.CodeGen using (emit)

------------------------------------------------------------------------
-- Bridge surface (postulated until I-arith-4 discharge)
------------------------------------------------------------------------

postulate
  XState     : InputShape → Set
  concretise : ∀ {sh} → ArithAbsState sh → XState sh
  exec-x86   : ∀ {sh} → XProgram → XState sh → XState sh

------------------------------------------------------------------------
-- Per-AbstractInstr refinement
--
-- Structural scaffold (Plan 0.20 follow-up, 2026-05-27): the top-level
-- `refine` case-splits on `AbstractInstr` and dispatches to per-ctor
-- postulates. Adding a new `AbstractInstr` constructor breaks coverage
-- of the dispatcher, forcing a matching scaffold entry in lock-step
-- with the operational layer (`emit` in CodeGen, `step` in AbsInstr).
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
