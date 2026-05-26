-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Arith.Backend.X86.Correct
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

module Once.Arith.Backend.X86.Correct where

open import Data.Nat using (ℕ)
open import Data.Integer using (ℤ)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Arith.Machine.AbsState using (ArithAbsState; InputShape; ⟦_⟧S)
open import Once.Arith.Machine.AbsInstr
  using (AbstractInstr; step)
open import Once.Arith.Backend.X86.Syntax using (XInstr; XProgram)
open import Once.Arith.Backend.X86.CodeGen using (emit)

------------------------------------------------------------------------
-- Bridge surface (postulated until I-arith-4 discharge)
------------------------------------------------------------------------

postulate
  XState     : InputShape → Set
  concretise : ∀ {sh} → ArithAbsState sh → XState sh
  exec-x86   : ∀ {sh} → XProgram → XState sh → XState sh

------------------------------------------------------------------------
-- Per-AbstractInstr refinement
------------------------------------------------------------------------

postulate
  refine :
    ∀ {sh} (i : AbstractInstr) (s : ArithAbsState sh) →
    exec-x86 (emit i) (concretise s) ≡ concretise (step i s)
