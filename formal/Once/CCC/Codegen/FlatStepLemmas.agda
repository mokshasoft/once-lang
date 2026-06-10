-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Codegen.FlatStepLemmas — opaque-state step API for the flat
-- abstract machine `exec-flat` (Plan 0.36, task #8 foundation).
--
-- This is the `exec-flat` analogue of the X86-64 `StepLemmas` API that
-- the deleted `CataIsEvenInduction` POC used to prove the cata loop↔fold
-- ∀-n. The technique (per the prior POCs + `feedback_fuel_cpu_induction
-- _technique`): reason over OPAQUE states, peel a FIXED number of steps
-- off SYMBOLIC fuel via a chain combinator, then μ-induct on the input.
--
-- The peel primitive already exists: `FlatMachine.exec-flat-step` (the
-- `exec-1` analogue). Here we add `FlatSteps`/`exec-flat-steps` — the
-- chain combinator (mirrors `StepLemmas.Steps`/`exec-steps`) — over
-- which the descend/base/ascend phases of the cata loop are reasoned
-- once each (not unrolled per input). `flat-exec-instr` is itself the
-- abstract per-instruction semantics, so each step's "next state" is
-- forced (no free `s'`, unlike the real-CPU `step-not-halted ≡ just s'`).
------------------------------------------------------------------------

module Once.CCC.Codegen.FlatStepLemmas where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (false)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore using (halted; AbstractInstr; AbstractTrace)
open import Once.CCC.Machine.Flat using (module FlatMachine)

module FlatStepsAPI {FS : FrameSemantics} where
  open FlatMachine {FS}

  -- A chain of `k` non-halted `exec-flat` steps from `fs` to `fs'`. Each
  -- link carries its halted+fetch evidence; the next state is forced by
  -- `flat-exec-instr i prog fs` (opaque — never destructured).
  data FlatSteps (prog : AbstractTrace) : ℕ → FlatState → FlatState → Set where
    []  : ∀ {fs} → FlatSteps prog 0 fs fs
    _∷_ : ∀ {fs k fs'} {i : AbstractInstr}
        → (halted (floc fs) ≡ false × fetch prog (fpc fs) ≡ just i)
        → FlatSteps prog k (flat-exec-instr i prog fs) fs'
        → FlatSteps prog (suc k) fs fs'

  infixr 5 _∷_

  -- Peel a whole chain off the fuel (mirrors `StepLemmas.exec-steps`):
  -- a `k`-step chain reduces `exec-flat (k + b)` from `fs` to
  -- `exec-flat b` from `fs'`.
  exec-flat-steps : ∀ {prog k fs fs'} → FlatSteps prog k fs fs'
                  → ∀ b → exec-flat (k + b) prog fs ≡ exec-flat b prog fs'
  exec-flat-steps []                           b = refl
  exec-flat-steps (_∷_ {k = k} {i = i} (h , f) rest) b =
    trans (exec-flat-step (k + b) _ _ i h f) (exec-flat-steps rest b)
