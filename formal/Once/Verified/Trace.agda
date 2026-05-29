-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Verified.Trace — the SigOp effect trace (Plan 0.24, Phase A).
--
-- The observable behaviour of a Once program is the sequence of SigOp
-- calls it performs, with their arguments — NOT a return value, and
-- NOT just an exit code (see `Once.Verified.Behavior` preamble and the
-- memory note "programs don't return values"). For reactive /
-- non-terminating programs that sequence is INFINITE, so the trace is
-- a COINDUCTIVE structure: a free monad / resumption over SigOps (an
-- "interaction tree").
--
--   `Eff A` is a (possibly infinite) computation that either returns an
--   `A` or performs a SigOp call (recording its `SigOpInfo` + argument)
--   and continues based on the SigOp's result.
--
-- Coinduction follows the codebase's `νS` style: a `coinductive`
-- record wrapping a one-step `EffStep`, with `--guardedness`.
--
-- This module defines only the trace TYPE, an observable event
-- projection, and the Layer-0 `exitCode` projection. Bisimilarity
-- (`_≈_`) and the IR trace denotation `⟦_⟧tr` land in later phases.
------------------------------------------------------------------------

module Once.Verified.Trace where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.String using (String) renaming (_≟_ to _≟str_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (Type; Int)
open import Once.CCC.SigOp.Info using (SigOpInfo; name; semM)
import Once.Semantics.Core ℕ as M

------------------------------------------------------------------------
-- The trace type: a coinductive resumption / interaction tree.
--
-- A `call si arg k` records the SigOp `si` invoked with argument `arg`
-- (a machine value `M.⟦ D ⟧`) and continues with `k`, which consumes
-- the SigOp's result (`M.⟦ R ⟧`). SigOps that return data (e.g.
-- `linux.read`) thus drive subsequent control flow; the trace is a
-- tree indexed by responses, linear when there is no input.
------------------------------------------------------------------------

mutual
  record Eff (A : Set) : Set where
    coinductive
    field force : EffStep A

  data EffStep (A : Set) : Set where
    ret  : A → EffStep A
    call : ∀ {D R : Type} → SigOpInfo D R → M.⟦ D ⟧ → (M.⟦ R ⟧ → Eff A) → EffStep A

open Eff public

------------------------------------------------------------------------
-- Observable events.
--
-- An event records a SigOp's name and, when its input type is `Int`,
-- the ℕ argument (the only observable argument shape Layer 0 needs;
-- richer arg observables are future work).
------------------------------------------------------------------------

-- | Recognise the `Int` domain so an `Int`-argument SigOp's value can
-- be observed as a ℕ. (`M.⟦ Int ⟧ = ℕ`.)
isInt? : (D : Type) → Maybe (D ≡ Int)
isInt? Int = just refl
isInt? _   = nothing

record SigOpEvent : Set where
  constructor mk-event
  field
    ev-name : String
    ev-argℕ : Maybe ℕ   -- the argument as ℕ, when the SigOp's input is Int

mkEvent : ∀ {D R} → SigOpInfo D R → M.⟦ D ⟧ → SigOpEvent
mkEvent {D} si arg with isInt? D
... | just refl = mk-event (name si) (just arg)
... | nothing   = mk-event (name si) nothing

------------------------------------------------------------------------
-- Determinate event list (fuel-bounded).
--
-- For an input-free program every SigOp's result is its machine
-- semantics `semM si arg`, so the trace has a single determinate run.
-- `events n` returns that run's events, up to `n` steps (a total
-- approximation of the possibly-infinite trace).
------------------------------------------------------------------------

events : ∀ {A} → ℕ → Eff A → List SigOpEvent
events zero    _ = []
events (suc n) e with force e
... | ret _         = []
... | call si arg k = mkEvent si arg ∷ events n (k (semM si arg))

------------------------------------------------------------------------
-- Layer-0 exit-code projection.
--
-- Walk the determinate run (feeding each SigOp its `semM` result) up to
-- `n` steps; return the argument of the first `linux.exit` call. This
-- is the COARSE Layer-0 observable — the full observable is `events` /
-- the trace itself. A program that never calls `linux.exit` within the
-- budget yields `nothing`.
------------------------------------------------------------------------

exitCode : ∀ {A} → ℕ → Eff A → Maybe ℕ
exitCode zero    _ = nothing
exitCode (suc n) e with force e
... | ret _ = nothing
... | call {D} si arg k with name si ≟str "linux.exit" | isInt? D
...   | yes _ | just refl = just arg
...   | _     | _         = exitCode n (k (semM si arg))
