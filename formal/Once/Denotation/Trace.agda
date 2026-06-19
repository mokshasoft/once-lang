-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Denotation.Trace — SigOp effect events (Plan 0.24, Phase A′).
--
-- The observable behaviour of a Once program is the sequence of SigOp
-- calls it performs, with their arguments — NOT a return value, NOT an
-- exit code (see `Once.Denotation.Behavior` preamble and the memory note
-- "programs don't return values"). The exit code is just the argument
-- of the program's `linux.exit` call, recovered from the event list.
--
-- A (possibly infinite) trace is represented by the OBSERVATION-DEPTH-
-- INDEXED denotation `Once.Denotation.DenotTrace.evalᴰ` (via `projTrace`)
-- as the family of its finite prefixes (a `List SigOpEvent` per depth
-- bound). This avoids coinduction and sized types; productive programs
-- are handled by proving agreement at every bound (the take-lemma). This
-- module defines the finite event vocabulary; the denotation is in
-- `DenotTrace` (the retired operational `obs` reader once lived in
-- `TraceDenote`, now reduced to shared event helpers).
------------------------------------------------------------------------

module Once.Denotation.Trace where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.String using (String) renaming (_≟_ to _≟str_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (Type; Int)
open import Once.CCC.SigOp.Info using (SigOpInfo; name)
import Once.Semantics.Core ℕ as M

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

open SigOpEvent public

mkEvent : ∀ {D R} → SigOpInfo D R → M.⟦ D ⟧ → SigOpEvent
mkEvent {D} si arg with isInt? D
... | just refl = mk-event (name si) (just arg)
... | nothing   = mk-event (name si) nothing

------------------------------------------------------------------------
-- Exit-code projection: the argument of the first `linux.exit` event
-- in a (finite) trace prefix. The coarse Layer-0 observable — the full
-- observable is the event list itself.
------------------------------------------------------------------------

exitCodeOf : List SigOpEvent → Maybe ℕ
exitCodeOf []       = nothing
exitCodeOf (e ∷ es) with ev-name e ≟str "linux.exit"
... | yes _ = ev-argℕ e
... | no _  = exitCodeOf es
