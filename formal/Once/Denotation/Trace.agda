-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.Trace — SigOp effect events (Plan 0.24, Phase A′).
--
-- The observable behaviour of a Once program is the sequence of SigOp
-- calls it performs, with their arguments — NOT a return value, NOT an
-- exit code (see `Once.Denotation.Behavior` preamble and the memory note
-- "programs don't return values"). The exit code is just the argument
-- of the program's exit-syscall call, recovered from the event list.
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
open import Once.Functor.Translate using (IsBaseType)
open import Once.SigOp.Info using (SigOpInfo; name; baseA)
open import Once.CanonicalName using (CanonicalName)
open import Once.Word using (Carrier)
open import Once.Float.Dyadic using (Dyadic)
import Once.Semantics.Value Carrier Carrier as M

------------------------------------------------------------------------
-- Observable events.
--
-- An event records a SigOp's name and ITS ARGUMENT, at the argument's own
-- base type (D114). This is SPEC: it declares which two programs count as
-- behaviourally equal, so `Once.Spec.Meaning` re-exports this module.
--
-- It used to record the argument only when the domain was syntactically
-- `Int`, which made `print "hello"` and `print "goodbye"` the same behaviour
-- (and `emitF 0.5` the same as `emitF 2.75`). Both sides of the correspondence
-- carried that gate, and the machine side said why: "so the two sides can be
-- proven equal". The claim had been narrowed to fit its proof.
--
-- WHY THE ARGUMENT'S OWN TYPE, and not a machine word: for `Str`/`Buffer`/
-- products the register holds an ADDRESS, and an address is a lowering
-- artifact — two correct compilers with different heap layouts would then have
-- different behaviours. Observing `⟦ A ⟧` says what the program DID; observing
-- the register says how this target passed it. At the scalars the two coincide
-- (`⟦ Int ⟧ = ⟦ Float ⟧ = Carrier`), which is D113's dividend: because a
-- numeric denotation IS the target's representation, nothing is lost.
--
-- There is no dispatch left, so `isInt?` and `mkEvent-name` are gone. They
-- existed only to keep the old `with isInt? D` reducing on an abstract domain.
------------------------------------------------------------------------

record SigOpEvent : Set where
  constructor mk-event
  field
    ev-name  : CanonicalName   -- Plan 0.50: the resolved identity (was String)
    ev-dom   : Type            -- the SigOp's argument type
    -- IRRELEVANT: `IsBaseType` is an h-prop in practice, and two events with
    -- the same name, domain and value must be `≡` regardless of which witness
    -- they carry. It is kept rather than dropped because it is what rules out
    -- an `ev-dom` whose `⟦_⟧` is a function type — an observation the ABI
    -- could not pass and no funext-free bridge could relate. `SigOpInfo.baseA`
    -- already calls itself proof-irrelevant; this makes that enforceable.
    .ev-base : IsBaseType ev-dom
    ev-arg   : M.⟦ ev-dom ⟧

open SigOpEvent public

-- Every `SigOpInfo` carries `baseA : IsBaseType A`, so the witness is already
-- to hand and this needs no dispatch: it reduces on an abstract domain.
mkEvent : ∀ {D R} → SigOpInfo D R → M.⟦ D ⟧ → SigOpEvent
mkEvent {D} si arg = mk-event (name si) D (baseA si) arg
