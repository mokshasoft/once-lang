-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Event — what is observed: one call of a generator.
--
-- SPEC. An event is the call of a generator of the signature — its resolved
-- name, its argument type (a base type: a value the ABI can pass) and the
-- argument. A program's behaviour is the sequence of its events.
------------------------------------------------------------------------

module Once.Spec.Event where

open import Once.Spec.Type using (Type)
open import Once.Spec.Type.WellFormed using (IsBaseType)
open import Once.Spec.Name using (CanonicalName)
open import Once.Spec.Word using (Carrier)
import Once.Spec.Value Carrier Carrier as M

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

