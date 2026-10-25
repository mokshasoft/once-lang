-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Internal.Event — what is observed: one call of a generator.
--
-- INTERNAL (D333). An event is the call of a generator of the signature — its resolved
-- name, its argument type (a base type: a value the ABI can pass) and the
-- argument. A program's behaviour is the sequence of its events.
------------------------------------------------------------------------

module Once.Internal.Event where

open import Once.Spec.Type using (Type)
open import Once.Spec.Type using (Base; b-*; b-+; b-Float; b-Int; b-Unit; b-Void; ∅ₖ)
open import Once.Spec.Name using (CanonicalName)
open import Once.Spec.Word using (Carrier)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
import Once.Internal.Value Carrier Carrier as M

record SigOpEvent : Set where
  constructor mk-event
  field
    ev-name  : CanonicalName   -- Plan 0.50: the resolved identity (was String)
    ev-dom   : Type            -- the SigOp's argument type
    -- IRRELEVANT: `Base ∅ₖ` is an h-prop in practice, and two events with
    -- the same name, domain and value must be `≡` regardless of which witness
    -- they carry. It is kept rather than dropped because it is what rules out
    -- an `ev-dom` whose `⟦_⟧` is a function type — an observation the ABI
    -- could not pass and no funext-free bridge could relate. `SigOpInfo.baseA`
    -- already calls itself proof-irrelevant; this makes that enforceable.
    .ev-base : Base ∅ₖ ev-dom
    ev-arg   : M.⟦ ev-dom ⟧


------------------------------------------------------------------------
-- The Spec's event (D320, plan 0.119 §7 D4): the argument type read as a base
-- type, the argument as its value. A type parameter has no values, so its
-- events are read at `void`.
------------------------------------------------------------------------

import Once.Internal.Type as T
import Once.Spec.Type as T

import Once.Spec.Type as T
import Once.Spec.Signature as S

private
  baseˡ : ∀ {A B} → Base ∅ₖ (A T.* B) → Base ∅ₖ A
  baseˡ (b-* a _) = a
  baseʳ : ∀ {A B} → Base ∅ₖ (A T.* B) → Base ∅ₖ B
  baseʳ (b-* _ b) = b
  sumˡ : ∀ {A B} → Base ∅ₖ (A T.+ B) → Base ∅ₖ A
  sumˡ (b-+ a _) = a
  sumʳ : ∀ {A B} → Base ∅ₖ (A T.+ B) → Base ∅ₖ B
  sumʳ (b-+ _ b) = b

baseOf : (A : Type) → .(Base ∅ₖ A) → S.BTy
baseOf T.Unit           _ = S.unit
baseOf T.Void           _ = S.void
baseOf T.Int            _ = S.int
baseOf T.Float          _ = S.float
baseOf (A T.* B)        b = baseOf A (baseˡ b) S.* baseOf B (baseʳ b)
baseOf (A T.+ B)        b = baseOf A (sumˡ b) S.+ baseOf B (sumʳ b)
baseOf (_ T.⇒[ _ ] _)   ()
baseOf (T.μ _)     ()
baseOf (T.ν _ _)   ()

valOf : (A : Type) → .(b : Base ∅ₖ A) → M.⟦ A ⟧ → S.⟦ baseOf A b ⟧ᵇ
valOf T.Unit        _ v = v
valOf T.Void        _ v = v
valOf T.Int         _ v = v
valOf T.Float       _ v = v
valOf (A T.* B)     b (x , y)  = valOf A (baseˡ b) x , valOf B (baseʳ b) y
valOf (A T.+ B)     b (inj₁ x) = inj₁ (valOf A (sumˡ b) x)
valOf (A T.+ B)     b (inj₂ y) = inj₂ (valOf B (sumʳ b) y)
valOf (_ T.⇒[ _ ] _) ()
valOf (T.μ _)   ()
valOf (T.ν _ _) ()

toEvent : SigOpEvent → S.Event
toEvent (mk-event n A b v) = S.event n (baseOf A b) (valOf A b v)
