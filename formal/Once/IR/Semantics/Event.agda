-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.IR.Semantics.Event — what is observed: one call of a generator.
--
-- IR'S OWN (D336). An event is the call of a generator of the signature — its resolved
-- name, its argument type (a base type: a value the ABI can pass) and the
-- argument. A program's behaviour is the sequence of its events.
------------------------------------------------------------------------

module Once.IR.Semantics.Event where

open import Once.Spec.Type using (Type)
open import Once.Spec.Type using (Base; b-*; b-+; b-Float; b-Int; b-Unit; b-Void; ∅ₖ)
open import Once.Spec.Name using (CanonicalName)
open import Once.Spec.Word using (Carrier)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
import Once.IR.Semantics.Value Carrier Carrier as M
open import Once.Spec.Float.Dyadic using (FloatFormat)
open import Once.Spec.Float.Encoding using (decode)

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
-- events are read at `void`. A `Float` argument is a word here and a level-2
-- value in the Spec: it is read by `decode` at the target's format (plan 0.150).
------------------------------------------------------------------------

import Once.Type.Core as T
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

valOf : FloatFormat → (A : Type) → .(b : Base ∅ₖ A) → M.⟦ A ⟧ → S.⟦ baseOf A b ⟧ᵇ
valOf F T.Unit        _ v = v
valOf F T.Void        _ v = v
valOf F T.Int         _ v = v
valOf F T.Float       _ v = decode F v
valOf F (A T.* B)     b (x , y)  = valOf F A (baseˡ b) x , valOf F B (baseʳ b) y
valOf F (A T.+ B)     b (inj₁ x) = inj₁ (valOf F A (sumˡ b) x)
valOf F (A T.+ B)     b (inj₂ y) = inj₂ (valOf F B (sumʳ b) y)
valOf F (_ T.⇒[ _ ] _) ()
valOf F (T.μ _)   ()
valOf F (T.ν _ _) ()

toEvent : FloatFormat → SigOpEvent → S.Event
toEvent F (mk-event n A b v) = S.event n (baseOf A b) (valOf F A b v)
