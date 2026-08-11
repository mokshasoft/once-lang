-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Grammar.PolyTypeBridge — bridges the bounded `parsePolyTypeB` (the live
-- PolyType parser) to the independent generic relation `ParsesPolyType`. Both
-- directions, via the de-`with`'d `ppB-go` helper (the `parsePolyTypeP` result
-- is a parameter, so we case it concretely and apply at the stuck term). The
-- foundation for the three PolyType-dependent decl bridges. Plan 0.7-2.
------------------------------------------------------------------------

module Once.Grammar.PolyTypeBridge where

open import Data.List using (List; length)
open import Data.Nat using (_<_)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Once.Type using (PolyType)
open import Once.Parser.Token
open import Once.Parser.PolyType using (parsePolyTypeB; ppB-go)
open import Once.Parser.Generic.PolyInst
  using (ParsesPolyType; parsePolyTypeP; sound-polyType; complete-polyType; ParsesPolyType-shrink)

-- Soundness: whatever the bounded parser accepts is in the relation.
ppB-go-sound : ∀ (toks : List Token) (r : _) (pf : parsePolyTypeP toks ≡ r) {t rest bnd} →
  ppB-go toks r pf ≡ just (t , rest , bnd) → ParsesPolyType toks t rest
ppB-go-sound toks (just (t , rest)) pf h with refl ← h =
  sound-polyType toks (<-wellFounded (length toks)) pf

parsePolyTypeB-sound : ∀ {toks t rest bnd} →
  parsePolyTypeB toks ≡ just (t , rest , bnd) → ParsesPolyType toks t rest
parsePolyTypeB-sound {toks} h = ppB-go-sound toks (parsePolyTypeP toks) refl h

-- Completeness: every derivation is found, with the structural bound.
ppB-go-complete : ∀ (toks : List Token) (r : _) (pf : parsePolyTypeP toks ≡ r) {t rest} →
  ParsesPolyType toks t rest →
  Σ[ bnd ∈ (length rest < length toks) ] ppB-go toks r pf ≡ just (t , rest , bnd)
ppB-go-complete toks nothing pf d with trans (sym pf) (complete-polyType d)
... | ()
ppB-go-complete toks (just (t' , rest')) pf d
  with refl ← just-injective (trans (sym pf) (complete-polyType d)) = _ , refl

parsePolyTypeB-complete : ∀ {toks t rest} → ParsesPolyType toks t rest →
  Σ[ bnd ∈ (length rest < length toks) ] parsePolyTypeB toks ≡ just (t , rest , bnd)
parsePolyTypeB-complete {toks} d = ppB-go-complete toks (parsePolyTypeP toks) refl d
