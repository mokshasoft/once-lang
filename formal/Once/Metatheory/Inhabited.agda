{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Inhabited — worlds exist, and an honest signature has a
-- model (`Spec.Metatheory.Inhabited`).
--
-- A world answers each call with an inhabitant of the answer type, which
-- exists exactly when it is asked for. An honest declaration of a value has
-- an inhabited result type, so the model returns an inhabitant.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)

module Once.Metatheory.Inhabited (Σ : Signature) where

open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (refl)
open import Once.Spec.Signature
  using (Decl; module Decl; WellFormed; []; _∷_; WellFormedDecl; _∶_; constant; value)
open import Once.Metatheory.Inhabitant using (inhabitant)
open import Once.Spec.Observation Σ using (Model)
open import Once.Spec.Metatheory using (Inhabited)
open import Once.Metatheory.Coherence.Relation Σ using (aWorld)

private
  -- An honest signature's declarations are honest.
  honest : ∀ {Σ₀ : Signature} {d} → WellFormed Σ₀ → d ∈ Σ₀ → WellFormedDecl (Decl.type d)
  honest (w ∷ ws) (here refl) = w
  honest (w ∷ ws) (there p)   = honest ws p

  aModel : WellFormed Σ → Model
  aModel ws = record
    { constantᵐ = λ {c} {b} p → inhabitant b (proj₁ (honest ws p))
    ; valueᵐ    = λ {c} {a} {q} {b} p _ → inhabitant b (proj₁ (honest ws p))
    }

inhabited : Inhabited Σ
inhabited = record { a-world = aWorld ; a-model = aModel }
