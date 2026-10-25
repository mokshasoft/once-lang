{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Internal.Type.WellFormed — concrete types.
------------------------------------------------------------------------

module Once.Internal.Type.WellFormed where

open import Once.Spec.Type using (Base; WFFun; ∅ₖ; b-Unit; b-Void; b-Int; b-Float; b-*; b-+; wf-K; wf-Id; wf-⊕; wf-⊗; Type; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; K; Id; _⊕_; _⊗_)

open import Once.Spec.Type using (Fun; μ; ν)

-- A concrete type: a base type (the Spec's `Base ∅ₖ`), or an arrow between two.
data IsConcrete : Type → Set where
  con-base : ∀ {A} → Base ∅ₖ A → IsConcrete A
  con-fun  : ∀ {A B k} → Base ∅ₖ A → Base ∅ₖ B → IsConcrete (A ⇒[ k ] B)
