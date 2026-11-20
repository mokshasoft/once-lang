{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Type.Concrete — concrete types.
------------------------------------------------------------------------

module Once.Type.Concrete where

open import Once.Spec.Type using (Base; ∅ₖ; Type; _⇒[_]_)


-- A concrete type: a base type (the Spec's `Base ∅ₖ`), or an arrow between two.
data IsConcrete : Type → Set where
  con-base : ∀ {A} → Base ∅ₖ A → IsConcrete A
  con-fun  : ∀ {A B k} → Base ∅ₖ A → Base ∅ₖ B → IsConcrete (A ⇒[ k ] B)
