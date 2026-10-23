{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Internal.Type.WellFormed — base types, concrete types, well-formed functors,
-- and types without parameters.
------------------------------------------------------------------------

module Once.Internal.Type.WellFormed where

open import Once.Spec.Type using (Base; WFFun; ∅ₖ; b-Unit; b-Void; b-Int; b-Float; b-*; b-+; wf-K; wf-Id; wf-⊕; wf-⊗; Type; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; K; Id; _⊕_; _⊗_)

open import Once.Spec.Type using (Fun; μ; ν)

-- The base types and the well-formed functors are the Spec's (`Base`, `WFFun`), here at
-- the ground kinding context; the compiler's older constructor names stay while plan 0.122
-- renames their users.
IsBaseType : Type → Set
IsBaseType = Base ∅ₖ

pattern base-Unit = b-Unit
pattern base-Void = b-Void
pattern base-Int = b-Int
pattern base-Float = b-Float
pattern base-Prod a b = b-* a b
pattern base-Sum a b = b-+ a b

-- | The types an external operation may have: a base type, or a first-order
-- arrow between base types. An external operation takes and returns base
-- values; it never receives or returns a Once function, `μ` or `ν` value.
data IsConcrete : Type → Set where
  con-base : ∀ {A} → IsBaseType A → IsConcrete A
  con-fun  : ∀ {A B k} → IsBaseType A → IsBaseType B → IsConcrete (A ⇒[ k ] B)

-- | A functor is well formed when every constant in it is a base type.
WellFormedF : Fun 0 → Set
WellFormedF = WFFun ∅ₖ

pattern wf-Sum f g = wf-⊕ f g
pattern wf-Prod f g = wf-⊗ f g

