{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Internal.Type.WellFormed — base types, concrete types, well-formed functors,
-- and types without parameters.
------------------------------------------------------------------------

module Once.Internal.Type.WellFormed where

open import Once.Spec.Type using (Base; WFFun; ∅ₖ; b-Unit; b-Void; b-Int; b-Float; b-*; b-+; wf-K; wf-Id; wf-⊕; wf-⊗; Type; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; K; Id; _⊕_; _⊗_)

open import Once.Internal.Type using (μ-type; ν-type; Functor)

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
WellFormedF : Functor → Set
WellFormedF = WFFun ∅ₖ

pattern wf-Sum f g = wf-⊕ f g
pattern wf-Prod f g = wf-⊗ f g

-- | A type with no type parameter in it. Every ground `Type` is one (plan
-- 0.122: a parameter is a `var` of `Ty m`, never part of a `Type`); the
-- relation goes when its users are renamed.
mutual
  data RigidFree : Type → Set where
    rf-Unit   : RigidFree Unit
    rf-Void   : RigidFree Void
    rf-Int    : RigidFree Int
    rf-Float  : RigidFree Float
    rf-*      : ∀ {A B} → RigidFree A → RigidFree B → RigidFree (A * B)
    rf-+      : ∀ {A B} → RigidFree A → RigidFree B → RigidFree (A + B)
    rf-⇒      : ∀ {A B k} → RigidFree A → RigidFree B → RigidFree (A ⇒[ k ] B)
    rf-μ      : ∀ {F} → RigidFreeF F → RigidFree (μ-type F)
    rf-ν      : ∀ {F π} → RigidFreeF F → RigidFree (ν-type F π)

  data RigidFreeF : Functor → Set where
    rf-K  : ∀ {A} → RigidFree A → RigidFreeF (K A)
    rf-Id : RigidFreeF Id
    rf-⊕  : ∀ {F G} → RigidFreeF F → RigidFreeF G → RigidFreeF (F ⊕ G)
    rf-⊗  : ∀ {F G} → RigidFreeF F → RigidFreeF G → RigidFreeF (F ⊗ G)
