{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Type.WellFormed — base types, concrete types, well-formed functors,
-- and types without parameters.
------------------------------------------------------------------------

module Once.Spec.Type.WellFormed where

open import Once.Spec.Type
  using (Type; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ-type; ν-type; rigid; k-base; Functor; K; Id; _⊕_; _⊗_)

data IsBaseType : Type → Set where
  base-Unit   : IsBaseType Unit
  base-Void   : IsBaseType Void
  base-Int    : IsBaseType Int
  base-Float  : IsBaseType Float
  base-Prod   : ∀ {A B} → IsBaseType A → IsBaseType B → IsBaseType (A * B)
  base-Sum    : ∀ {A B} → IsBaseType A → IsBaseType B → IsBaseType (A + B)
  -- a base-kinded type parameter is a base type; nothing else is known of it
  base-rigid  : ∀ {i} → IsBaseType (rigid k-base i)

-- | The types an external operation may have: a base type, or a first-order
-- arrow between base types. An external operation takes and returns base
-- values; it never receives or returns a Once function, `μ` or `ν` value.
data IsConcrete : Type → Set where
  con-base : ∀ {A} → IsBaseType A → IsConcrete A
  con-fun  : ∀ {A B k} → IsBaseType A → IsBaseType B → IsConcrete (A ⇒[ k ] B)

-- | A functor is well formed when every constant in it is a base type.
data WellFormedF : Functor → Set where
  wf-K   : ∀ {A} → IsBaseType A → WellFormedF (K A)
  wf-Id  : WellFormedF Id
  wf-Sum : ∀ {F G} → WellFormedF F → WellFormedF G → WellFormedF (F ⊕ G)
  wf-Prod : ∀ {F G} → WellFormedF F → WellFormedF G → WellFormedF (F ⊗ G)

-- | A type with no type parameter in it. The signature's operations and the
-- monomorphic definitions have such types; parameters exist only while a
-- polymorphic definition's body is typed.
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
