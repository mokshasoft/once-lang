{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Internal.Type.Instance — a schema's parameters, their kinds, its rigid
-- instance, and the instances a use of it may be at.
--
--   * The parameters of `∀ā.T` are its free variables in order of first
--     occurrence (`params`).
--   * A parameter is `k-base` if it occurs inside a functor constant (`PK`),
--     where every instance must be a base type; otherwise it is `k-any`.
--     Kinds are read off the schema.
--   * The body of a polymorphic definition is typed once, at `rigidOf T`:
--     parameter `i` held abstract as `rigid kᵢ i`.
--   * A use is at a kinded instance: some `θ` with `substPoly θ T ≡ U` that
--     instantiates every base-kinded parameter at a base type.
------------------------------------------------------------------------

module Once.Internal.Type.Instance where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.String using (String; _≟_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (yes; no)
open import Once.Spec.Type using (Type)
open import Once.Internal.Type using (TKind; k-base; k-any)
open import Once.Internal.Type.Poly
  using (PolyType; PolyFunctor; PK; PId; _P⊕_; _P⊗_; PUnit; PVoid; _P*_; _P+_; _P⇒[_]_; PEff; PAct;
         Pμ-type; Pν-type; PInt; PFloat; PTVar; ftv; substPoly)
open import Once.Internal.Type.WellFormed using (IsBaseType)

------------------------------------------------------------------------
-- Parameters and kinds
------------------------------------------------------------------------

-- The variables occurring inside a functor constant: the base-kinded ones.
mutual
  ftvK : PolyType → List String
  ftvK (PTVar _)     = []
  ftvK PUnit         = []
  ftvK PVoid         = []
  ftvK PInt          = []
  ftvK PFloat        = []
  ftvK (A P* B)      = ftvK A ++ ftvK B
  ftvK (A P+ B)      = ftvK A ++ ftvK B
  ftvK (A P⇒[ _ ] B) = ftvK A ++ ftvK B
  ftvK (PEff A B)    = ftvK A ++ ftvK B
  ftvK (PAct A B)    = ftvK A ++ ftvK B
  ftvK (Pμ-type F)   = ftvKF F
  ftvK (Pν-type F _) = ftvKF F

  ftvKF : PolyFunctor → List String
  ftvKF (PK A)   = ftv A            -- everything under a constant is base
  ftvKF PId      = []
  ftvKF (F P⊕ G) = ftvKF F ++ ftvKF G
  ftvKF (F P⊗ G) = ftvKF F ++ ftvKF G

memberB : String → List String → Bool
memberB x []       = false
memberB x (y ∷ ys) with x ≟ y
... | yes _ = true
... | no  _ = memberB x ys

-- First occurrences, in order (`seen`: the variables already listed).
nubFrom : List String → List String → List String
nubFrom seen []       = []
nubFrom seen (x ∷ xs) = if memberB x seen then nubFrom seen xs else x ∷ nubFrom (x ∷ seen) xs

nub : List String → List String
nub = nubFrom []

params : PolyType → List String
params T = nub (ftv T)

arityOf : PolyType → ℕ
arityOf T = length (params T)

kindOf : PolyType → String → TKind
kindOf T x = if memberB x (ftvK T) then k-base else k-any

-- A parameter's position (its index in the definition's telescope).
indexOf : String → List String → ℕ
indexOf x []       = zero
indexOf x (y ∷ ys) with x ≟ y
... | yes _ = zero
... | no  _ = suc (indexOf x ys)

------------------------------------------------------------------------
-- The rigid instance: the type the body is checked at
------------------------------------------------------------------------

rigidSubst : PolyType → String → Type
rigidSubst T x = rigid (kindOf T x) (indexOf x (params T))

rigidOf : PolyType → Type
rigidOf T = substPoly (rigidSubst T) T

------------------------------------------------------------------------
-- Kinded instances: what a use may be at
------------------------------------------------------------------------

RespectsKinds : PolyType → (String → Type) → Set
RespectsKinds T θ = ∀ {x} → x ∈ ftvK T → IsBaseType (θ x)

KindedInstance : PolyType → Type → Set
KindedInstance T U = Σ[ θ ∈ (String → Type) ] (substPoly θ T ≡ U) × RespectsKinds T θ
