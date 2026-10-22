{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Internal.Type — the compiler's names over the Spec's types.
--
-- The types are the Spec's (`Once.Spec.Type`): `Ty m` over `m` type
-- variables, ground types `Type = Ty 0`. This module keeps the compiler's own
-- helpers over them: a ground type read over `m` type variables (`wk₀`), the
-- pure arrows at each usage and the deciders `isVoid?`, `isUnit?`.
------------------------------------------------------------------------

module Once.Internal.Type where

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Spec.Grade using (mk-kind; Zero; One; Many; pure)
open import Once.Spec.Type
  using (Ty; Type; Fun; var; Unit; Void; _*_; _+_; _⇒[_]_; μ; ν; Int; Float; _⟨_⟩; _⟨_⟩F)
open import Data.Fin using (Fin)

-- A ground type, as a type over `m` type variables (it mentions none).
-- The substitution out of no type variables (named once: two absurd lambdas
-- are not equal).
none : ∀ {m} → Fin 0 → Ty m
none ()

wk₀ : ∀ {m} → Type → Ty m
wk₀ A = A ⟨ none ⟩

wk₀F : ∀ {m} → Fun 0 → Fun m
wk₀F F = F ⟨ none ⟩F

-- The pure arrows at each usage: linear, unrestricted, erased.
_⊸_ : ∀ {m} → Ty m → Ty m → Ty m
A ⊸ B = A ⇒[ mk-kind One pure ] B

_⇒_ : ∀ {m} → Ty m → Ty m → Ty m
A ⇒ B = A ⇒[ mk-kind Many pure ] B

_⇒₀_ : ∀ {m} → Ty m → Ty m → Ty m
A ⇒₀ B = A ⇒[ mk-kind Zero pure ] B

infixr 30 _⊸_
infixr 30 _⇒_
infixr 30 _⇒₀_

-- Is a type `Void`, or `Unit`? The contract of an external operation
-- (`Spec.Contract`) is defined by cases on its codomain: one into `Void` never
-- returns, one into `Unit` returns nothing.
isVoid? : ∀ {m} (T : Ty m) → Dec (T ≡ Void)
isVoid? Void          = yes refl
isVoid? (var _)       = no (λ ())
isVoid? Unit          = no (λ ())
isVoid? (_ * _)       = no (λ ())
isVoid? (_ + _)       = no (λ ())
isVoid? (_ ⇒[ _ ] _)  = no (λ ())
isVoid? (μ _)         = no (λ ())
isVoid? (ν _ _)       = no (λ ())
isVoid? Int           = no (λ ())
isVoid? Float         = no (λ ())

isUnit? : ∀ {m} (T : Ty m) → Dec (T ≡ Unit)
isUnit? Unit          = yes refl
isUnit? (var _)       = no (λ ())
isUnit? Void          = no (λ ())
isUnit? (_ * _)       = no (λ ())
isUnit? (_ + _)       = no (λ ())
isUnit? (_ ⇒[ _ ] _)  = no (λ ())
isUnit? (μ _)         = no (λ ())
isUnit? (ν _ _)       = no (λ ())
isUnit? Int           = no (λ ())
isUnit? Float         = no (λ ())
