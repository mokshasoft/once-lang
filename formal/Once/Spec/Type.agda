{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Type — the types: the objects of the category.
--
--   Unit, Void      the terminal and the initial object;
--   A * B, A + B    product and coproduct;
--   A ⇒[ k ] B      the exponential, graded by `k` (`Spec.Type.Grade`);
--   μ-type F        the initial algebra of the functor `F` (inductive data);
--   ν-type F π      the final coalgebra of `F` (codata), whose layers are
--                   produced with effect `π`: `ν-type F eff` is ν(T ∘ F);
--   Int, Float      the target's integers and floating-point numbers;
--   rigid k i       the `i`-th type parameter of a polymorphic definition,
--                   of kind `k`, held abstract while its body is typed.
--
-- The functors are the polynomial ones, built from constants, the recursive
-- position, sums and products; `⟦ F ⟧T X` is `F` applied to `X`.
------------------------------------------------------------------------

module Once.Spec.Type where

open import Data.Nat using (ℕ)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Spec.Type.Grade using (ArrowKind; mk-kind; Zero; One; Many; Purity; pure)

mutual
  -- Polynomial (strictly positive) functors.
  data Functor : Set where
    K    : Type → Functor               -- constant
    Id   : Functor                      -- the recursive position
    _⊕_  : Functor → Functor → Functor  -- sum
    _⊗_  : Functor → Functor → Functor  -- product

  data Type : Set where
    Unit   : Type
    Void   : Type
    _*_    : Type → Type → Type
    _+_    : Type → Type → Type
    _⇒[_]_ : Type → ArrowKind → Type → Type
    μ-type : Functor → Type
    ν-type : Functor → Purity → Type
    Int    : Type
    Float  : Type
    rigid  : TKind → ℕ → Type

  -- What a type parameter may be instantiated at: `k-base`, a base type (it
  -- occurs under a functor constant); `k-any`, any type.
  data TKind : Set where
    k-base k-any : TKind

infixr 40 _⊕_
infixr 50 _⊗_

infixr 30 _⇒[_]_
infixr 40 _+_
infixr 50 _*_

-- The pure arrows at each usage: linear, unrestricted, erased.
_⊸_ : Type → Type → Type
A ⊸ B = A ⇒[ mk-kind One pure ] B

_⇒_ : Type → Type → Type
A ⇒ B = A ⇒[ mk-kind Many pure ] B

_⇒₀_ : Type → Type → Type
A ⇒₀ B = A ⇒[ mk-kind Zero pure ] B

infixr 30 _⊸_
infixr 30 _⇒_
infixr 30 _⇒₀_

-- A functor applied to a type.
⟦_⟧T : Functor → Type → Type
⟦ K A ⟧T X = A
⟦ Id ⟧T X = X
⟦ F ⊕ G ⟧T X = ⟦ F ⟧T X + ⟦ G ⟧T X
⟦ F ⊗ G ⟧T X = ⟦ F ⟧T X * ⟦ G ⟧T X

-- Is a type `Void`, or `Unit`? The contract of an external operation
-- (`Spec.Contract`) is defined by cases on its codomain: one into `Void` never
-- returns, one into `Unit` returns nothing.
isVoid? : (T : Type) → Dec (T ≡ Void)
isVoid? Void          = yes refl
isVoid? Unit          = no (λ ())
isVoid? (_ * _)       = no (λ ())
isVoid? (_ + _)       = no (λ ())
isVoid? (_ ⇒[ _ ] _)  = no (λ ())
isVoid? (μ-type _)    = no (λ ())
isVoid? (ν-type _ _)  = no (λ ())
isVoid? Int           = no (λ ())
isVoid? Float         = no (λ ())
isVoid? (rigid _ _)   = no (λ ())

isUnit? : (T : Type) → Dec (T ≡ Unit)
isUnit? Unit          = yes refl
isUnit? Void          = no (λ ())
isUnit? (_ * _)       = no (λ ())
isUnit? (_ + _)       = no (λ ())
isUnit? (_ ⇒[ _ ] _)  = no (λ ())
isUnit? (μ-type _)    = no (λ ())
isUnit? (ν-type _ _)  = no (λ ())
isUnit? Int           = no (λ ())
isUnit? Float         = no (λ ())
isUnit? (rigid _ _)   = no (λ ())
