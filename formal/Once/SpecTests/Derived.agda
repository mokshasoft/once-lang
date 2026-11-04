{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.SpecTests.Derived — witnesses that the derived terms of
-- `Once.Spec.Core.Derived` and the substitutions of `Once.Spec.Type` mean
-- what their names say (plan 0.141 step 4b).
--
-- The laws cannot pin these: a `map` that ignored its function, or mapped at
-- the wrong variable, would satisfy both functor laws (`map id = id`,
-- `map (g ∘ f) = map g ∘ map f` both become `id = id`). Each witness here is
-- one small instance, checked by computation. Positive sameness witnesses are
-- left out: the laws and the fundamental theorem claim them.
------------------------------------------------------------------------

module Once.SpecTests.Derived where

open import Data.Fin using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Spec.Type
  using (Ty; var; Fun; K; Id; _⊕_; _⊗_; Unit; Int; _*_; _+_; _⟨_⟩; at₀; shiftᵗ)
open import Once.Spec.Core.Syntax using (Defs; Tm; app; pair; fst; snd)
open import Once.Spec.Core.Derived using (mapAtᶜ; mapᶜ; layerᶜ)

------------------------------------------------------------------------
-- Substitutions single out variable 0
------------------------------------------------------------------------

-- `at₀ A` puts `A` for variable 0 and renames the rest down by one.
at₀-pair : (var zero * var (suc zero)) ⟨ at₀ {1} Int ⟩ ≡ Int * var zero
at₀-pair = refl

-- `shiftᵗ` renames every variable up by one: variable 0 becomes free for a new one.
shiftᵗ-var : var {2} zero ⟨ shiftᵗ ⟩ ≡ var (suc zero)
shiftᵗ-var = refl

------------------------------------------------------------------------
-- `map` acts at variable 0, and only there
------------------------------------------------------------------------

module _ {s} {S : Defs s} (A B : Ty 1) {n} (h x : Tm S 1 n) where

  -- at variable 0, the function is applied
  map-at-var₀ : mapAtᶜ A B (var zero) h x ≡ app h x
  map-at-var₀ = refl

  -- another variable is left alone
  map-at-var₁ : mapAtᶜ A B (var (suc zero)) h x ≡ x
  map-at-var₁ = refl

  -- a base type is left alone
  map-at-Int : mapAtᶜ A B Int h x ≡ x
  map-at-Int = refl

  -- a product goes by its parts: the function on the variable-0 part only
  map-at-pair : mapAtᶜ A B (var zero * var (suc zero)) h x ≡ pair (app h (fst x)) (snd x)
  map-at-pair = refl

------------------------------------------------------------------------
-- `layer` is `map` at one layer of the functor, the recursive position as variable 0
------------------------------------------------------------------------

-- the layer of lists of `Int`: `Unit + Int * R`
ListF : Fun 0
ListF = K Unit ⊕ (K Int ⊗ Id)

module _ {s} {S : Defs s} (A B : Ty 0) {n} (f : Tm S 0 n) where

  layer-list : layerᶜ ListF A B f ≡ mapᶜ (Unit + (Int * var zero)) A B f
  layer-list = refl
