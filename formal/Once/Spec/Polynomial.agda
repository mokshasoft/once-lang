{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Polynomial — polynomial functors on sets and their initial
-- algebras.
--
-- A code is a constant set, the identity, a sum or a product; `⟦ F ⟧SF` is
-- the functor it denotes and `sfmap` its action. `μS F` is its initial
-- algebra (`inS`); its fold, at every effect grade, is `Spec.Domain.foldM`.
-- (Final coalgebras, whose layers carry an effect, are `Spec.Effect.νM`.)
------------------------------------------------------------------------

module Once.Spec.Polynomial where

open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

data SFunctor : Set₁ where
  SK   : Set → SFunctor
  SId  : SFunctor
  _S⊕_ : SFunctor → SFunctor → SFunctor
  _S⊗_ : SFunctor → SFunctor → SFunctor

infixr 30 _S⊕_
infixr 40 _S⊗_

⟦_⟧SF : SFunctor → Set → Set
⟦ SK A ⟧SF   X = A
⟦ SId ⟧SF    X = X
⟦ F S⊕ G ⟧SF X = ⟦ F ⟧SF X ⊎ ⟦ G ⟧SF X
⟦ F S⊗ G ⟧SF X = ⟦ F ⟧SF X × ⟦ G ⟧SF X

sfmap : ∀ F {X Y : Set} → (X → Y) → ⟦ F ⟧SF X → ⟦ F ⟧SF Y
sfmap (SK A)   f x        = x
sfmap SId      f x        = f x
sfmap (F S⊕ G) f (inj₁ x) = inj₁ (sfmap F f x)
sfmap (F S⊕ G) f (inj₂ y) = inj₂ (sfmap G f y)
sfmap (F S⊗ G) f (x , y)  = sfmap F f x , sfmap G f y

data μS (F : SFunctor) : Set where
  inS : ⟦ F ⟧SF (μS F) → μS F
