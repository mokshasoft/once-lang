{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Type.Grade — the grades an arrow carries.
--
-- An arrow `A ⇒[ k ] B` is graded twice, independently:
--   * by a usage `Quantity` (quantitative type theory): how many times the
--     argument is consumed — `Zero` (erased), `One` (linear), `Many`;
--   * by a `Purity`: whether running it has observable effects — `pure`, or
--     `eff`, ordered `pure ≤ eff`.
-- No law couples the two, so all four combinations are arrows.
------------------------------------------------------------------------

module Once.Spec.Type.Grade where

open import Data.Bool using (Bool; true; false)

------------------------------------------------------------------------
-- Usage: the semiring {0, 1, ω}
------------------------------------------------------------------------

data Quantity : Set where
  Zero  : Quantity  -- 0: erased
  One   : Quantity  -- 1: linear
  Many  : Quantity  -- ω: unrestricted

-- Addition: the usage of two uses together.
-- (`Zero +q q = q` is one clause, so it holds for a variable `q`.)
_+q_ : Quantity → Quantity → Quantity
Zero  +q q     = q
One   +q Zero  = One
One   +q One   = Many
One   +q Many  = Many
Many  +q _     = Many

infixl 60 _+q_

-- Multiplication: a use of usage `q` inside a context used `p` times.
-- (`Zero *q q = Zero` is one clause; `q *q Zero = Zero` holds by cases.)
_*q_ : Quantity → Quantity → Quantity
Zero  *q _     = Zero
One   *q Zero  = Zero
One   *q One   = One
One   *q Many  = Many
Many  *q Zero  = Zero
Many  *q One   = Many
Many  *q Many  = Many

infixl 70 _*q_

-- Join in the order `Zero ≤ One ≤ Many`: the usage of a case, where exactly
-- one branch runs.
_⊔q_ : Quantity → Quantity → Quantity
Zero ⊔q q    = q
One  ⊔q Zero = One
One  ⊔q One  = One
One  ⊔q Many = Many
Many ⊔q _    = Many

infixl 55 _⊔q_

-- The sub-usage order: `q₁ ≤q q₂` when a `q₁` use may stand where `q₂` is
-- expected. (`Zero ≤q q = true` is one clause.)
_≤q_ : Quantity → Quantity → Bool
Zero  ≤q _     = true
One   ≤q Zero  = false
One   ≤q One   = true
One   ≤q Many  = true
Many  ≤q Zero  = false
Many  ≤q One   = false
Many  ≤q Many  = true

------------------------------------------------------------------------
-- Effect: the order pure ≤ eff
------------------------------------------------------------------------

data Purity : Set where
  pure : Purity   -- no observable effects
  eff  : Purity   -- may have observable effects

-- Join: composing two arrows takes the join of their grades; `pure` is the
-- unit and `eff` absorbs.
_⊔p_ : Purity → Purity → Purity
pure ⊔p p = p
eff  ⊔p _ = eff

infixr 5 _⊔p_

------------------------------------------------------------------------
-- The grade of an arrow
------------------------------------------------------------------------

record ArrowKind : Set where
  constructor mk-kind
  field
    quantity : Quantity
    purity   : Purity

pureK : Quantity → ArrowKind
pureK q = mk-kind q pure

effK : ArrowKind
effK = mk-kind Many eff
