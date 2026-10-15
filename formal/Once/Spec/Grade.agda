{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Grade — the two grades an arrow carries.
--
--   * USAGE: how many times the argument is used, in the ordered semiring
--     `0 ≤ 1 ≤ ω` (quantitative type theory, affine: `1` is at most once).
--   * EFFECT: what running the arrow may do, in the chain
--       pure ≤ act ≤ eff
--     `pure`: nothing — a value. `act`: finitely many events, then it
--     returns. `eff`: each next event after finite work; it need not stop.
--     Sequencing two computations has the larger grade (the join).
--
-- One law couples them: an erased position (`0`) is never evaluated, so what
-- sits there must be pure.
------------------------------------------------------------------------

module Once.Spec.Grade where

------------------------------------------------------------------------
-- Usage
------------------------------------------------------------------------

data Quantity : Set where
  Zero One Many : Quantity

-- The usage of two uses together.
_+q_ : Quantity → Quantity → Quantity
Zero +q q    = q
One  +q Zero = One
One  +q One  = Many
One  +q Many = Many
Many +q _    = Many

-- A use of usage `q`, inside a context used `p` times.
_*q_ : Quantity → Quantity → Quantity
Zero *q _    = Zero
One  *q q    = q
Many *q Zero = Zero
Many *q One  = Many
Many *q Many = Many

infixl 60 _+q_
infixl 70 _*q_

-- The order `0 ≤ 1 ≤ ω`: a use may claim more than it makes (affine).
data _≤q_ : Quantity → Quantity → Set where
  0≤q : ∀ {q} → Zero ≤q q
  1≤1 : One ≤q One
  1≤ω : One ≤q Many
  ω≤ω : Many ≤q Many

infix 4 _≤q_

------------------------------------------------------------------------
-- Effect
------------------------------------------------------------------------

data Purity : Set where
  pure act eff : Purity

-- The chain, one derivation per pair.
data _⊑π_ : Purity → Purity → Set where
  ⊑-pure : pure ⊑π pure
  ⊑-pa   : pure ⊑π act
  ⊑-pe   : pure ⊑π eff
  ⊑-act  : act  ⊑π act
  ⊑-ae   : act  ⊑π eff
  ⊑-eff  : eff  ⊑π eff

infix 4 _⊑π_

-- The join: two arms of which exactly one runs, or two computations run one
-- after the other. (`pure ⊔p π = π` is one clause.)
_⊔p_ : Purity → Purity → Purity
pure ⊔p π    = π
act  ⊔p pure = act
act  ⊔p act  = act
act  ⊔p eff  = eff
eff  ⊔p _    = eff

infixr 5 _⊔p_

-- What a computation in a position used `q` times may be, in a term of grade
-- `π`: an erased position is never evaluated, so only a pure one.
positionGrade : Quantity → Purity → Purity
positionGrade Zero _ = pure
positionGrade One  π = π
positionGrade Many π = π

------------------------------------------------------------------------
-- An arrow's grade
------------------------------------------------------------------------

record ArrowKind : Set where
  constructor mk-kind
  field
    quantity : Quantity
    purity   : Purity
