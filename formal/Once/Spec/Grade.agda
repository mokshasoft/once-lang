{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Grade — the two grades an arrow carries.
--
--   * USAGE: how many times the argument is used, in the ordered semiring
--     `0 ≤ 1 ≤ ω` (quantitative type theory, affine: `1` is at most once).
--   * EFFECT: what running the arrow may do, ordered by
--       pure ≤ act ≤ eff   and   eff⁺ ≤ eff
--     `pure`: nothing — a value. `act`: finitely many events, then it
--     returns. `eff`: each next event after finite work; it need not stop.
--     `eff⁺`: an event FIRST, then anything — the guard of iteration (D311).
--     Sequencing two computations has the grade `·p` of the two.
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
  pure act eff⁺ eff : Purity

-- The order, one derivation per pair. `eff⁺` is incomparable with `pure` and
-- `act`: a guarded computation performs an event, and need not return.
data _⊑π_ : Purity → Purity → Set where
  ⊑-pure : pure ⊑π pure
  ⊑-pa   : pure ⊑π act
  ⊑-pe   : pure ⊑π eff
  ⊑-act  : act  ⊑π act
  ⊑-ae   : act  ⊑π eff
  ⊑-g    : eff⁺ ⊑π eff⁺
  ⊑-ge   : eff⁺ ⊑π eff
  ⊑-eff  : eff  ⊑π eff

infix 4 _⊑π_

-- Sequencing: one computation, then another. Pure adds nothing; a guarded
-- one first keeps the guard; a guarded one after an `act` keeps it too (the
-- `act` part may perform no event, the guard still comes before any return).
_·p_ : Purity → Purity → Purity
pure ·p π    = π
act  ·p pure = act
act  ·p act  = act
act  ·p eff⁺ = eff⁺
act  ·p eff  = eff
eff⁺ ·p _    = eff⁺
eff  ·p pure = eff
eff  ·p act  = eff
eff  ·p eff⁺ = eff⁺
eff  ·p eff  = eff

infixr 6 _·p_

-- The grades an operation is declared at that are not the guard.
data EffGrade : Purity → Set where
  eg-act : EffGrade act
  eg-eff : EffGrade eff

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
