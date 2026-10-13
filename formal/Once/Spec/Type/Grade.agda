{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Type.Grade — the grades an arrow carries.
--
-- An arrow `A ⇒[ k ] B` is graded twice, independently:
--   * by a usage `Quantity` (quantitative type theory): how many times the
--     argument is consumed — `Zero` (erased), `One` (linear), `Many`;
--   * by a `Purity`: whether running it has observable effects —
--     `pure ≤ act ≤ eff`, `eff⁺ ≤ eff` (D311–D313); sequencing multiplies
--     grades (`_·p_`).
-- All four combinations are arrows. One law couples the two where a
-- computation sits in a position (plan 0.116): an ERASED position is never run
-- — it has no resources at run time — so what sits there must be pure
-- (`positionGrade`). Usage counts copies of values; it never decides whether
-- an effect happens.
------------------------------------------------------------------------

module Once.Spec.Type.Grade where

open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

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

-- ω is the top of the order: every usage may stand where ω is expected.
≤q-Many : ∀ q → (q ≤q Many) ≡ true
≤q-Many Zero = refl
≤q-Many One  = refl
≤q-Many Many = refl

------------------------------------------------------------------------
-- Effect: the order pure ≤ act ≤ eff, with eff⁺ ≤ eff
--
-- `pure`: a value (TOTAL). `act`: a computation of the free monad `T` — it
-- performs finitely many events and RETURNS (D313). `eff`: a computation of
-- the free completely iterative monad `T∞` — it reaches each next event, or
-- its end, after finite work, and need not stop (PRODUCTIVE, D312). Below
-- `eff` sits the GUARD `eff⁺`: a computation whose first node is an event; it
-- is not above `pure` (a value performs no event), and not comparable with
-- `act` (a guarded computation may run forever).
------------------------------------------------------------------------

data Purity : Set where
  pure : Purity   -- no observable effects
  act  : Purity   -- observable effects, and returns (D313)
  eff⁺ : Purity   -- an event FIRST: the guard of iteration (D311)
  eff  : Purity   -- observable effects, and may run forever: each next event
                  -- after finite work (D312)

-- Join: the least grade above both — the grade at which two arms meet, of
-- which exactly one runs. `pure`/`act` and `eff⁺` meet at `eff` (one arm may
-- perform no event, the other may not return).
_⊔p_ : Purity → Purity → Purity
pure ⊔p pure = pure
pure ⊔p act  = act
pure ⊔p eff⁺ = eff
pure ⊔p eff  = eff
act  ⊔p pure = act
act  ⊔p act  = act
act  ⊔p eff⁺ = eff
act  ⊔p eff  = eff
eff⁺ ⊔p pure = eff
eff⁺ ⊔p act  = eff
eff⁺ ⊔p eff⁺ = eff⁺
eff⁺ ⊔p eff  = eff
eff  ⊔p _    = eff

infixr 5 _⊔p_

-- SEQUENCING (D311): running one computation and then another has the
-- PRODUCT of their grades. Grades are an ordered monoid with unit `pure`;
-- `eff⁺` absorbs — an event in either part is an event first of the whole,
-- since the part before it either begins with one or returns at once (a tree
-- has no silent node, D312) — and `eff` absorbs `act`. So the product is not
-- the join: `pure ·p eff⁺` is `eff⁺`, which is not above `pure`. A rule that
-- runs premises in order concludes at the product of their grades, left to
-- right.
_·p_ : Purity → Purity → Purity
pure ·p p    = p
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

-- The grades at which applying an arrow at the SURFACE builds a suspension
-- (`Unit ⇒[ π ] B`, D232): the effectful grades a program writes, `act` and
-- `eff` (D313). The guard `eff⁺` is never written.
data EffGrade : Purity → Set where
  eg-act : EffGrade act
  eg-eff : EffGrade eff

-- The grade a computation may have in a position used `q` times, inside a
-- term of grade `π`: an erased position (`Zero`) is never evaluated, so only a
-- pure computation may sit there (dropping an effectful one would lose its
-- effect — plan 0.116 §0); any other position is evaluated, once, at `π`.
positionGrade : Quantity → Purity → Purity
positionGrade Zero _ = pure
positionGrade One  π = π
positionGrade Many π = π

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
