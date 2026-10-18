{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Lang.Type.Grade — the grades an arrow carries.
--
-- An arrow `A ⇒[ k ] B` is graded twice, independently:
--   * by a usage `Quantity` (quantitative type theory): how many times the
--     argument is consumed — `Zero` (erased), `One` (linear), `Many`;
--   * by a `Purity`: whether running it has observable effects —
--     the chain `pure ≤ act ≤ eff` (D314); sequencing multiplies
--     grades (`_·p_`).
-- All four combinations are arrows. One law couples the two where a
-- computation sits in a position (plan 0.116): an ERASED position is never run
-- — it has no resources at run time — so what sits there must be pure
-- (`positionGrade`). Usage counts copies of values; it never decides whether
-- an effect happens.
------------------------------------------------------------------------

module Once.Lang.Type.Grade where

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
-- Effect: the chain pure ≤ act ≤ eff (D314)
--
-- `pure`: a value (TOTAL). `act`: a computation of the free monad `T` — it
-- performs finitely many events and RETURNS (D313). `eff`: a computation of
-- the resumption monad `T∞` — blocks of `T`, possibly forever (D317).
------------------------------------------------------------------------

data Purity : Set where
  pure : Purity   -- no observable effects
  act  : Purity   -- observable effects, and returns (D313)
  eff  : Purity   -- observable effects, and may run forever (D317)

-- D318 (item 13): a STREAM's layers are at most `act` — `ν F eff` has no
-- introduction (a layer of a stream is a finite block of calls). The finite
-- grades, named as the grades they are (`fin`).
data Finite : Set where
  pure : Finite
  act  : Finite

fin : Finite → Purity
fin pure = pure
fin act  = act

-- Join: the least grade above both — the grade at which two arms meet, of
-- which exactly one runs.
_⊔p_ : Purity → Purity → Purity
pure ⊔p p    = p
act  ⊔p pure = act
act  ⊔p act  = act
act  ⊔p eff  = eff
eff  ⊔p _    = eff

infixr 5 _⊔p_

-- SEQUENCING: running one computation and then another has the product of
-- their grades; on the chain it is the join (D314, `Spec.Grade._·p_`). A rule
-- that runs premises in order concludes at the product of their grades.
_·p_ : Purity → Purity → Purity
pure ·p p    = p
act  ·p pure = act
act  ·p act  = act
act  ·p eff  = eff
eff  ·p _    = eff

infixr 6 _·p_

-- The grades at which applying an arrow at the SURFACE builds a suspension
-- (`Unit ⇒[ π ] B`, D232): the effectful grades a program writes, `act` and
-- `eff` (D313).
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
