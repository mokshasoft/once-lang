-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Res
--
-- THE RESULT OF A COMPUTATION: a value, or the program ended.
--
-- Plan 0.98. A SigOp declared `halts` ends the program, so it has no
-- result. Before this, its codomain was `Unit` and a boolean flag beside
-- it said "do not look at the value" — a patch over a type that lied, and
-- the reason `EffectShape`'s `Emits`/`Halts` carried the SAME index and
-- could therefore be confused on the surface path.
--
-- `Res` is the honest shape, and it is a LEAF module (no dependencies) so
-- that both ends of the correspondence can name it: `Once.SigOp.Info`'s
-- `semM` (a SigOp's semantics either returns or ends the program) and
-- `Once.Denotation.TraceMonad`'s `T` (a computation's observable is a
-- trace plus a result, and a stopped computation has none).
--
-- The gain is not tidiness: with a value that only exists when the
-- computation returns, "stopped ⇒ no result" is a TYPING fact rather than
-- a premise every obligation has to remember to carry.
------------------------------------------------------------------------

module Once.Res where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Bool using (Bool; true; false)

data Res (X : Set) : Set where
  stopped : Res X            -- the program ended; there is NO result
  returns : X → Res X

-- | The flag, for the consumers that only need to know WHETHER it stopped.
--   Written as a top-level dispatch (not a `with`) so it reduces on a
--   constructor and stays stuck — rather than wrong — on a variable.
is-stopped : ∀ {X} → Res X → Bool
is-stopped stopped     = true
is-stopped (returns _) = false

-- | Map over the result of a computation that returns.
mapRes : ∀ {X Y} → (X → Y) → Res X → Res Y
mapRes f stopped     = stopped
mapRes f (returns x) = returns (f x)

-- | `stopped` and `returns` are distinct — the discrimination every
--   "a stopped run has no result" argument spends.
returns≢stopped : ∀ {X} {x : X} → returns x ≡ stopped → ∀ {W : Set} → W
returns≢stopped ()
