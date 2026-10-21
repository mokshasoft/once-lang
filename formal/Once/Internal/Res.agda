-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Internal.Res
--
-- INTERNAL (D333).
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
-- `Once.Internal.Trace`'s `T` (a computation's observable is a
-- trace plus a result, and a stopped computation has none).
--
-- The gain is not tidiness: with a value that only exists when the
-- computation returns, "stopped ⇒ no result" is a TYPING fact rather than
-- a premise every obligation has to remember to carry.
------------------------------------------------------------------------

module Once.Internal.Res where

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

-- | Lift a relation on values to one on results. Two results are related
--   when they stop together, or both return related values. This is what a
--   bisimulation over possibly-finite codata compares layer by layer — the
--   `Res` analogue of the trace-carrying layer relation D201 gave `∼ᵈ`.
--
--   A DATA type, not a definition by cases on the two results. The relation is
--   the same one either way, and both presentations let a proof case-split and
--   refute a mixed pair. What only the data presentation gives is INJECTIVITY:
--   a defined function applied to an unknown result is BLOCKED — it might still
--   reduce — so the unifier refuses to look inside it, and every consumer that
--   relates two COMPUTATIONS through it (`RelT`, `_∼ᵈ_`, the coalgebra
--   relations) then has to have those computations written out by hand at each
--   use site, because they can no longer be read back out of the goal. A data
--   type is injective in its indices, so they stay inferred.
--
--   The relation is a PARAMETER, not an index, and it appears only to the left
--   of the constructor's result. That is what keeps the type legal at a
--   relation which is itself not strictly positive — `RelV` at an arrow eats a
--   relation on the domain — since a parameter is checked once, abstractly.
data Res-rel {X Y : Set} (R : X → Y → Set) : Res X → Res Y → Set where
  rel-stopped : Res-rel R stopped stopped
  rel-returns : ∀ {x y} → R x y → Res-rel R (returns x) (returns y)

