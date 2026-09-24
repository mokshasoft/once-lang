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

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; Σ-syntax)

data Res (X : Set) : Set where
  stopped : Res X            -- the program ended; there is NO result
  returns : X → Res X

-- | The flag, for the consumers that only need to know WHETHER it stopped.
--   Written as a top-level dispatch (not a `with`) so it reduces on a
--   constructor and stays stuck — rather than wrong — on a variable.
is-stopped : ∀ {X} → Res X → Bool
is-stopped stopped     = true
is-stopped (returns _) = false

-- | INVERTING THE FLAG (plan 0.98).
--
--   A lemma whose subject is the TRACE does not care what the value was, only
--   whether there was one — so the boolean premise is the right statement for
--   it, and over-specifying it with a value parameter would say less about
--   more. But its PROOF has to reduce `bindRes`, and that needs the
--   constructor. These two are the bridge, and they are proofs: the flag and
--   the result carry exactly the same information about stopping.
res-returns : ∀ {X} {r : Res X} → is-stopped r ≡ false → Σ[ v ∈ X ] r ≡ returns v
res-returns {r = returns v} _ = v , refl

res-stopped : ∀ {X} {r : Res X} → is-stopped r ≡ true → r ≡ stopped
res-stopped {r = stopped} _ = refl

-- | `returns` is injective — it is a constructor. Needed wherever an
--   obligation BINDS the returned value and a proof knows what it was.
returns-inj : ∀ {X} {x y : X} → returns x ≡ returns y → x ≡ y
returns-inj refl = refl

-- | Map over the result of a computation that returns.
mapRes : ∀ {X Y} → (X → Y) → Res X → Res Y
mapRes f stopped     = stopped
mapRes f (returns x) = returns (f x)

-- | The functor laws for `mapRes`, and congruence. Every one is a two-case
--   split, and the `stopped` case is `refl` in each — a computation with no
--   result has nothing to map.
mapRes-id : ∀ {X} (r : Res X) → mapRes (λ x → x) r ≡ r
mapRes-id stopped     = refl
mapRes-id (returns _) = refl

mapRes-∘ : ∀ {X Y Z} (g : Y → Z) (f : X → Y) (r : Res X)
         → mapRes g (mapRes f r) ≡ mapRes (λ x → g (f x)) r
mapRes-∘ g f stopped     = refl
mapRes-∘ g f (returns _) = refl

mapRes-cong : ∀ {X Y} {f g : X → Y} → (∀ x → f x ≡ g x)
            → (r : Res X) → mapRes f r ≡ mapRes g r
mapRes-cong h stopped     = refl
mapRes-cong h (returns x) = cong returns (h x)

-- | Mapping does not change WHETHER it stopped.
is-stopped-mapRes : ∀ {X Y} (f : X → Y) (r : Res X)
                  → is-stopped (mapRes f r) ≡ is-stopped r
is-stopped-mapRes f stopped     = refl
is-stopped-mapRes f (returns _) = refl

-- | Lift a relation on values to one on results. Two results are related
--   when they stop together, or both return related values. This is what a
--   bisimulation over possibly-finite codata compares layer by layer — the
--   `Res` analogue of the trace-carrying layer relation D201 gave `∼ᵈ`.
--
--   Enumerated rather than defined by a `with`: a proof that has only an
--   abstract `Res` must be able to case-split, and a mixed pair must be
--   REFUTABLE rather than merely unprovable.
Res-rel : ∀ {X Y} → (X → Y → Set) → Res X → Res Y → Set
Res-rel R stopped     stopped     = ⊤
Res-rel R stopped     (returns _) = ⊥
Res-rel R (returns _) stopped     = ⊥
Res-rel R (returns x) (returns y) = R x y

-- | `stopped` and `returns` are distinct — the discrimination every
--   "a stopped run has no result" argument spends.
returns≢stopped : ∀ {X} {x : X} → returns x ≡ stopped → ∀ {W : Set} → W
returns≢stopped ()
