-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.CopyFree — plan 0.157 S2 step 3 (D6, D500): a core term that
-- names no copy of a value with cells.
--
-- A core term copies cells in three ways (`Measure.Copies` counts them):
--   * `dup` at a type that owns cells (a deep copy);
--   * `bcopy` at a type that owns cells (a lent value copied out);
--   * a closure that owns its environment (`llamωᶜ`) with cells, at a type the
--     program calls LENT (D498): its lent entry copies the environment.
-- `CF lc t`: none of them anywhere in `t` (a `llamω`'s lent body included;
-- its owned body is `Own.ownT`'s, which moves what the lent body reads).
-- `lc`: the program's lent-called closure types (`Keys.Univ.lct`).
------------------------------------------------------------------------

open import Once.Spec.Numerics using (TargetNum)

module Once.LinCore.CopyFree (fmt : TargetNum) where

open import Data.Bool using (Bool; true; false; _∨_; _∧_; not; T)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.LinCore.Core fmt

-- a type whose values own cells
cells : LTy → Bool
cells One        = false
cells Zero       = false
cells (Bt _)     = false
cells (A ⊗t B)   = cells A ∨ cells B
cells (A ⊕t B)   = cells A ∨ cells B
cells (Ct _ X)   = cells X
cells (Fn _ _ _ _) = true
cells (Nu _)     = true
cells (μt _)     = true

-- no cells: a copy of it is words
NC : LTy → Set
NC A = T (not (cells A))

module _ (lc : LTy → Bool) where

  -- ★ the term names no copy of cells
  CF : ∀ {Γ E A B} → Tm Γ E A B → Set
  CF (f ∘l g)          = CF f × CF g
  CF (f ⊗l g)          = CF f × CF g
  CF (lcase f g)       = CF f × CF g
  CF (lcata F f)       = CF f
  CF (lend f)          = CF f
  CF (blift f)         = CF f
  CF (bfst f)          = CF f
  CF (bsnd f)          = CF f
  CF (bcaseE f g)      = CF f × CF g
  CF (bout f)          = CF f
  CF (llam b _)        = CF b
  CF (llamω b _)       = CF b
  CF (llamωᶜ {g = g} {X = X} {A = A} {B = B} b _) = CF b × (T (not (lc (Fn many g A B))) ⊎ NC X)
  CF (liter f _)       = CF f
  CF (dup {A = A})     = NC A
  CF (bcopy {E = E})   = NC E
  {-# CATCHALL #-}
  CF _                 = ⊤

------------------------------------------------------------------------
-- The Booleans the conditions come in.
------------------------------------------------------------------------

nc-∨ : ∀ {a b : Bool} → T (not a) → T (not b) → T (not (a ∨ b))
nc-∨ {false} {false} _ _ = tt

T-∧ : ∀ {a b : Bool} → T (a ∧ b) → T a × T b
T-∧ {true} {true} _ = tt , tt

not-∨ʳ : ∀ {a b : Bool} → T (not (a ∨ b)) → T (not b)
not-∨ʳ {false} {false} _ = tt

not-∨ˡ : ∀ {a b : Bool} → T (not (a ∨ b)) → T (not a)
not-∨ˡ {false} {false} _ = tt

notnot : ∀ {a : Bool} → T (not (not a)) → T a
notnot {true} _ = tt
