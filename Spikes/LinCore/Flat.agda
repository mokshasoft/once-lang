-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- LinCore.Flat — plan 0.146 A12: the FLAT types a SigOp takes and answers.
--
-- The Spec's `Spec.Signature.BTy` (`unit void int float * +`), over a set of
-- base words: what crosses the boundary to an Interpretation is a flat value,
-- with the layout `Spec.ABI` gives it. A SigOp answering `void` halts.
--
-- It has no parameters, so the core's modules can take a signature over it.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module LinCore.Flat where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)

infixr 40 _f+_
infixr 50 _f*_

data FTy (B : Set) : Set where
  funit fvoid : FTy B
  fw          : B → FTy B          -- a base word (`int`, `float`)
  _f*_ _f+_   : FTy B → FTy B → FTy B

-- its values, given what a base word is
⟦_⟧F : ∀ {B} → (B → Set) → FTy B → Set
⟦ m ⟧F funit    = ⊤
⟦ m ⟧F fvoid    = ⊥
⟦ m ⟧F (fw b)   = m b
⟦ m ⟧F (a f* b) = ⟦ m ⟧F a × ⟦ m ⟧F b
⟦ m ⟧F (a f+ b) = ⟦ m ⟧F a ⊎ ⟦ m ⟧F b
