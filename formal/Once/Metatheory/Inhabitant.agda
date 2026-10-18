{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Inhabitant — an inhabited base type has a value: the
-- witness the world and the model of `Once.Metatheory.Inhabited` answer with.
------------------------------------------------------------------------

module Once.Metatheory.Inhabitant where

open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Once.Spec.Signature using (BTy; unit; void; int; float; _*_; _+_; ⟦_⟧ᵇ; NotEmpty)

inhabitant : ∀ b → NotEmpty b → ⟦ b ⟧ᵇ
inhabitant unit    _       = _
inhabitant void    ()
inhabitant int     _       = 0
inhabitant float   _       = 0
inhabitant (a * b) (p , q) = inhabitant a p , inhabitant b q
inhabitant (a + b) (inj₁ p) = inj₁ (inhabitant a p)
inhabitant (a + b) (inj₂ q) = inj₂ (inhabitant b q)
