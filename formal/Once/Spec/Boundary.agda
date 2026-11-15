{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Boundary — A VALUE FROM OUTSIDE, READ AT THE TARGET (D397).
--
-- SPEC. `Int` and `Float` mean what the target provides (D054, D113): the
-- carrier is width-free and the target enters through the operations — `norm`
-- at the word's width, rounding to the format — so every value the language
-- computes is the target's. A value the WORLD gives (an interpretation's value
-- or a call's answer) is the one the language does not compute: the world is
-- width-free, so it is a bare carrier, and format-free, so a float is any
-- level-2 value. Where it crosses into the program it is read at the target,
-- as the CPU reads the register the answer arrives in: an `int` as the word at
-- the target's width, a `float` as a value of the target's format (`fitV`:
-- the identity on the values the format represents), a compound value leaf by
-- leaf. Going beyond the target's
-- word is another type's business (D054's `BigInt`), not a wider `Int`.
------------------------------------------------------------------------

module Once.Spec.Boundary where

open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
import Once.Spec.Word as SW
open import Once.Spec.Signature using (BTy; unit; void; int; float; ⟦_⟧ᵇ)
import Once.Spec.Signature as S
open import Once.Spec.Numerics using (TargetNum; module TargetNum)
open TargetNum
open import Once.Spec.Float.Value using (fitV)

-- the world's value, read at the target
readAt : TargetNum → ∀ b → ⟦ b ⟧ᵇ → ⟦ b ⟧ᵇ
readAt tn unit      x        = x
readAt tn void      x        = x
readAt tn int       v        = SW.Width.norm (int-bits tn) v
readAt tn float     v        = fitV (float-format tn) v
readAt tn (a S.* b) (x , y)  = readAt tn a x , readAt tn b y
readAt tn (a S.+ b) (inj₁ x) = inj₁ (readAt tn a x)
readAt tn (a S.+ b) (inj₂ y) = inj₂ (readAt tn b y)
