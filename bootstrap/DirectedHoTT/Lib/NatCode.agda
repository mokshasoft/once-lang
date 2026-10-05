-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · Lib — `Nat` at its CODE: `El ⌜Nat⌝` decodes to `Nat`.
-- The depth index of every scoped syntax (`Lib/Syn`, the Knot) is a
-- term of `El ⌜Nat⌝`; these cross between the two forms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.NatCode where

open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )

------------------------------------------------------------------------
-- Crossing between `Nat` and `El ⌜Nat⌝`; an index successor and equation.
------------------------------------------------------------------------

INat : {Γ : Cx} → RTy Γ
INat = El ⌜Nat⌝

toI : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ Nat → Γ ⊢ t ∷ El ⌜Nat⌝
toI d = ⊢conv d (csymᵀ (credᵀ El-⌜Nat⌝))

fromI : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ El ⌜Nat⌝ → Γ ⊢ t ∷ Nat
fromI d = ⊢conv d (credᵀ El-⌜Nat⌝)

-- `suc` of an index, as an index
⊢isuc : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ El ⌜Nat⌝ → Γ ⊢ nsuc t ∷ El ⌜Nat⌝
⊢isuc d = toI (⊢nsuc (fromI d))

-- an index equation, as a code, and its canonical proof
⊢Eq : {Γ : Ctx} {a b : RTm ⌊ Γ ⌋} → Γ ⊢ a ∷ El ⌜Nat⌝ → Γ ⊢ b ∷ El ⌜Nat⌝ → Γ ⊢ ⌜Id⌝ ⌜Nat⌝ a b ∷ U
⊢Eq = ⊢⌜Id⌝ ⊢⌜Nat⌝

⊢eqrefl : {Γ : Ctx} {a : RTm ⌊ Γ ⌋} → Γ ⊢ a ∷ El ⌜Nat⌝ → Γ ⊢ idrefl ⌜Nat⌝ a ∷ El (⌜Id⌝ ⌜Nat⌝ a a)
⊢eqrefl {a = a} da = ⊢conv (⊢idrefl ⊢⌜Nat⌝ da) (csymᵀ (credᵀ (El-⌜Id⌝ ⌜Nat⌝ a a)))
