-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · LIB — `max` ON `Nat`, FROM MONUS.
--
--     max a b = a + (b ∸ a)
--
-- ★ TWO LINES, because both halves already exist.  ⚠ `Lib/Max` is NOT
--   this: that module is the MAXIMALITY predicate of a divisor (gcd's
--   spec), which shares only the word.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs; _<ˢ_; _<ˢ?_ )
open import Agda.Builtin.Nat using () renaming ( Nat to ℕ )
module DirectedHoTT.Lib.NatMax (𝒮 : Defs) (n : ℕ) where
open import DirectedHoTT.Spec.Syntax using ( Cx; RTm; Nat )
open import DirectedHoTT.Spec.Typing 𝒮 n using ( Ctx; ⌊_⌋; _⊢_∷_ )
open import DirectedHoTT.Lib.Nat 𝒮 n   using ( plusTm; ⊢plus )
open import DirectedHoTT.Lib.Monus 𝒮 n using ( monusTm; ⊢monus )

maxTm : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
maxTm a b = plusTm a (monusTm b a)

⊢max : {Γ : Ctx} {a b : RTm ⌊ Γ ⌋} →
       Γ ⊢ a ∷ Nat → Γ ⊢ b ∷ Nat → Γ ⊢ maxTm a b ∷ Nat
⊢max da db = ⊢plus da (⊢monus db da)
