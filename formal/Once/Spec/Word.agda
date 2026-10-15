{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Word — the machine integer that `Int` denotes.
--
-- SPEC. `Int` means what the target's CPU computes: arithmetic on a word of
-- the target's width, two's complement. The carrier is ℕ, a value in
-- `[0, 2^bits)` (the residue representation); the width is a parameter of
-- the operations, never of the carrier, so `⟦ Int ⟧ = Carrier` at every
-- target. `+`, `-`, `*` and negation WRAP — that is their meaning, not an
-- error. Comparisons read the word as SIGNED. Division and remainder are
-- TOTAL with RISC-V's results: `a / 0 = −1`, `a % 0 = a`,
-- `MIN / −1 = MIN`, `MIN % −1 = 0`, otherwise truncated toward zero.
-- A LITERAL must fit the signed range (`InRange`); arithmetic is not checked.
------------------------------------------------------------------------

module Once.Spec.Word where

import Data.Nat as ℕ
open ℕ using (ℕ; zero; suc; _∸_; _^_)
open import Data.Nat.DivMod using (_%_; _/_)
open import Data.Nat.Properties using (m^n≢0)
open import Data.Integer using (ℤ; +_; -[1+_]; ∣_∣; sign; _◃_; _-_)
import Data.Integer as ℤ
open import Data.Product using (_×_)
open import Relation.Nullary.Decidable using (Dec; _×-dec_)
open import Data.Integer.Properties using (_<?_)
import Data.Sign as Sign
open import Data.Bool using (Bool; if_then_else_; _∧_)
open import Relation.Nullary using (does)

-- The carrier, shared by all widths.
Carrier : Set
Carrier = ℕ

module Width (bits : ℕ) where

  modulus : ℕ
  modulus = 2 ^ bits

  instance
    modulus≢0 : ℕ.NonZero modulus
    modulus≢0 = m^n≢0 2 bits

  -- A word at this width; `bits` drives only the operations.
  Word : Set
  Word = Carrier

  -- Reduce a natural into `[0, modulus)`.
  norm : ℕ → Word
  norm n = n % modulus

  -- A ℤ literal as a word: a negative one by two's complement.
  fromℤ : ℤ → Word
  fromℤ (+ n)      = norm n
  fromℤ (-[1+ n ]) = norm (modulus ∸ norm (suc n))

  infixl 6 _⊕_ _⊖_
  infixl 7 _⊗_

  _⊕_ : Word → Word → Word
  x ⊕ y = norm (x ℕ.+ y)

  _⊖_ : Word → Word → Word
  x ⊖ y = norm (x ℕ.+ (modulus ∸ y))

  _⊗_ : Word → Word → Word
  x ⊗ y = norm (x ℕ.* y)

  ⊝_ : Word → Word
  ⊝ x = norm (modulus ∸ x)

  -- The signed view: `[0, half)` non-negative, `[half, modulus)` negative.
  half : ℕ
  half = 2 ^ (bits ∸ 1)

  toℤ : Word → ℤ
  toℤ w = if w ℕ.<ᵇ half then + w else (+ w) - (+ modulus)

  intMin : Word           -- −2^(bits−1)
  intMin = half

  negOne : Word           -- all ones; −1
  negOne = modulus ∸ 1

  -- A literal is admissible when it fits the signed range; its word is then
  -- `fromℤ` (whose wrap an admissible literal never exercises).
  InRange : ℤ → Set
  InRange z = (ℤ.- (+ half) ℤ.≤ z) × (z ℤ.≤ + (half ℕ.∸ 1))

  inRange? : ∀ z → Dec (InRange z)
  inRange? z = (ℤ.- (+ half) ℤ.≤? z) ×-dec (z ℤ.≤? + (half ℕ.∸ 1))

  toWord : ∀ z → InRange z → Word
  toWord z _ = fromℤ z

  infix 4 _<ˢ_ _≡ʷ_

  _<ˢ_ : Word → Word → Bool          -- signed less-than
  x <ˢ y = does (toℤ x <? toℤ y)

  _≡ʷ_ : Word → Word → Bool          -- bit equality
  x ≡ʷ y = x ℕ.≡ᵇ y

  -- Division on naturals and truncated signed division on ℤ (the divisor is
  -- non-zero wherever `_/ˢ_`/`_%ˢ_` use them).
  _divℕ_ _modℕ_ : ℕ → ℕ → ℕ
  n divℕ zero    = zero
  n divℕ (suc d) = n / suc d
  n modℕ zero    = n
  n modℕ (suc d) = n % suc d

  tdivℤ tmodℤ : ℤ → ℤ → ℤ
  tdivℤ a b = (sign a Sign.* sign b) ◃ (∣ a ∣ divℕ ∣ b ∣)
  tmodℤ a b = sign a ◃ (∣ a ∣ modℕ ∣ b ∣)

  infixl 7 _/ˢ_ _%ˢ_

  _/ˢ_ : Word → Word → Word
  a /ˢ b = if b ℕ.≡ᵇ 0 then negOne
           else if (a ℕ.≡ᵇ intMin) ∧ (b ℕ.≡ᵇ negOne) then intMin
           else fromℤ (tdivℤ (toℤ a) (toℤ b))

  _%ˢ_ : Word → Word → Word
  a %ˢ b = if b ℕ.≡ᵇ 0 then a
           else if (a ℕ.≡ᵇ intMin) ∧ (b ℕ.≡ᵇ negOne) then 0
           else fromℤ (tmodℤ (toℤ a) (toℤ b))

module Word64 = Width 64
