-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Float.Word — THE FLOAT OPERATIONS ON WORDS, for the machine side
-- (plan 0.150 step 3).
--
-- The Spec's `Float` is a level-2 value (`Spec.Float.Value`); a word is its
-- encoding (`Spec.Float.Encoding`). The machine keeps words in its registers,
-- so each operation here reads its operands, applies the Spec's operation on
-- values, and writes the result: `encode ∘ op ∘ decode`. A word operation is
-- then the Spec's by definition, and the machine side's correspondence proofs
-- stay `refl`-shaped.
--
-- Negation is the exception: it is the sign-bit flip the hardware performs
-- (`btcq`, `fsgnjn`), defined on every pattern. It reads as `negV` on values
-- (a NaN of either sign is the one NaN), which is what a bridge proves.
------------------------------------------------------------------------

module Once.Float.Word where

open import Data.Nat as ℕ using (ℕ; _+_; _∸_; _^_)
open import Data.Integer using (ℤ)
open import Data.Bool using (Bool; true; false)

open import Once.Spec.Float.Dyadic using (FloatFormat)
open Once.Spec.Float.Dyadic.FloatFormat using (exp-bits; sig-bits)
open import Once.Spec.Float.Value using (FloatVal; negV; fitV)
open import Once.Spec.Float.Decimal using (Decimal; roundDec)
open import Once.Spec.Float.Encoding using (encode; decode; nanW)
import Once.Spec.Float.Arith as FA

-- | Two operands read, one result written.
onWords : FloatFormat → (FloatVal → FloatVal → FloatVal) → ℕ → ℕ → ℕ
onWords F op a b = encode F (op (decode F a) (decode F b))

fadd fsub fmul fdiv : FloatFormat → ℕ → ℕ → ℕ
fadd F = onWords F (FA.addV F)
fsub F = onWords F (λ x y → FA.addV F x (negV y))
fmul F = onWords F (FA.mulV F)
fdiv F = onWords F (FA.divV F)

-- | The sign-bit flip.
fnegAt : FloatFormat → ℕ → Bool → ℕ
fnegAt F w true  = w ∸ 2 ^ (exp-bits F + sig-bits F)
fnegAt F w false = w + 2 ^ (exp-bits F + sig-bits F)

fneg : FloatFormat → ℕ → ℕ
fneg F w = fnegAt F w (2 ^ (exp-bits F + sig-bits F) ℕ.≤ᵇ w)

-- | `Int` → `Float` (D125).
i2f : FloatFormat → ℤ → ℕ
i2f F z = encode F (FA.i2fV F z)

-- | A literal's word.
round : FloatFormat → Decimal → ℕ
round F d = encode F (roundDec F d)

-- | THE canonical NaN.
nan : FloatFormat → ℕ
nan = nanW

-- | A word from the world, read at the format (`Spec.Boundary.readAt`'s
-- `fitV`, on the encoding).
fit : FloatFormat → ℕ → ℕ
fit F w = encode F (fitV F (decode F w))
