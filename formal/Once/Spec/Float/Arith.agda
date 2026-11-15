{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Float.Arith — WHAT THE OPERATIONS ON `Float` MEAN (plan 0.75 F4,
-- restated on values by plan 0.150).
--
-- IEEE 754 §4.3: every operation is performed "as if it first produced an
-- intermediate result correct to infinite precision and with unbounded range,
-- and then rounded that result". So each operation here is two steps: the
-- EXACT result (`Exact`: invalid, a signed infinity, or a signed exact ratio),
-- then the one rounding (`round`). The special cases of IEEE's tables are the
-- few places the exact step answers `invalid` or `∞`; signed zeros (§6.3) fall
-- out of the exact step, except that an exact zero sum of opposite signs is
-- `+0`.
--
-- There is one NaN, so no rule chooses a NaN: `invalid` rounds to `fv-nan`,
-- the same on every target BY DECISION (D055).
------------------------------------------------------------------------

module Once.Spec.Float.Arith where

open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)
open import Data.Integer as ℤ using (ℤ; +_; -[1+_])
open import Data.Bool using (Bool; true; false; not; _∧_; _∨_)
open import Data.Maybe using (Maybe; just; nothing)

open import Once.Spec.Float.Dyadic using (FloatFormat)
open import Once.Spec.Float.Value

------------------------------------------------------------------------
-- An operand, exactly: a signed infinity or `±n · 2^e`; NaN is no number
------------------------------------------------------------------------

data Operand : Set where
  inf : Sign → Operand
  fin : Sign → ℕ → ℤ → Operand

exact : FloatVal → Maybe Operand
exact (fv-zero s)    = just (fin s 0 (+ 0))
exact (fv-num s m e) = just (fin s (odd m) e)
exact (fv-inf s)     = just (inf s)
exact fv-nan         = nothing

-- | An operation on two numbers, with `r` when either operand is NaN.
both : {R : Set} → R → (Operand → Operand → R) → Maybe Operand → Maybe Operand → R
both r f (just a) (just b) = f a b
both r f (just _) nothing  = r
both r f nothing  _        = r

onNumbers : {R : Set} → R → (Operand → Operand → R) → FloatVal → FloatVal → R
onNumbers r f x y = both r f (exact x) (exact y)

------------------------------------------------------------------------
-- A result, exactly, and its rounding
------------------------------------------------------------------------

data Exact : Set where
  invalid : Exact
  ∞       : Sign → Exact
  ratio   : Sign → ℕ → ℤ → ℕ → Exact      -- ± n · 2^e / (suc d)

round : FloatFormat → Exact → FloatVal
round F invalid         = fv-nan
round F (∞ s)           = fv-inf s
round F (ratio s n e d) = roundQ F s n e d

-- | An operand as an exact result: `round ∘ exactOf ∘ exact` is the identity on
-- the format's values (a NaN, no number, is `invalid`).
exactOf : Maybe Operand → Exact
exactOf nothing            = invalid
exactOf (just (inf s))     = ∞ s
exactOf (just (fin s n e)) = ratio s n e 0

-- | Negation, exactly.
negO : Operand → Operand
negO (inf s)     = inf (flip s)
negO (fin s n e) = fin (flip s) n e

negE : Exact → Exact
negE invalid         = invalid
negE (∞ s)           = ∞ (flip s)
negE (ratio s n e d) = ratio (flip s) n e d

------------------------------------------------------------------------
-- The exact operations
------------------------------------------------------------------------

-- | `n · 2^(e − m)`, for `m ≤ e`.
alignTo : ℕ → ℤ → ℤ → ℕ
alignTo n e m = n * 2 ^ ℤ.∣ e ℤ.- m ∣

-- | Opposite signs: the larger magnitude's sign; equal magnitudes cancel
-- exactly, to `+0` (§6.3, roundTiesToEven).
cancel : Sign → ℕ → Sign → ℕ → ℤ → Bool → Bool → Exact
cancel s a t b m true  _     = ratio t (b ∸ a) m 0     -- a < b
cancel s a t b m false true  = ratio s (a ∸ b) m 0     -- b < a
cancel s a t b m false false = ratio pos 0 m 0         -- a ≡ b

-- | Two finite values, aligned at the smaller exponent `m`.
addAt : Sign → ℕ → Sign → ℕ → ℤ → Bool → Exact
addAt s a t b m true  = ratio s (a + b) m 0
addAt s a t b m false = cancel s a t b m (a ℕ.<ᵇ b) (b ℕ.<ᵇ a)

-- | `∞ + (−∞)` is invalid.
infAdd : Sign → Sign → Bool → Exact
infAdd s t true  = ∞ s
infAdd s t false = invalid

addE : Operand → Operand → Exact
addE (inf s)     (inf t)     = infAdd s t (sameS s t)
addE (inf s)     (fin _ _ _) = ∞ s
addE (fin _ _ _) (inf t)     = ∞ t
addE (fin s a e) (fin t b f) =
  addAt s (alignTo a e (e ℤ.⊓ f)) t (alignTo b f (e ℤ.⊓ f)) (e ℤ.⊓ f) (sameS s t)

-- | `∞ × 0` is invalid.
infMul : Sign → ℕ → Exact
infMul s zero    = invalid
infMul s (suc _) = ∞ s

mulE : Operand → Operand → Exact
mulE (inf s)     (inf t)     = ∞ (xorS s t)
mulE (inf s)     (fin t b _) = infMul (xorS s t) b
mulE (fin s a _) (inf t)     = infMul (xorS s t) a
mulE (fin s a e) (fin t b f) = ratio (xorS s t) (a * b) (e ℤ.+ f) 0

-- | A finite value over a finite divisor: `0/0` is invalid, `x/0` a signed
-- infinity (divideByZero, not invalid), otherwise the exact ratio.
finDiv : Sign → ℕ → ℕ → ℤ → ℤ → Exact      -- the divisor's magnitude first
finDiv s (suc b) a       e f = ratio s a (e ℤ.- f) b
finDiv s zero    zero    e f = invalid
finDiv s zero    (suc a) e f = ∞ s

divE : Operand → Operand → Exact
divE (inf _)     (inf _)     = invalid
divE (inf s)     (fin t _ _) = ∞ (xorS s t)
divE (fin s _ _) (inf t)     = ratio (xorS s t) 0 (+ 0) 0
divE (fin s a e) (fin t b f) = finDiv (xorS s t) b a e f

------------------------------------------------------------------------
-- The operations: exact, then rounded
------------------------------------------------------------------------

-- | A NaN operand makes the result invalid (§6.2).
addV mulV divV : FloatFormat → FloatVal → FloatVal → FloatVal
addV F x y = round F (onNumbers invalid addE x y)
mulV F x y = round F (onNumbers invalid mulE x y)
divV F x y = round F (onNumbers invalid divE x y)

-- | `Int` → `Float` (`toFloat`, D408): an integer is the exact value `z · 2^0`.
fromℤ : ℤ → Exact
fromℤ (+ n)    = ratio pos n (+ 0) 0
fromℤ -[1+ n ] = ratio neg (suc n) (+ 0) 0

i2fV : FloatFormat → ℤ → FloatVal
i2fV F z = round F (fromℤ z)

------------------------------------------------------------------------
-- Comparison
--
-- One numeric order of the extended reals, and from it:
--   * IEEE's quiet comparisons, `==.` and `<.`: numeric, false with a NaN;
--   * IEEE's totalOrder, `<`: numeric, then `−0 < +0`, then the one NaN (the
--     canonical, positive one) above everything;
--   * identity, `==` (`χ_Δ`): neither below the other in totalOrder, which
--     separates any two distinct values (`NaN == NaN`, `-0.0 != 0.0`).
------------------------------------------------------------------------

-- | `±n · 2^e` as a signed integer at the exponent `m ≤ e`.
signedAt : Sign → ℕ → ℤ → ℤ → ℤ
signedAt pos n e m = + alignTo n e m
signedAt neg n e m = ℤ.- (+ alignTo n e m)

-- | `x < y` numerically.
ltR : Operand → Operand → Bool
ltR (inf s)     (inf t)     = sameS s neg ∧ sameS t pos
ltR (inf s)     (fin _ _ _) = sameS s neg
ltR (fin _ _ _) (inf t)     = sameS t pos
ltR (fin s a e) (fin t b f) = not (signedAt t b f (e ℤ.⊓ f) ℤ.≤ᵇ signedAt s a e (e ℤ.⊓ f))

isNaN : FloatVal → Bool
isNaN (fv-zero _)    = false
isNaN (fv-num _ _ _) = false
isNaN (fv-inf _)     = false
isNaN fv-nan         = true

-- | `−0`, and `+0`.
isZeroOf : Sign → FloatVal → Bool
isZeroOf s (fv-zero t)    = sameS s t
isZeroOf s (fv-num _ _ _) = false
isZeroOf s (fv-inf _)     = false
isZeroOf s fv-nan         = false

-- | `x = y` numerically: neither below the other.
eqR : Operand → Operand → Bool
eqR a b = not (ltR a b) ∧ not (ltR b a)

-- | IEEE's quiet comparisons: false when either operand is NaN.
eqQ ltQ : FloatVal → FloatVal → Bool
ltQ = onNumbers false ltR
eqQ = onNumbers false eqR

-- | IEEE's totalOrder.
ltT : FloatVal → FloatVal → Bool
ltT x y = ltQ x y ∨ (isZeroOf neg x ∧ isZeroOf pos y) ∨ (not (isNaN x) ∧ isNaN y)

-- | Identity.
eqV : FloatVal → FloatVal → Bool
eqV x y = not (ltT x y) ∧ not (ltT y x)
