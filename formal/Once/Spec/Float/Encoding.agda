{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Float.Encoding — A `Float`'S BITS: IEEE 754 levels 3 and 4.
--
-- A `Float` is a level-2 value (`Spec.Float.Value`); its bit pattern is only
-- its encoding in the target's interchange format, and it is seen only where a
-- value crosses the boundary as a word (`Spec.ABI`). `encode` is defined on
-- the values the format represents (what rounding to the format produces).
--
-- THE CANONICAL NaN (D055, D113 restated by plan 0.150 N6): there is one NaN,
-- so it has one encoding: exponent all ones, quiet bit set, sign clear,
-- payload zero, on every target. RISC-V produces exactly this pattern; x86
-- sets the sign on an invalid operation and propagates payloads, so an x86
-- backend canonicalises wherever bits are observed.
--
-- `decode` reads any pattern, including the ones `encode` never writes: a NaN
-- of any sign and payload is the one NaN, and a subnormal is read as the
-- number it is.
------------------------------------------------------------------------

module Once.Spec.Float.Encoding where

open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)
open import Data.Nat.DivMod using (_/_)
open import Data.Nat.Properties using (m^n≢0)
open import Data.Integer as ℤ using (ℤ; +_; -[1+_])
open import Data.Bool using (Bool; true; false; if_then_else_)

open import Once.Spec.Float.Dyadic using (FloatFormat; bias; bitLen; modPow)
open Once.Spec.Float.Dyadic.FloatFormat using (exp-bits; sig-bits)
open import Once.Spec.Float.Value
  using (Sign; pos; neg; FloatVal; fv-zero; fv-num; fv-inf; fv-nan; odd; canon; qmin)

------------------------------------------------------------------------
-- The fields
------------------------------------------------------------------------

signBitOf : Sign → ℕ
signBitOf pos = 0
signBitOf neg = 1

-- | The weight of the sign bit, `2^(exp-bits + sig-bits)`.
signWeight : FloatFormat → ℕ
signWeight F = 2 ^ (exp-bits F + sig-bits F)

-- | The all-ones exponent field, in place.
maxExpField : FloatFormat → ℕ
maxExpField F = ((2 ^ exp-bits F) ∸ 1) * 2 ^ sig-bits F

zeroW : FloatFormat → Sign → ℕ
zeroW F s = signBitOf s * signWeight F

infW : FloatFormat → Sign → ℕ
infW F s = signBitOf s * signWeight F + maxExpField F

-- | THE canonical quiet NaN.
nanW : FloatFormat → ℕ
nanW F = maxExpField F + 2 ^ (sig-bits F ∸ 1)

------------------------------------------------------------------------
-- encode
------------------------------------------------------------------------

-- | A normal number: the odd significand `M` shifted up to `p` bits, its
-- leading bit implicit; the stored exponent `se ≥ 1`.
normalW : FloatFormat → Sign → ℕ → ℕ → ℕ
normalW F s M se =
  signBitOf s * signWeight F + se * 2 ^ sig-bits F
    + (M * 2 ^ (suc (sig-bits F) ∸ bitLen M) ∸ 2 ^ sig-bits F)

-- | A subnormal: the significand at the subnormal quantum, stored exponent 0.
subnormalW : FloatFormat → Sign → ℕ → ℤ → ℕ
subnormalW F s M (+ j)    = signBitOf s * signWeight F + M * 2 ^ j
subnormalW F s M -[1+ _ ] = signBitOf s * signWeight F    -- not representable

-- | `±M · 2^e` by its stored exponent `e + (bitLen M − 1) + bias`.
numAt : FloatFormat → Sign → ℕ → ℤ → ℤ → ℕ
numAt F s M e (+ suc k) = normalW F s M (suc k)
numAt F s M e (+ zero)  = subnormalW F s M (e ℤ.- qmin F)
numAt F s M e -[1+ _ ]  = subnormalW F s M (e ℤ.- qmin F)

encode : FloatFormat → FloatVal → ℕ
encode F (fv-zero s)    = zeroW F s
encode F (fv-num s m e) = numAt F s (odd m) e (e ℤ.+ (+ (bitLen (odd m) ∸ 1 + bias F)))
encode F (fv-inf s)     = infW F s
encode F fv-nan         = nanW F

------------------------------------------------------------------------
-- decode
------------------------------------------------------------------------

signOf : ℕ → Sign
signOf zero    = pos
signOf (suc _) = neg

-- | The all-ones exponent: an infinity if the fraction is zero, else the NaN.
decodeMax : Sign → ℕ → FloatVal
decodeMax s zero    = fv-inf s
decodeMax s (suc _) = fv-nan

-- | By the stored exponent `se`: zero or subnormal (`se ≡ 0`), the maximum,
-- or normal.
decodeAt : FloatFormat → Sign → ℕ → ℕ → Bool → Bool → FloatVal
decodeAt F s se frac true  _     = canon frac s frac (qmin F)
decodeAt F s se frac false true  = decodeMax s frac
decodeAt F s se frac false false =
  canon (2 ^ sig-bits F + frac) s (2 ^ sig-bits F + frac) ((+ se) ℤ.- (+ (bias F + sig-bits F)))

decode : FloatFormat → ℕ → FloatVal
decode F w =
  decodeAt F
    (signOf (_/_ (modPow w (suc (exp-bits F + sig-bits F))) (signWeight F) {{m^n≢0 2 (exp-bits F + sig-bits F)}}))
    (_/_ (modPow w (exp-bits F + sig-bits F)) (2 ^ sig-bits F) {{m^n≢0 2 (sig-bits F)}})
    (modPow w (sig-bits F))
    (_/_ (modPow w (exp-bits F + sig-bits F)) (2 ^ sig-bits F) {{m^n≢0 2 (sig-bits F)}} ℕ.≡ᵇ 0)
    (_/_ (modPow w (exp-bits F + sig-bits F)) (2 ^ sig-bits F) {{m^n≢0 2 (sig-bits F)}}
       ℕ.≡ᵇ ((2 ^ exp-bits F) ∸ 1))
