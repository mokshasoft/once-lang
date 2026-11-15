{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Float.Value — WHAT A `Float` IS: IEEE 754 LEVEL 2 (plan 0.150 N6).
--
-- IEEE 754 §3.2 separates four levels. Level 1 is the extended reals; level 2,
-- FLOATING-POINT DATA, is what a format can hold: the finite numbers it
-- represents, with SIGNED ZEROS, the two infinities, and ONE NaN; levels 3 and
-- 4 are representations and bit strings, where a NaN acquires a sign and a
-- payload. A `Float` is level 2. Its bit pattern is an ENCODING
-- (`Spec.Float.Encoding`), used where bits cross the boundary (`Spec.ABI`).
--
-- So there is one NaN, by the value set and not by a rule of arithmetic
-- (D113 restated): no operation has to canonicalise anything, because there is
-- nothing else for it to produce. Its encoding is the canonical quiet NaN.
--
-- THE VALUES ARE CANONICAL. A non-zero finite value is `±(2m+1)·2^e`, an ODD
-- significand, so each number has exactly one representation and `_≡_` on
-- `FloatVal` is identity of level-2 data: `==` at `Float` (`χ_Δ`) is this
-- equality. The type is format-free, as `ℤ`'s values are width-free; a format
-- enters through ROUNDING, which lands in the values the format represents.
--
-- THE ONE ROUNDING. Every result that rounds is an exact rational
-- `± n · 2^E / D` (a literal: `n / 10^k`; a sum or product: `D = 1`; a quotient
-- of two odd significands: `D` the divisor's), and `roundQ` rounds it to the
-- format by IEEE's roundTiesToEven, with GRADUAL UNDERFLOW (subnormals, a
-- quantum of `2^(emin−p+1)`), overflow to ±∞, and the sign of a zero result
-- kept. Nothing rounds twice, and no sticky bit is needed: the rounding
-- division sees the exact numerator and denominator. Subnormals are level-2
-- data of the format, and the hardware of every target produces them, so the
-- value set has them (D118's "no subnormals" restated by plan 0.150).
------------------------------------------------------------------------

module Once.Spec.Float.Value where

open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _*_; _∸_; _^_; NonZero)
open import Data.Nat.DivMod using (_/_; _%_)
open import Data.Nat.Properties using (m^n≢0; m*n≢0)
open import Data.Integer as ℤ using (ℤ; +_; -[1+_])
open import Data.Bool using (Bool; true; false; if_then_else_; not; _∧_; _∨_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Spec.Float.Dyadic using (FloatFormat; bias; bitLen)
open Once.Spec.Float.Dyadic.FloatFormat using (exp-bits; sig-bits)

------------------------------------------------------------------------
-- Signs
------------------------------------------------------------------------

data Sign : Set where
  pos neg : Sign

flip : Sign → Sign
flip pos = neg
flip neg = pos

-- | The sign of a product or quotient.
xorS : Sign → Sign → Sign
xorS pos t = t
xorS neg t = flip t

sameS : Sign → Sign → Bool
sameS pos pos = true
sameS neg neg = true
sameS pos neg = false
sameS neg pos = false

------------------------------------------------------------------------
-- The values
------------------------------------------------------------------------

data FloatVal : Set where
  fv-zero : Sign → FloatVal
  fv-num  : Sign → ℕ → ℤ → FloatVal      -- ± (2m+1) · 2^e
  fv-inf  : Sign → FloatVal
  fv-nan  : FloatVal

-- | The odd significand of `fv-num s m e`.
odd : ℕ → ℕ
odd m = suc (2 * m)

-- | NEGATION, one structural rule: flip the sign of whatever has one. NaN has
-- none, as `0` has none in `ℤ`.
negV : FloatVal → FloatVal
negV (fv-zero s)    = fv-zero (flip s)
negV (fv-num s m e) = fv-num (flip s) m e
negV (fv-inf s)     = fv-inf (flip s)
negV fv-nan         = fv-nan

------------------------------------------------------------------------
-- Round half to even, of an exact quotient
------------------------------------------------------------------------

-- | `q` and `r` are `num / den` and `num % den`: up if the remainder is over
-- half, down if under, to the even neighbour on an exact half.
roundHalfEven : ℕ → ℕ → ℕ → ℕ
roundHalfEven q r den =
  if      (2 * r) ℕ.<ᵇ den then q
  else if den ℕ.<ᵇ (2 * r) then suc q
  else if (_%_ q 2 {{_}}) ℕ.≡ᵇ 0 then q else suc q

divRHE : ℕ → (den : ℕ) → {{NonZero den}} → ℕ
divRHE num den = roundHalfEven (num / den) (num % den) den

------------------------------------------------------------------------
-- The format's constants
------------------------------------------------------------------------

-- | The quantum of the subnormals, `2^(emin − p + 1)`: `emin = 1 − bias`,
-- `p = sig-bits + 1`.
qmin : FloatFormat → ℤ
qmin F = (+ 1) ℤ.- (+ (bias F + sig-bits F))

-- | The quantum at which a value whose binade is `2^t` rounds: `p` significant
-- bits, but never finer than the subnormal quantum.
quantum : FloatFormat → ℤ → ℤ
quantum F t = (t ℤ.- (+ sig-bits F)) ℤ.⊔ qmin F

-- | `m · 2^q ≥ 2^(emax + 1)`, `emax = bias`: past the largest finite value.
overflows : FloatFormat → ℕ → ℤ → Bool
overflows F m q = (+ (bias F + 2)) ℤ.≤ᵇ ((+ bitLen m) ℤ.+ q)

------------------------------------------------------------------------
-- Canonical form: strip the factors of two into the exponent
--
-- `fuel` bounds the halvings; it is the significand itself, which is more
-- than enough. Each decision is an aux taking its scrutinee as an argument, so
-- a proof that cases on it reduces.
------------------------------------------------------------------------

canon  : ℕ → Sign → ℕ → ℤ → FloatVal
canonAt : ℕ → Sign → ℕ → ℤ → Bool → FloatVal

canon fuel    s zero    e = fv-zero s
canon zero    s (suc m) e = fv-num s (suc m / 2) e     -- unreachable: fuel ≥ m
canon (suc f) s (suc m) e = canonAt f s (suc m) e ((suc m % 2) ℕ.≡ᵇ 1)

canonAt f s m e true  = fv-num s (m / 2) e
canonAt f s m e false = canon f s (m / 2) (e ℤ.+ (+ 1))

-- | A rounded significand at its quantum: zero keeps its sign, too large is
-- ±∞, anything else is the canonical number.
finish : FloatFormat → Sign → ℕ → ℤ → FloatVal
finishAt : Sign → ℕ → ℤ → Bool → FloatVal

finish F s zero    q = fv-zero s
finish F s (suc m) q = finishAt s (suc m) q (overflows F (suc m) q)

finishAt s m q true  = fv-inf s
finishAt s m q false = canon m s m q

------------------------------------------------------------------------
-- THE ONE ROUNDING: `± n · 2^E / (suc d)` to the format
------------------------------------------------------------------------

-- | `2^k ≤ n / D`.
atLeast : ℕ → ℕ → ℤ → Bool
atLeast n D (+ j)    = (D * 2 ^ j) ℕ.≤ᵇ n
atLeast n D -[1+ j ] = D ℕ.≤ᵇ (n * 2 ^ suc j)

lgAt : ℤ → Bool → ℤ
lgAt k true  = k
lgAt k false = k ℤ.- (+ 1)

-- | `⌊log₂ (n / D)⌋` for `n, D > 0`. With `k = bitLen n − bitLen D`,
-- `log₂ n − log₂ D` lies strictly between `k − 1` and `k + 1`, so the floor is
-- `k` or `k − 1`, and one exact comparison decides.
lg : ℕ → ℕ → ℤ
lg n D = lgAt ((+ bitLen n) ℤ.- (+ bitLen D)) (atLeast n D ((+ bitLen n) ℤ.- (+ bitLen D)))

-- | `n · 2^k / (suc d)`, rounded half to even.
scaleRHE : ℕ → ℕ → ℤ → ℕ
scaleRHE n d (+ j)    = divRHE (n * 2 ^ j) (suc d)
scaleRHE n d -[1+ j ] =
  divRHE n (suc d * 2 ^ suc j) {{m*n≢0 (suc d) (2 ^ suc j) {{_}} {{m^n≢0 2 (suc j)}}}}

-- | At the quantum `2^q`: the significand is `n · 2^(E − q) / D`, rounded.
roundAt : FloatFormat → Sign → ℕ → ℤ → ℕ → ℤ → FloatVal
roundAt F s n E d q = finish F s (scaleRHE n d (E ℤ.- q)) q

roundQ : FloatFormat → Sign → ℕ → ℤ → ℕ → FloatVal
roundQ F s zero    E d = fv-zero s
roundQ F s (suc n) E d = roundAt F s (suc n) E d (quantum F (E ℤ.+ lg (suc n) (suc d)))

-- | A level-2 value of any format, read at `F`: the identity on the values `F`
-- represents (a value from the world, `Spec.Boundary`).
fitV : FloatFormat → FloatVal → FloatVal
fitV F (fv-zero s)    = fv-zero s
fitV F (fv-num s m e) = roundQ F s (odd m) e 0
fitV F (fv-inf s)     = fv-inf s
fitV F fv-nan         = fv-nan

-- | `v` is a value of the format `F`: reading it at `F` changes nothing.
Fits : FloatFormat → FloatVal → Set
Fits F v = fitV F v ≡ v
