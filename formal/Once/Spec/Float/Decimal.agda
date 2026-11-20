{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Float.Decimal — THE LITERAL'S PAYLOAD, AND ITS ROUNDING TO A VALUE
-- (plan 0.74 K0/K1, D116; plan 0.150: the result is a level-2 value).
--
-- `3.14` IS NOT A DYADIC. `3.14 = 157/50` and 50 is not a power of two, so no
-- `Dyadic` equals it — which is why `accept?` rejected it at the EXACTNESS
-- step, before representability was ever consulted. A float literal's payload
-- therefore cannot be a `Dyadic`; it must be the DECIMAL the programmer wrote.
--
-- This is the same principle that made `Int`'s payload a `ℤ` (D115): the
-- payload is SOURCE SYNTAX, and source syntax for a float literal is a
-- decimal. `Dyadic` was source syntax only for the subset that happened to be
-- exact, which is exactly the subset `accept?` was restricting us to.
--
-- WHY EXACTNESS OF THE PAYLOAD IS THE WHOLE POINT: with an exact payload there
-- is EXACTLY ONE rounding, at the target's format (`Value.roundQ`). Agda's
-- `Float` would round first and round again — harmless for binary32-via-
-- binary64 by Figueroa (53 ≥ 2·24+2) but it CAPS PRECISION at the payload's
-- format, so binary128 or x87-extended could never be served. It is also
-- D109/D112's mistake: a format baked where all targets must be served.
--
-- `(ℤ , ℕ)` as integer-part/fraction-part was rejected too, and the second
-- reason is silent: `3.14` and `3.014` both give `(3 , 14)` unless the DIGIT
-- COUNT rides along, and `-0.5` has integer part `-0 = 0`, so THE SIGN IS
-- LOST. The sign rides beside the digits (plan 0.150): a decimal is a sign, a
-- magnitude and an exponent, so `-0.0` keeps its sign, and its value is the
-- magnitude rounded with the sign (rounding is odd, `round (−r) = −round r`).
------------------------------------------------------------------------

module Once.Spec.Float.Decimal where

open import Data.Nat as ℕ using (ℕ; _∸_; _^_; _+_; _*_)
open import Data.Integer using (+_)

open import Once.Spec.Float.Dyadic using (FloatFormat)
open import Once.Spec.Float.Value using (FloatVal; Sign; pos; roundQ)

------------------------------------------------------------------------
-- The payload
--
-- `Dyadic` is `sig /2^ shift`; this is the SAME record in base ten. It holds
-- every decimal literal EXACTLY — `3.1` is `⟨ pos ⟩ 31 /10^ 1`, no rounding.
--
-- UNNORMALISED, exactly as `Dyadic` is: `0.5` and `0.50` are distinct records
-- (`⟨ pos ⟩ 5 /10^ 1` vs `⟨ pos ⟩ 50 /10^ 2`). They round to the same value
-- because `roundQ` rounds the exact quotient.
------------------------------------------------------------------------

record Decimal : Set where
  constructor ⟨_⟩_/10^_
  field
    sign  : Sign   -- beside the digits, so `-0.0` is `⟨ neg ⟩ 0 /10^ 1`
    sig   : ℕ      -- the magnitude
    exp10 : ℕ

open Decimal

-- | The whole number `n`.
fromℕ : ℕ → Decimal
fromℕ n = ⟨ pos ⟩ n /10^ 0

-- | A literal as written: its sign beside the integer digits `i` and the `l`
-- fraction digits `f` (`-0.0` is the negative zero).
signedDecimal : Sign → ℕ → ℕ → ℕ → Decimal
signedDecimal s i f l = ⟨ s ⟩ (i * 10 ^ l + f) /10^ l

------------------------------------------------------------------------
-- The literal's value at a format
------------------------------------------------------------------------

-- | `±sig / 10^k`, rounded once, with its sign: a zero (`-0.0`) and a literal
-- that rounds to zero (`-1e-400`) are the zero of their sign (`roundQ`).
roundDec : FloatFormat → Decimal → FloatVal
roundDec F (⟨ s ⟩ n /10^ k) = roundQ F s n (+ 0) (10 ^ k ∸ 1)
