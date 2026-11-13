-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Float.DecimalLaws — a literal's rounding, pinned by `refl`.
--
-- A literal means `roundDec F d`, a level-2 value (plan 0.150 N6 (a)); the
-- machine loads its encoding, `Once.Float.Word.round F d`. That the encoding
-- fits the register is `Once.Float.EncodingLaws.round-fits`.
------------------------------------------------------------------------

module Once.Float.DecimalLaws where

open import Data.Nat using (ℕ)
open import Data.Integer using (+_; -[1+_])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Spec.Float.Dyadic using (binary32; binary64)
open import Once.Spec.Float.Value using (negV)
open import Once.Spec.Float.Decimal using (decimalOf; negate; _/10^_; roundDec)
open import Once.Spec.Float.Encoding using (encode)
open import Once.Float.Word using (round)

------------------------------------------------------------------------
-- PINNED PATTERNS
--
-- D109's lesson, and this module is where it applies hardest. A rounding
-- routine that both sides of the correspondence call is UNFALSIFIABLE from
-- inside the development: the compiler and the meaning agree by construction
-- whatever it computes. `Once.Spec.Float.Dyadic` learned this when an encoder that
-- wrote the pair straight into the two fields typechecked and satisfied
-- `encode-fits`, because nothing could refute it.
--
-- So these are checked against patterns produced ELSEWHERE (glibc/IEEE),
-- transcribed as hex. `refl` here is the whole point: it is decided by
-- evaluation, so a rounding that drifts stops the build.
------------------------------------------------------------------------

-- 3.1 — the motivating literal. Not a dyadic at any width, so this is the case
-- `accept?` used to reject outright, and the digits below are the reason the
-- payload had to change.
_ : round binary64 ((+ 31) /10^ 1) ≡ 0x4008cccccccccccd
_ = refl

_ : round binary32 ((+ 31) /10^ 1) ≡ 0x40466666
_ = refl

-- 0.1 — the canonical "decimal that is not binary".
_ : round binary64 ((+ 1) /10^ 1) ≡ 0x3fb999999999999a
_ = refl

_ : round binary32 ((+ 1) /10^ 1) ≡ 0x3dcccccd
_ = refl

-- Exact dyadics: `round` must AGREE WITH `encode` where `encode` was already
-- right, or it has subsumed it wrongly.
_ : round binary64 ((+ 5) /10^ 1) ≡ 0x3fe0000000000000
_ = refl

_ : round binary32 ((+ 275) /10^ 2) ≡ 0x40300000
_ = refl

-- UNNORMALISED PAYLOADS MUST AGREE. `0.5` and `0.50` are distinct records, and
-- the module's own caveat says so; this is the lemma discharged by evaluation
-- rather than assumed.
_ : round binary64 ((+ 5) /10^ 1) ≡ round binary64 ((+ 50) /10^ 2)
_ = refl

-- 16777217 — the first integer binary32 cannot hold. Exact at binary64,
-- ROUNDED at binary32, and under D116 both compile. This is the literal K3
-- deletes `accept?` for.
_ : round binary64 ((+ 16777217) /10^ 0) ≡ 0x4170000010000000
_ = refl

_ : round binary32 ((+ 16777217) /10^ 0) ≡ 0x4b800000
_ = refl

-- The sign rides beside the magnitude, never through the rounding.
_ : round binary64 ((-[1+ 4 ]) /10^ 1) ≡ 0xbfe0000000000000
_ = refl

-- Zero.
_ : round binary64 ((+ 0) /10^ 0) ≡ 0
_ = refl

-- The lexer's triple, end to end: `3.14` is `RFloat 3 14 2`.
_ : round binary64 (decimalOf 3 14 2) ≡ 0x40091eb851eb851f
_ = refl

-- `16777217.0` — `RFloat 16777217 0 1`. Compiles at BOTH formats now (D116);
-- exactly at binary64, rounded at binary32. Before K3 it was rejected on every
-- target, which is the interim D116 was written to end.
_ : round binary32 (decimalOf 16777217 0 1) ≡ 0x4b800000
_ = refl

------------------------------------------------------------------------
-- K2: THE EXPONENT RANGE, pinned
------------------------------------------------------------------------

-- OVERFLOW → ±∞. Before this, `expFieldN`'s `modPow` wrapped and `1e41` at
-- binary32 encoded as `0x03800000` — a small FINITE number. Silent, unbounded,
-- and nothing in the tree could see it: both the meaning and the machine call
-- this same function, so they agreed on the wrong answer.
_ : round binary32 (decimalOf 100000000000000000000000000000000000000000 0 1)
      ≡ 0x7f800000
_ = refl

_ : round binary64 (decimalOf 100000000000000000000000000000000000000000 0 1)
      ≡ 0x48725dfa371a19e7     -- still FINITE at binary64: the range is a
_ = refl                       -- TARGET fact, and this is the point of D113

-- …and it keeps the sign.
_ : round binary32 (negate (decimalOf 100000000000000000000000000000000000000000 0 1))
      ≡ 0xff800000
_ = refl

-- UNDERFLOW → a SUBNORMAL, as glibc stores `1e-40` at binary32 (plan 0.150
-- R1, superseding D118's flush to zero, which this pin used to record).
_ : round binary32 ((+ 1) /10^ 40) ≡ 0x000116c2
_ = refl

-- The same literal is NORMAL at binary64, so it is exact there.
_ : round binary64 ((+ 1) /10^ 40) ≡ 0x37a16c262777579c
_ = refl

------------------------------------------------------------------------
-- F3: THE NEGATED LITERAL, pinned (plan 0.73 F3)
--
-- `-3.14` is ONE literal whose payload is `negate (decimalOf 3 14 2)` — the
-- elaborator folds the minus (`Once.TypeCheck.Elaborate`'s
-- `inferElabV-neg-aux … (nov-float …)`) and the core meaning of the
-- elaborated literal reads the same payload. THAT IS EXACTLY WHY THESE PINS
-- EXIST: the two sides name the same `negate` and the same `round`, so the
-- correspondence between them is `refl`-shaped and cannot falsify either
-- (D117). The patterns below were computed by glibc/GHC, not by this file.
--
-- The MAGNITUDE path is shared with the positive literal — `round` splits into
-- `signBit (sig d)` and `∣ sig d ∣` — so what is really being checked is that
-- the sign is the ONLY difference, including where rounding is not exact.
------------------------------------------------------------------------

-- `-0.5` and `-2.75`: exact at both formats, so only the sign bit moves.
_ : round binary64 (negate (decimalOf 0 5 1)) ≡ 0xbfe0000000000000
_ = refl

_ : round binary32 (negate (decimalOf 0 5 1)) ≡ 0xbf000000
_ = refl

_ : round binary64 (negate (decimalOf 2 75 2)) ≡ 0xc006000000000000
_ = refl

_ : round binary32 (negate (decimalOf 2 75 2)) ≡ 0xc0300000
_ = refl

-- `-3.14` is NOT exact at either format, so this is the one that exercises
-- round-to-nearest-even on a negative significand rather than the sign bit
-- alone. Compare the positive twin pinned above at `0x40091eb851eb851f`:
-- identical below the sign, which is the claim.
_ : round binary64 (negate (decimalOf 3 14 2)) ≡ 0xc0091eb851eb851f
_ = refl

_ : round binary32 (negate (decimalOf 3 14 2)) ≡ 0xc048f5c3
_ = refl

-- `-16777217.0` at binary32 — a TIE, resolved by round-half-to-even. The tie
-- must break the same way on both signs; had `roundHalfEven` been reached with
-- the sign folded into the significand instead of beside it, this is where it
-- would show.
_ : round binary32 (negate (decimalOf 16777217 0 1)) ≡ 0xcb800000
_ = refl

-- `-0.1`, negative and inexact at both formats, one ulp apart in the two.
_ : round binary64 (negate (decimalOf 0 1 1)) ≡ 0xbfb999999999999a
_ = refl

_ : round binary32 (negate (decimalOf 0 1 1)) ≡ 0xbdcccccd
_ = refl

-- A DECIMAL HAS NO NEGATIVE ZERO: `negate` is `ℤ.-` on the significand and
-- `ℤ.- (+ 0) ≡ + 0`, so `negate 0.0` rounds to `+0`. That is why the literal
-- `-0.0` is rejected (`Spec.Surface.Syntax.NegativeZero`, plan 0.150 R6) rather
-- than read as `+0.0`; `-0.0` the value is the negation `-(0.0)`, `negV`, and
-- encodes as glibc's `0x8000000000000000`.
_ : round binary64 (negate (decimalOf 0 0 1)) ≡ 0
_ = refl

_ : round binary32 (negate (decimalOf 0 0 1)) ≡ 0
_ = refl

_ : encode binary64 (negV (roundDec binary64 (decimalOf 0 0 1))) ≡ 0x8000000000000000
_ = refl

_ : encode binary32 (negV (roundDec binary32 (decimalOf 0 0 1))) ≡ 0x80000000
_ = refl
