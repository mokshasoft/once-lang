-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Float.Decimal — THE LITERAL'S PAYLOAD, AND THE ONE ROUNDING
-- (plan 0.74 K0/K1, D116).
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
-- is EXACTLY ONE rounding, at the backend, at the target's format. Agda's
-- `Float` would round first and round again — harmless for binary32-via-
-- binary64 by Figueroa (53 ≥ 2·24+2) but it CAPS PRECISION at the payload's
-- format, so binary128 or x87-extended could never be served. It is also
-- D109/D112's mistake: a format baked where all targets must be served.
--
-- `(ℤ , ℕ)` as integer-part/fraction-part was rejected too, and the second
-- reason is silent: `3.14` and `3.014` both give `(3 , 14)` unless the DIGIT
-- COUNT rides along, and `-0.5` has integer part `-0 = 0`, so THE SIGN IS
-- LOST. Putting the sign on the significand is what avoids that.
------------------------------------------------------------------------

module Once.Float.Decimal where

open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _*_; _∸_; _^_; NonZero)
open import Data.Nat.DivMod using (_/_; _%_)
open import Data.Nat.Properties using (m^n≢0; m*n≢0)
open import Data.Integer using (ℤ; +_; -[1+_]; ∣_∣)
import Data.Integer as ℤ
open import Data.Bool using (if_then_else_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Float.Dyadic
  using (Dyadic; _/2^_; FloatFormat; sig-bits; exp-bits; encode; bitLen;
         binary32; binary64)

------------------------------------------------------------------------
-- The payload
--
-- `Dyadic` is `sig /2^ shift`; this is the SAME record in base ten. It holds
-- every decimal literal EXACTLY — `3.1` is `31 /10^ 1`, no rounding.
--
-- UNNORMALISED, exactly as `Dyadic` is: `0.5` and `0.50` are distinct records
-- (`5 /10^ 1` vs `50 /10^ 2`). They must round to the same word, and that is a
-- lemma to prove rather than a coincidence to assume — see the pins below,
-- which include the pair.
------------------------------------------------------------------------

record Decimal : Set where
  constructor _/10^_
  field
    sig   : ℤ      -- SIGNED, so `-0.5` is `-5 /10^ 1` and the sign survives
    exp10 : ℕ

open Decimal public

-- | The whole number `n`.
fromℕ : ℕ → Decimal
fromℕ n = (+ n) /10^ 0

-- | Negation — total, and the reason `sig` is signed. Plan 0.73's F3
-- (negative float literals) is this and nothing more.
negate : Decimal → Decimal
negate (m /10^ e) = (ℤ.- m) /10^ e

-- | The lexer's triple, as a decimal: `RFloat i f l` is `i.f` with `l`
-- fraction digits, so its value is `i + f/10^l` and its exact significand is
-- `i·10^l + f`.
--
-- TOTAL, and that is K3's whole content. This used to be `accept? i f l`,
-- returning a `Maybe (Σ Dyadic (Accepted …))` — partial, because `3.14` has no
-- dyadic to return. Every literal has a decimal.
decimalOf : ℕ → ℕ → ℕ → Decimal
decimalOf i f l = (+ (i * 10 ^ l + f)) /10^ l

------------------------------------------------------------------------
-- ROUND-TO-NEAREST-EVEN, on integers
------------------------------------------------------------------------

-- | `q` or `q+1`, deciding by the remainder against half the divisor, and
-- breaking the exact tie TOWARDS EVEN.
--
-- Comparing `2r` with `den` rather than `r` with `den/2` is what keeps the
-- half-way case exact: `den/2` would itself truncate on an odd divisor and
-- turn a tie into a below-half.
roundHalfEven : ℕ → ℕ → ℕ → ℕ
roundHalfEven q r den =
  if      (2 * r) ℕ.<ᵇ den then q
  else if den ℕ.<ᵇ (2 * r) then suc q
  else if (_%_ q 2 {{_}}) ℕ.≡ᵇ 0 then q else suc q

-- | `num / den`, correctly rounded.
divRHE : ℕ → (den : ℕ) → {{NonZero den}} → ℕ
divRHE num den = roundHalfEven (num / den) (num % den) den

------------------------------------------------------------------------
-- THE ONE ROUNDING
--
-- `round F d` is the target's bit pattern for the decimal `d`. It is built as
-- "round to a `P`-bit dyadic, then encode that dyadic", which is worth stating
-- because it means the existing encoder is REUSED rather than reimplemented —
-- and `encode` is the function the pinned patterns at the bottom of
-- `Once.Float.Dyadic` already check.
--
-- `encode` TRUNCATES (`sigFieldN` drops low bits via `modPow`), and was
-- correct only because `accept?` guaranteed nothing was there to drop. Here
-- nothing is there to drop for a different and better reason: `roundToDyadic`
-- delivers a significand of at most `P = sig-bits + 1` bits, so the truncation
-- is a no-op and the rounding has already happened, once, in the right place.
------------------------------------------------------------------------

-- | A shift big enough that `n · 2^S ≥ 10^e`, so the first division is
-- non-zero and its bit length is a true binary exponent.
--
-- `4e` because `2^4 = 16 > 10`; the `+ sig-bits + 4` is headroom for the
-- significand itself. Generous on purpose — it costs a wider intermediate and
-- buys not having to prove a tight bound.
guardShift : FloatFormat → ℕ → ℕ
guardShift F e = 4 * e + sig-bits F + 4

-- | `⌊log₂ (n / 10^e)⌋ + 1`, read off a scaled truncated division.
--
-- Truncation is safe HERE: flooring cannot cross a power-of-two boundary
-- downwards, so the bit length of the floor is the bit length of the value.
binLen : FloatFormat → ℕ → ℕ → ℕ
binLen F n e =
  bitLen (_/_ (n * 2 ^ guardShift F e) (10 ^ e) {{m^n≢0 10 e}})

-- | The magnitude, rounded to a `P`-bit dyadic.
--
-- NO CARRY HANDLING, deliberately: if rounding carries out of the significand
-- (`1.111…1` → `10.000…0`) the result is `2^P`, and `encode` normalises it for
-- free — `bitLen` sees `P+1` bits, the leading-bit strip leaves 0, and the
-- exponent comes out one larger. Special-casing it would be a second place to
-- get the same thing wrong.
roundMag : FloatFormat → ℕ → ℕ → Dyadic
roundMag F zero      e = (+ 0) /2^ 0
roundMag F n@(suc _) e = go ((+ (suc (sig-bits F) + guardShift F e)) ℤ.- (+ binLen F n e))
  where
    go : ℤ → Dyadic
    -- scale UP: m ≈ n·2^t / 10^e, so the value is m / 2^t
    go (+ t)    = (+ divRHE (n * 2 ^ t) (10 ^ e) {{m^n≢0 10 e}}) /2^ t
    -- scale DOWN: m ≈ n / (10^e · 2^(k+1)), so the value is m · 2^(k+1)
    go -[1+ k ] =
      (+ (divRHE n (10 ^ e * 2 ^ suc k)
                {{m*n≢0 (10 ^ e) (2 ^ suc k) {{m^n≢0 10 e}} {{m^n≢0 2 (suc k)}}}}
              * 2 ^ suc k)) /2^ 0

-- | …and with the sign put back. IEEE-754 is sign-magnitude, so the sign never
-- takes part in the rounding.
roundToDyadic : FloatFormat → Decimal → Dyadic
roundToDyadic F d = signed (sig d) (roundMag F ∣ sig d ∣ (exp10 d))
  where
    signed : ℤ → Dyadic → Dyadic
    signed (+ _)    r = r
    signed -[1+ _ ] r = Once.Float.Dyadic.negate r

-- | THE function. Both the denotation and the codegen call THIS, which is what
-- makes their correspondence `refl`-shaped and needs no rounding theorem.
--
-- That `round` is the RIGHT function — IEEE round-to-nearest-even — is a
-- SPEC-quality question, not a compiler-correctness one, and it is a NAMED
-- trust point of the same kind as `assemble-correct`. What must not happen is
-- the version where nobody states it and the compiler is "correct" about a
-- rounding nobody checked: that is `emit`'s low byte again (D114).
round : FloatFormat → Decimal → ℕ
round F d = encode F (roundToDyadic F d)

------------------------------------------------------------------------
-- PINNED PATTERNS
--
-- D109's lesson, and this module is where it applies hardest. A rounding
-- routine that both sides of the correspondence call is UNFALSIFIABLE from
-- inside the development: the compiler and the meaning agree by construction
-- whatever it computes. `Once.Float.Dyadic` learned this when an encoder that
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
