-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Float.DecimalLaws — the rounding's range, and its results pinned by `refl`.
------------------------------------------------------------------------

module Once.Float.DecimalLaws where

open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _*_; _∸_; _^_; NonZero)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Nat.DivMod using (_/_; _%_)
open import Data.Nat.Properties
  using (m^n≢0; m*n≢0; m^n>0; *-monoˡ-<; ∸-monoʳ-<; ^-distribˡ-+-*)
open import Data.Integer using (ℤ; +_; -[1+_]; ∣_∣)
import Once.Spec.Float.Dyadic
import Data.Integer as ℤ
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Once.Spec.Float.Dyadic
  using (FloatFormat; bitLen; binary32; binary64; bias; signBit; modPow)
open import Once.Float.DyadicLaws using (signBit<; combine-bound; modPow<)
open Once.Spec.Float.Dyadic.FloatFormat using (exp-bits; sig-bits)
open import Once.Spec.Float.Decimal
open Decimal

------------------------------------------------------------------------
-- RANGE
--
-- All three patterns are packed identically — a sign bit above an
-- `(exp-bits + sig-bits)`-wide magnitude — so `combine-bound` discharges each
-- the same way. The only arithmetic worth naming is that the infinity
-- magnitude `(2^e − 1)·2^s` is `2^(e+s) − 2^s`: strictly INSIDE the field
-- rather than at its boundary, which is what makes ±∞ a representable pattern
-- and not an overflow of its own.
------------------------------------------------------------------------

private
  magInf : ∀ F → ((2 ^ exp-bits F) ∸ 1) * (2 ^ sig-bits F)
                   ℕ.< 2 ^ (exp-bits F + sig-bits F)
  magInf F =
    subst (λ z → ((2 ^ exp-bits F) ∸ 1) * (2 ^ sig-bits F) ℕ.< z)
          (sym (^-distribˡ-+-* 2 (exp-bits F) (sig-bits F)))
          (*-monoˡ-< (2 ^ sig-bits F) {{m^n≢0 2 (sig-bits F)}}
                     (∸-monoʳ-< (ℕ.s≤s ℕ.z≤n) (m^n>0 2 (exp-bits F))))

  magFin : ∀ F m se → modPow se (exp-bits F) * (2 ^ sig-bits F) + fracField F m
                        ℕ.< 2 ^ (exp-bits F + sig-bits F)
  magFin F m se = combine-bound (exp-bits F) (sig-bits F)
                                (modPow< se (exp-bits F))
                                (modPow< _ (sig-bits F))

packHi-fits : ∀ F sb m se b → sb ℕ.< 2
            → packHi F sb m se b ℕ.< 2 ^ (1 + (exp-bits F + sig-bits F))
packHi-fits F sb m se true  sb< = combine-bound 1 (exp-bits F + sig-bits F) sb< (magInf F)
packHi-fits F sb m se false sb< = combine-bound 1 (exp-bits F + sig-bits F) sb< (magFin F m se)

packSE-fits : ∀ F sb m E → sb ℕ.< 2
            → packSE F sb m E ℕ.< 2 ^ (1 + (exp-bits F + sig-bits F))
packSE-fits F sb m -[1+ _ ]  sb< = combine-bound 1 (exp-bits F + sig-bits F) sb< (m^n>0 2 (exp-bits F + sig-bits F))
packSE-fits F sb m (+ zero)  sb< = combine-bound 1 (exp-bits F + sig-bits F) sb< (m^n>0 2 (exp-bits F + sig-bits F))
packSE-fits F sb m (+ suc e) sb< = packHi-fits F sb m (suc e) (maxFiniteExp F ℕ.<ᵇ suc e) sb<

packAt-fits : ∀ F sb m E → sb ℕ.< 2
            → packAt F sb m E ℕ.< 2 ^ (1 + (exp-bits F + sig-bits F))
packAt-fits F sb zero    E sb< = combine-bound 1 (exp-bits F + sig-bits F) sb< (m^n>0 2 (exp-bits F + sig-bits F))
packAt-fits F sb (suc m) E sb< = packSE-fits F sb (suc m) (storedExp F (suc m) E) sb<

-- | …a THEOREM, where D109's `primFloatToWord` needed a parameter.
round-fits : ∀ F d → round F d ℕ.< 2 ^ (1 + (exp-bits F + sig-bits F))
round-fits F d =
  packAt-fits F (signBit (sig d))
              (proj₁ (roundSig F ∣ sig d ∣ (exp10 d)))
              (proj₂ (roundSig F ∣ sig d ∣ (exp10 d)))
              (signBit< (sig d))

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

-- The lexer's triple, end to end: `3.14` is `RFloat 3 14 2`. _
_ : round binary64 (decimalOf 3 14 2) ≡ 0x40091eb851eb851f
_ = refl

-- `16777217.0` — `RFloat 16777217 0 1`. _ Compiles at BOTH formats now (D116);
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

-- UNDERFLOW → ZERO, and this is a STATED LIMITATION, not a claim of IEEE
-- conformance. glibc stores `1e-40` at binary32 as the SUBNORMAL `0x000116c2`;
-- Once has no subnormals and stores `0`. Bounded (the value was already tiny)
-- where the overflow wrap was not, which is why the two are not treated alike.
-- Recorded here so it is read rather than discovered.
_ : round binary32 ((+ 1) /10^ 40) ≡ 0
_ = refl

-- The same literal is NORMAL at binary64, so it is exact there.
_ : round binary64 ((+ 1) /10^ 40) ≡ 0x37a16c262777579c
_ = refl

------------------------------------------------------------------------
-- F3: THE NEGATED LITERAL, pinned (plan 0.73 F3)
--
-- `-3.14` is ONE literal whose payload is `negate (decimalOf 3 14 2)` — the
-- elaborator folds the minus (`Once.TypeCheck.Elaborate`'s
-- `inferElabV-neg-aux … (nov-float …)`) and `Once.Denotation.Meaning`'s
-- `⟦ t-neg-float ⟧ᵢ` reads the same payload. THAT IS EXACTLY WHY THESE PINS
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

-- NEGATIVE ZERO IS A STATED LIMITATION, alongside the subnormals of D118.
-- `negate` is `ℤ.-` on the significand and `ℤ.- (+ 0) ≡ + 0`, so `signBit`
-- reads `0` and `-0.0` compiles to POSITIVE zero. IEEE keeps the two apart
-- (glibc stores `0x8000000000000000`); Once does not.
--
-- It is bounded in the same way the missing subnormals are: the value is zero
-- either way, and only `1/x`, `copysign` and the sign of a zero result can
-- tell the difference — none of which Once has, since it has no float
-- ARITHMETIC at all (F4). If F4 lands, this pin is the one that has to change
-- first, and that is why it is written down rather than left to be found.
_ : round binary64 (negate (decimalOf 0 0 1)) ≡ 0
_ = refl

_ : round binary32 (negate (decimalOf 0 0 1)) ≡ 0
_ = refl