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
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Nat.DivMod using (_/_; _%_)
open import Data.Nat.Properties
  using (m^n≢0; m*n≢0; m^n>0; *-monoˡ-<; ∸-monoʳ-<; ^-distribˡ-+-*)
open import Data.Integer using (ℤ; +_; -[1+_]; ∣_∣)
import Once.Float.Dyadic
import Data.Integer as ℤ
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Once.Float.Dyadic
  using (Dyadic; _/2^_; FloatFormat; sig-bits; exp-bits; encode; encode-fits;
         bitLen; binary32; binary64; bias; signBit; signBit<; combine-bound;
         modPow; modPow<)

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

-- | The lexer's triple, as a decimal: `RFloat i f l` _ is `i.f` with `l`
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

-- | The magnitude rounded to a `P`-bit significand, WITH ITS BINARY EXPONENT.
--
-- The value is `m · 2^E`, and `E` is a `ℤ` because a large literal needs a
-- positive one and a small literal a negative one. That asymmetry is exactly
-- what `Dyadic`'s ℕ `shift` cannot express, and it is why `round` does not
-- route through `Dyadic.encode`:
--
--     round binary64 1e41  =  0x4870000000000000   -- a pure power of two
--
-- Writing the value as `(m · 2^K) /2^ 0` to fit the ℕ shift put K zero bits
-- BELOW the significand, and `sigFieldN` can only left-align — its
-- `2 ^ (sig-bits ∸ (bitLen ∸ 1))` clamps to `2^0` and `modPow` then keeps the
-- low `sig-bits` bits, which were the zeros. The whole fraction was lost:
-- `0x25dfa371a19e7` became `0x0`. `encode`'s documented precondition (a
-- significand the format can hold) was being violated by the very step meant
-- to satisfy it.
--
-- NO CARRY HANDLING, deliberately: if rounding carries (`1.111…1` →
-- `10.000…0`) the result is `2^P`, and `bitLen`/`fracField` normalise it for
-- free — the leading-bit strip leaves 0 and the exponent comes out one larger.
roundSig : FloatFormat → ℕ → ℕ → ℕ × ℤ
roundSig F zero      e = 0 , (+ 0)
roundSig F n@(suc _) e = go ((+ (suc (sig-bits F) + guardShift F e)) ℤ.- (+ binLen F n e))
  where
    go : ℤ → ℕ × ℤ
    -- scale UP: m ≈ n·2^t / 10^e, so the value is m · 2^(−t)
    go (+ t)    = divRHE (n * 2 ^ t) (10 ^ e) {{m^n≢0 10 e}} , ℤ.- (+ t)
    -- scale DOWN: m ≈ n / (10^e·2^(k+1)), so the value is m · 2^(k+1)
    go -[1+ k ] =
      divRHE n (10 ^ e * 2 ^ suc k)
             {{m*n≢0 (10 ^ e) (2 ^ suc k) {{m^n≢0 10 e}} {{m^n≢0 2 (suc k)}}}}
      , (+ suc k)

------------------------------------------------------------------------
-- THE EXPONENT RANGE (plan 0.74 K2)
--
-- `accept?`'s other two conditions were `exp-lo` and `exp-hi`: the value had
-- to land in the NORMAL exponent range. Deleting them (K3) means answering
-- what happens OUTSIDE it, and the answer cannot be "whatever `encode` does",
-- because what `encode` does is WRAP — `expFieldN` ends in
-- `modPow … (exp-bits F)`, so a stored exponent of 260 at binary32 came out as
-- 4 and `1e41` encoded as a small FINITE number. That is the same silent value
-- substitution D115 forbids for `Int` literals, and worse, because nothing
-- gated it at all.
--
-- IEEE's answer above the range is ±∞, and D116's own argument settles that
-- Once should give it: the promise `Float` makes is the hardware's, and the
-- hardware produces ±∞. `⟦ Float ⟧` is the target's bit pattern (D113), so an
-- infinity is just a pattern — nothing in the value model changes.
--
-- BELOW the range IEEE gives SUBNORMALS, and Once does not model them: the
-- result is ZERO. That is a REAL limitation, stated here rather than
-- discovered later — see the `1e-40` pin, which glibc stores as the subnormal
-- `0x000116c2` and we store as `0`. It is BOUNDED (the value was already tiny)
-- where the overflow wrap was not, which is why the two are not treated alike.
------------------------------------------------------------------------

-- | `bias + (bitLen m − 1) + E`, in ℤ so it can be out of range in either
-- direction and be RANGE-CHECKED rather than wrapped.
storedExp : FloatFormat → ℕ → ℤ → ℤ
storedExp F m E = (+ (bias F + (bitLen m ∸ 1))) ℤ.+ E

-- | The largest stored exponent denoting a FINITE number. `2^e − 1` is
-- reserved for ±∞ and NaN.
maxFiniteExp : FloatFormat → ℕ
maxFiniteExp F = (2 ^ exp-bits F) ∸ 2

-- | The fraction field: the significand with its leading bit stripped, aligned
-- to `sig-bits`. Only ONE of the two shifts is ever non-trivial — `∸` picks —
-- and the RIGHT shift is exact, because `roundSig` already rounded those bits
-- away. That right shift is the thing `sigFieldN` could not do.
fracField : FloatFormat → ℕ → ℕ
fracField F m =
  modPow (_/_ ((m ∸ 2 ^ (bitLen m ∸ 1)) * 2 ^ (sig-bits F ∸ (bitLen m ∸ 1)))
              (2 ^ ((bitLen m ∸ 1) ∸ sig-bits F))
              {{m^n≢0 2 ((bitLen m ∸ 1) ∸ sig-bits F)}})
         (sig-bits F)

-- | ±∞: exponent all ones, significand zero.
infinity : FloatFormat → ℕ → ℕ
infinity F sb =
  sb * (2 ^ (exp-bits F + sig-bits F)) + ((2 ^ exp-bits F) ∸ 1) * (2 ^ sig-bits F)

-- | ±0. The `+ 0` is deliberate: every pattern here is a sign bit above an
-- `(exp-bits + sig-bits)`-wide magnitude, and writing ±0 in that shape means
-- ONE range lemma covers all three branches.
signedZero : FloatFormat → ℕ → ℕ
signedZero F sb = sb * (2 ^ (exp-bits F + sig-bits F)) + 0

-- Each decision is a separate aux taking its scrutinee as an ARGUMENT rather
-- than a nested `if` under a `with`. Same convention as `cfm-build-gated`
-- taking its `Dec`: a proof that cases on the decision then reduces.
packHi : FloatFormat → ℕ → ℕ → ℕ → Bool → ℕ
packHi F sb m se true  = infinity F sb
packHi F sb m se false =
  sb * (2 ^ (exp-bits F + sig-bits F)) + (modPow se (exp-bits F) * (2 ^ sig-bits F) + fracField F m)

packSE : FloatFormat → ℕ → ℕ → ℤ → ℕ
packSE F sb m -[1+ _ ]  = signedZero F sb          -- underflow: no subnormals
packSE F sb m (+ zero)  = signedZero F sb          -- likewise
packSE F sb m (+ suc e) = packHi F sb m (suc e) (maxFiniteExp F ℕ.<ᵇ suc e)

packAt : FloatFormat → ℕ → ℕ → ℤ → ℕ
packAt F sb zero    E = signedZero F sb
packAt F sb (suc m) E = packSE F sb (suc m) (storedExp F (suc m) E)

-- | THE function. Both the denotation and the codegen call THIS, which is what
-- makes their correspondence `refl`-shaped and needs no rounding theorem.
--
-- That `round` is the RIGHT function — IEEE round-to-nearest-even — is a
-- SPEC-quality question, not a compiler-correctness one, and it is a NAMED
-- trust point of the same kind as `assemble-correct`. What must not happen is
-- the version where nobody states it and the compiler is "correct" about a
-- rounding nobody checked: that is `emit`'s low byte again (D114).
round : FloatFormat → Decimal → ℕ
-- Projected rather than destructured: a `where pack (m , E) = …` would stop
-- `round F d` reducing for an abstract `d`, and `round-fits` below needs it to.
round F d = packAt F (signBit (sig d))
                     (proj₁ (roundSig F ∣ sig d ∣ (exp10 d)))
                     (proj₂ (roundSig F ∣ sig d ∣ (exp10 d)))

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
