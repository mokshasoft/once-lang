{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Float.Dyadic — the WIDTH-FREE float carrier, and the per-target
-- formats that encode it (plan 0.72, D112).
--
-- `Int`'s payload is `Carrier = ℕ`: exact, width-free, with the target's width
-- applied at the machine by `norm`. This is the same thing for `Float`.
--
-- A literal denotes a non-negative DYADIC RATIONAL `m / 2 ^ e`. Exact, so
-- nothing rounds in the frontend; width-free, so no target is baked in; and a
-- PAYLOAD rather than an arithmetic domain — float arithmetic is SigOps and
-- stays so, exactly as `Carrier` is not where `Int` arithmetic happens.
--
-- Deliberately NOT Agda's `Float`: that is a 64-bit double, and using it here
-- is what forced D109's lossy encoder and left its faithfulness unstateable.
------------------------------------------------------------------------

module Once.Spec.Float.Dyadic where

import Data.Nat
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-trans)
open import Data.Nat.DivMod using (_/_; _%_; m%n<n)
import Data.Integer as ℤ
open import Data.Integer using (ℤ; +_; -[1+_]; ∣_∣)
open import Data.Nat.Properties using (m^n≢0)
open import Data.Nat.Properties using (m^n>0)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- THE CARRIER
------------------------------------------------------------------------

-- | A dyadic rational: `sig / 2 ^ shift`, with `sig` an INTEGER.
--
-- `sig : ℤ`, not `ℕ`. A dyadic rational is `m / 2 ^ e` with `m ∈ ℤ` — signed
-- by definition — and the earlier `ℕ` here was an unjustified restriction that
-- made the type not mean its own name. It also made float negation look
-- impossible: `fneg-semM : Dyadic → Dyadic` had no negative value to return,
-- so the language could not write `-1.5` at all. That was an accident of this
-- definition, not a fact about floats.
--
-- Not normalised (`sig` need not be odd). Normalisation is a property some
-- consumers want, not an invariant the carrier enforces — keeping it out means
-- the type has no proof obligations attached to construction, exactly as ℤ has
-- none for `Int`.
--
-- ±0: IEEE-754 is sign-magnitude and distinguishes `+0` from `−0`. The
-- RATIONALS do not, and this carrier is the value model, so the two collapse
-- here and `encode` maps zero to `+0`. That is deliberate — the meaning of a
-- value should be the mathematics — but it becomes observable the day `1/x` or
-- `signbit` exists, so it is a decision and not an oversight.
record Dyadic : Set where
  constructor _/2^_
  field
    sig   : ℤ
    shift : ℕ

open Dyadic

-- | The whole number `n`.
fromℕ : ℕ → Dyadic
fromℕ n = (+ n) /2^ 0

-- | Negation — total, and the reason `sig` is signed.
negate : Dyadic → Dyadic
negate (m /2^ e) = (ℤ.- m) /2^ e

------------------------------------------------------------------------
-- THE FORMATS
--
-- A target's float format, as the two numbers that determine it. Single and
-- double are VALUES here, not separate functions — which is the whole point:
-- adding a target adds a value, not a code path.
------------------------------------------------------------------------

record FloatFormat : Set where
  constructor mkFormat
  field
    sig-bits : ℕ      -- significand field width (23 single, 52 double)
    exp-bits : ℕ      -- exponent field width     (8 single, 11 double)

open FloatFormat

binary32 : FloatFormat
binary32 = mkFormat 23 8

binary64 : FloatFormat
binary64 = mkFormat 52 11

-- | Total width in bits: sign + exponent + significand.
width : FloatFormat → ℕ
width F = suc (exp-bits F + sig-bits F)

-- | The exponent bias: 2 ^ (exp-bits − 1) − 1 (127 single, 1023 double).
bias : FloatFormat → ℕ
bias F = (2 ^ (exp-bits F ∸ 1)) ∸ 1

-- Reduction modulo 2 ^ k, with the `NonZero` witness supplied EXPLICITLY
-- rather than left to instance search — the divisor is `2 ^ k` for a variable
-- `k`, which search cannot discharge on its own. Both the operation and its
-- bound are stated here so every field below gets them together.
modPow : ℕ → ℕ → ℕ
modPow x k = _%_ x (2 ^ k) {{m^n≢0 2 k}}


------------------------------------------------------------------------
-- THE ENCODING, and its RANGE — proved, not assumed.
--
-- `LitFits.float-fits` exists on all three arches today because `float-bits` (as it was)
-- is `primFloatToWord` and the standard library states no bound on it. Here
-- the encoder is ℕ arithmetic over fields whose widths ARE the format, so the
-- bound is a theorem and the parameter goes away (plan 0.72 P3).
--
-- The carrier is non-negative, so the SIGN BIT IS ALWAYS 0 — negation is an
-- operation, not part of a literal, exactly as `intLit` takes `∣ n ∣`.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- NORMALISATION: `sig / 2 ^ shift` ↦ `1.f × 2 ^ E`
--
-- IEEE-754 does not store a dyadic pair. It stores a BIASED EXPONENT and the
-- FRACTION of a significand normalised to `1.f`, and getting from one to the
-- other is the whole content of the encoder. For `m / 2 ^ e` with `m > 0`, let
-- `L` be `m`'s bit length. Then
--
--     m / 2 ^ e  =  1.f × 2 ^ (L − 1 − e)
--
-- so the stored exponent is `bias + (L − 1) − e` and the fraction is `m` with
-- its leading bit removed, left-aligned into `sig-bits`.
--
-- Writing the pair straight into the two fields — exponent ← `sig`, fraction ←
-- `shift` — is what this module did until 2026-08-18. It typechecked, it
-- satisfied `encode-fits` (both are residues), and the machine correspondence
-- held BY CONSTRUCTION because both sides call this same function. Nothing in
-- the tree could refute it, because no source program can produce a float
-- literal yet. The pinned patterns at the bottom of this module are the answer:
-- an encoder must be checked against numbers someone else computed.
------------------------------------------------------------------------

-- | Bit length: `bitLen 0 = 0`, else `⌊log₂ m⌋ + 1`.
--
-- NOT the library's `⌊log₂_⌋`, and the reason is REDUCTION COST rather than
-- taste. `⌊log₂_⌋` is defined by well-founded recursion, so evaluating it on a
-- numeral normalises `<-wellFounded n` — an accessibility tree built by
-- induction on `n`, i.e. LINEAR in the number. That is invisible on the small
-- significands the pins below use, and hopeless at `2 ^ 24 + 1`, which is
-- exactly the size `Once.Float.Representable`'s cross-target pin needs (the
-- first significand binary32 cannot hold). Found the hard way: that pin did
-- not finish.
--
-- Halving with fuel is structural, reduces in ⌈log₂ n⌉ steps, and each step is
-- a builtin division. `n` is always enough fuel — the value reaches 0 after
-- that many halvings — and matching `suc` on a numeral does not expand it to
-- unary, so passing the number as its own fuel costs nothing.
bitLen-go : ℕ → ℕ → ℕ
bitLen-go zero       _         = 0
bitLen-go (suc _)    zero      = 0
bitLen-go (suc fuel) n@(suc _) = suc (bitLen-go fuel (n / 2))

bitLen : ℕ → ℕ
bitLen n = bitLen-go n n

-- | The sign bit: IEEE-754 is SIGN-MAGNITUDE, so the sign is a bit beside the
-- magnitude rather than part of it. No comparison needed — `ℤ`'s two
-- constructors are exactly the two cases.
signBit : ℤ → ℕ
signBit (+ _)      = 0
signBit -[1+ _ ]   = 1

-- | The stored (biased) exponent, from the MAGNITUDE: `bias + (L − 1) − shift`.
--
-- The `∸` clamps rather than wrapping, so a value too small for the format
-- lands on the zero/subnormal exponent instead of a nonsense one. Plan 0.71's
-- F4 decides at the SOURCE what may reach here.
expFieldN : FloatFormat → ℕ → ℕ → ℕ
expFieldN F m e = modPow ((bias F + (bitLen m ∸ 1)) ∸ e) (exp-bits F)

-- | The stored fraction: the magnitude minus its leading bit, left-aligned.
sigFieldN : FloatFormat → ℕ → ℕ → ℕ
sigFieldN F m _ =
  modPow ((m ∸ 2 ^ (bitLen m ∸ 1)) * 2 ^ (sig-bits F ∸ (bitLen m ∸ 1))) (sig-bits F)

-- | The magnitude's pattern (exponent and fraction, no sign).
--
-- Zero is its own pattern and NOT the normalisation formula's output —
-- `bitLen 0` has no leading bit to strip, so the general case would emit the
-- bias as an exponent and call it `1.0`.
encodeMag : FloatFormat → ℕ → ℕ → ℕ
encodeMag F zero    _ = 0
encodeMag F (suc m) e = expFieldN F (suc m) e * (2 ^ sig-bits F) + sigFieldN F (suc m) e

-- | The IEEE-754 bit pattern: sign bit above the magnitude.
--
-- `∣ sig d ∣` is the magnitude and `signBit` the sign, which is why the carrier
-- being signed costs nothing here — the format was always sign-magnitude.
-- Both zeros land on `+0`: `ℤ` has a single zero, so there is no `−0` to encode
-- (see the carrier's note).
encode : FloatFormat → Dyadic → ℕ
encode F d =
  signBit (sig d) * (2 ^ (exp-bits F + sig-bits F))
    + encodeMag F ∣ sig d ∣ (shift d)

-- | …and its RANGE, which is the point: a theorem, where `float-bits` (as it

