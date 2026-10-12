-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Float.DyadicLaws — the encoding's range, and its patterns pinned by `refl`.
------------------------------------------------------------------------

module Once.Float.DyadicLaws where


import Data.Nat
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-trans)
open import Data.Nat.DivMod using (_/_; _%_; m%n<n)
import Data.Integer as ℤ
open import Data.Integer using (ℤ; +_; -[1+_]; ∣_∣)
open import Data.Nat.Properties using (m^n≢0)
open import Data.Nat.Properties using (m^n>0)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Spec.Float.Dyadic
open Dyadic
open FloatFormat

modPow< : ∀ x k → modPow x k < 2 ^ k
modPow< x k = m%n<n x (2 ^ k) {{m^n≢0 2 k}}

-- NOT private (plan 0.74 K2): `Once.Spec.Float.Decimal.encodeClamped-fits` needs
-- it for the ±∞ and ±0 patterns, which are packed the same way.
-- Two fields, each in range, pack into their combined width.
  -- `k` and `j` are EXPLICIT: they occur only under `_^_`, and the unifier
  -- cannot invert `2 ^ ?k ≟ 2 ^ (exp-bits F)` — a function application, not a
  -- constructor pattern. Left implicit this leaves unsolved metas at every use.
combine-bound : ∀ {e m} (k j : ℕ) → e < 2 ^ k → m < 2 ^ j
              → e * (2 ^ j) + m < 2 ^ (k + j)
combine-bound {e} {m} k j e< m< = lemma
  where
    open import Data.Nat.Properties
      using (+-monoʳ-<; *-monoˡ-≤; ^-distribˡ-+-*; +-comm; <-≤-trans; ≤-reflexive)
    open import Relation.Binary.PropositionalEquality using (sym)

    step1 : e * (2 ^ j) + m < e * (2 ^ j) + 2 ^ j
    step1 = +-monoʳ-< (e * (2 ^ j)) m<

    step2 : e * (2 ^ j) + 2 ^ j ≡ suc e * (2 ^ j)
    step2 = +-comm (e * (2 ^ j)) (2 ^ j)

    step3 : suc e * (2 ^ j) ≤ (2 ^ k) * (2 ^ j)
    step3 = *-monoˡ-≤ (2 ^ j) e<

    step4 : (2 ^ k) * (2 ^ j) ≡ 2 ^ (k + j)
    step4 = sym (^-distribˡ-+-* 2 k j)

    lemma : e * (2 ^ j) + m < 2 ^ (k + j)
    lemma = <-≤-trans step1
              (≤-trans (≤-reflexive step2)
                (≤-trans step3 (≤-reflexive step4)))
-- was) needed a parameter (`LitFits.float-fits`) because the standard library
-- states no bound on `primFloatToWord`.
--
-- The width is now `1 + exp-bits + sig-bits` — the sign bit included, i.e. the
-- format's ACTUAL width. For binary64 that is exactly 64 and for binary32
-- exactly 32, so each target's `float-fits` is this theorem with nothing to
-- add: the bound and the register are the same size, as they always should
-- have been.
encodeMag-fits : ∀ F m e → encodeMag F m e < 2 ^ (exp-bits F + sig-bits F)
encodeMag-fits F zero    e = m^n>0 2 (exp-bits F + sig-bits F)
encodeMag-fits F (suc m) e =
  combine-bound (exp-bits F) (sig-bits F)
                (modPow< ((bias F + (bitLen (suc m) ∸ 1)) ∸ e) (exp-bits F))
                (modPow< ((suc m ∸ 2 ^ (bitLen (suc m) ∸ 1))
                            * 2 ^ (sig-bits F ∸ (bitLen (suc m) ∸ 1)))
                         (sig-bits F))

signBit< : ∀ z → signBit z < 2
signBit< (+ _)    = s≤s z≤n              -- 0 < 2
signBit< -[1+ _ ] = s≤s (s≤s z≤n)        -- 1 < 2

encode-fits : ∀ F d → encode F d < 2 ^ (1 + (exp-bits F + sig-bits F))
encode-fits F d =
  combine-bound 1 (exp-bits F + sig-bits F)
                (signBit< (sig d))
                (encodeMag-fits F ∣ sig d ∣ (shift d))

------------------------------------------------------------------------
-- THE PINNED PATTERNS
--
-- Bit patterns computed OUTSIDE this module, checked by `refl` at typecheck
-- time. They are the only thing here that could have caught the crossed fields
-- described above, because every other property of the encoder — its range, its
-- agreement with the machine — holds just as well for a wrong encoder.
--
-- Each is a value plan 0.71's F4 will accept (exactly representable at every
-- supported format), which is also what makes them the right regression set.
------------------------------------------------------------------------

private
  -- POSITIVES — patterns computed outside this module.
  -- 1.0 → 0x3F800000 / 0x3FF0000000000000
  _ : encode binary32 ((+ 1) /2^ 0) ≡ 1065353216
  _ = refl
  _ : encode binary64 ((+ 1) /2^ 0) ≡ 4607182418800017408
  _ = refl

  -- 0.5 = 1/2 → 0x3F000000 (exponent one below the bias, fraction 0)
  _ : encode binary32 ((+ 1) /2^ 1) ≡ 1056964608
  _ = refl

  -- 1.5 = 3/2 → 0x3FC00000: the first case with a NON-ZERO fraction, so it is
  -- the one that separates a real normalisation from a field-shuffle.
  _ : encode binary32 ((+ 3) /2^ 1) ≡ 1069547520
  _ = refl

  -- 2.75 = 11/4 → 0x40300000
  _ : encode binary32 ((+ 11) /2^ 2) ≡ 1076887552
  _ = refl

  -- 0.0 → all bits clear, by `encodeMag`'s own clause and not by the formula.
  _ : encode binary32 ((+ 0) /2^ 0) ≡ 0
  _ = refl
  _ : encode binary64 ((+ 0) /2^ 5) ≡ 0
  _ = refl

  -- NEGATIVES — the sign bit is the top bit, so each is its positive twin plus
  -- 2 ^ 31 (binary32) or 2 ^ 63 (binary64). Written through `negate`, so these
  -- pin the OPERATION as well as the encoding.
  _ : encode binary32 (negate ((+ 1) /2^ 0)) ≡ 3212836864   -- -1.0  0xBF800000
  _ = refl
  _ : encode binary32 (negate ((+ 1) /2^ 1)) ≡ 3204448256   -- -0.5  0xBF000000
  _ = refl
  _ : encode binary32 (negate ((+ 3) /2^ 1)) ≡ 3217031168   -- -1.5  0xBFC00000
  _ = refl
  _ : encode binary32 (negate ((+ 11) /2^ 2)) ≡ 3224371200  -- -2.75 0xC0300000
  _ = refl
  _ : encode binary64 (negate ((+ 1) /2^ 0)) ≡ 13830554455654793216
  _ = refl

  -- …and negating zero stays `+0`: `ℤ` has one zero, so there is no `−0`.
  _ : encode binary32 (negate ((+ 0) /2^ 0)) ≡ 0
  _ = refl

  -- Negation is an involution on the carrier, which the sign-magnitude
  -- encoding does NOT make obvious — worth one line.
  _ : negate (negate ((+ 3) /2^ 1)) ≡ ((+ 3) /2^ 1)
  _ = refl