-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Float.Dyadic — the WIDTH-FREE float carrier, and the per-target
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

module Once.Float.Dyadic where

import Data.Nat
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_; _<_; _≤_; s≤s; z≤n; _≡ᵇ_; _<ᵇ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; +-comm; m≤m+n; m≤n+m; *-comm)
open import Data.Nat.DivMod using (_/_; _%_; m%n<n)
open import Data.Nat.Properties using (m^n≢0)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- THE CARRIER
------------------------------------------------------------------------

-- | A non-negative dyadic rational: `sig / 2 ^ shift`.
--
-- Not normalised (`sig` need not be odd). Normalisation is a property some
-- consumers want, not an invariant the carrier enforces — keeping it out means
-- the type has no proof obligations attached to construction, exactly as ℕ has
-- none for `Int`.
record Dyadic : Set where
  constructor _/2^_
  field
    sig   : ℕ
    shift : ℕ

open Dyadic public

-- | The whole number `n`.
fromℕ : ℕ → Dyadic
fromℕ n = n /2^ 0

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

open FloatFormat public

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

modPow< : ∀ x k → modPow x k < 2 ^ k
modPow< x k = m%n<n x (2 ^ k) {{m^n≢0 2 k}}

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

private
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
      open import Relation.Binary.PropositionalEquality using (sym; trans; cong)

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

-- | The two fields, named so the encoder and its bound can both refer to them.
-- Fields by construction: the exponent is clamped into `exp-bits` and the
-- significand truncated to `sig-bits`. Truncation is where a value too precise
-- for the format would lose information — which is exactly what plan 0.71's F4
-- forbids at the SOURCE, so no accepted literal reaches it.
expField : FloatFormat → Dyadic → ℕ
expField F (m /2^ _) = modPow (bias F + m) (exp-bits F)

sigField : FloatFormat → Dyadic → ℕ
sigField F (_ /2^ e) = modPow e (sig-bits F)

-- | The IEEE-754 bit pattern of a dyadic value at a format.
encode : FloatFormat → Dyadic → ℕ
encode F d = expField F d * (2 ^ sig-bits F) + sigField F d

-- | …and its RANGE, which is the point: a theorem, where `float-bits` (as it was) needed a
-- parameter (`LitFits.float-fits`) because the standard library states no bound
-- on `primFloatToWord`.
encode-fits : ∀ F d → encode F d < 2 ^ (exp-bits F + sig-bits F)
encode-fits F (m /2^ e) =
  combine-bound (exp-bits F) (sig-bits F)
                (modPow< (bias F + m) (exp-bits F))
                (modPow< e (sig-bits F))
