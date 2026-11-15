-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Float.EncodingLaws.Fields — `decode` reads back the three fields of a
-- word packed as `sign · 2^(e+s) + se · 2^s + f`, with `se < 2^e` and
-- `f < 2^s`.
------------------------------------------------------------------------

module Once.Float.EncodingLaws.Fields where

open import Data.Nat as ℕ
  using (ℕ; zero; suc; _+_; _*_; _∸_; _^_; _<_; _≤_; s≤s; z≤n; NonZero)
open import Data.Nat.Properties as ℕP
  using (≤-trans; <-≤-trans; ≤-reflexive; *-monoˡ-≤; +-monoˡ-<; m^n≢0; ^-distribˡ-+-*; +-identityʳ)
open import Data.Nat.DivMod
  using (_/_; _%_; m<n⇒m%n≡m; m<n⇒m/n≡0; [m+kn]%n≡m%n; +-distrib-/; m*n/n≡m; m*n%n≡0)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Once.Spec.Float.Dyadic using (FloatFormat; modPow)
open Once.Spec.Float.Dyadic.FloatFormat using (exp-bits; sig-bits)
open import Once.Spec.Float.Value using (Sign; pos; neg; FloatVal)
open import Once.Spec.Float.Encoding
  using (signBitOf; signWeight; signOf; decodeAt; decode)
open import Once.Float.DyadicLaws using (combine-bound)

private
  module NS where
    open import Data.Nat.Tactic.RingSolver using (solve-∀)

    rot : ∀ a b c → (a + b) + c ≡ (b + c) + a
    rot = solve-∀

    low : ∀ g E S se f → (g * (E * S) + se * S) + f ≡ f + (g * E + se) * S
    low = solve-∀

  sign<2 : ∀ s → signBitOf s < 2
  sign<2 pos = s≤s z≤n
  sign<2 neg = s≤s (s≤s z≤n)

  signOf-bit : ∀ s → signOf (signBitOf s) ≡ s
  signOf-bit pos = refl
  signOf-bit neg = refl

  -- `x / d ≡ k` for `x = m + k · d` with `m < d`.
  div-split : ∀ m k d .{{_ : NonZero d}} → m < d → (m + k * d) / d ≡ k
  div-split m k d m<d =
    trans (+-distrib-/ m (k * d)
             (subst (_< d) (sym (cong₂ _+_ (m<n⇒m%n≡m m<d) (m*n%n≡0 k d)))
                    (subst (_< d) (sym (+-identityʳ m)) m<d)))
          (cong₂ _+_ (m<n⇒m/n≡0 m<d) (m*n/n≡m k d))

  mod-split : ∀ m k d .{{_ : NonZero d}} → m < d → (m + k * d) % d ≡ m
  mod-split m k d m<d = trans ([m+kn]%n≡m%n m k d) (m<n⇒m%n≡m m<d)

-- | The three fields of a packed word, for any widths `e` and `s`.
module _ (e s g se f : ℕ) (g<2 : g < 2) (se< : se < 2 ^ e) (f< : f < 2 ^ s) where
  private
    W = 2 ^ (e + s)
    S = 2 ^ s
    instance
      nzW : NonZero W
      nzW = m^n≢0 2 (e + s)
      nzS : NonZero S
      nzS = m^n≢0 2 s
    w = g * W + se * S + f
    mag = se * S + f
    mag< : mag < W
    mag< = combine-bound e s se< f<
    w≡ : w ≡ mag + g * W
    w≡ = NS.rot (g * W) (se * S) f

  field-sign : modPow w (suc (e + s)) / W ≡ g
  field-sign =
    trans (cong (_/ W) (m<n⇒m%n≡m {{m^n≢0 2 (suc (e + s))}} w<))
          (trans (cong (_/ W) w≡) (div-split mag g W mag<))
    where
      w< : w < 2 ^ suc (e + s)
      w< = subst (_< 2 ^ suc (e + s)) (sym w≡)
             (<-≤-trans (+-monoˡ-< (g * W) mag<)
                        (ℕP.+-monoʳ-≤ W (*-monoˡ-≤ W (ℕP.≤-pred g<2))))

  field-exp : modPow w (e + s) / S ≡ se
  field-exp =
    trans (cong (_/ S) (trans (cong (_% W) w≡) (mod-split mag g W mag<)))
          (trans (cong (_/ S) (ℕP.+-comm (se * S) f)) (div-split f se S f<))

  field-frac : modPow w s ≡ f
  field-frac =
    trans (cong (_% S) (trans (cong (λ x → g * x + se * S + f) (^-distribˡ-+-* 2 e s))
                              (NS.low g (2 ^ e) S se f)))
          (mod-split f (g * 2 ^ e + se) S f<)

private
  decodeAt-cong : ∀ F {x s y se z f} → x ≡ s → y ≡ se → z ≡ f →
    decodeAt F x y z (y ℕ.≡ᵇ 0) (y ℕ.≡ᵇ ((2 ^ exp-bits F) ∸ 1))
      ≡ decodeAt F s se f (se ℕ.≡ᵇ 0) (se ℕ.≡ᵇ ((2 ^ exp-bits F) ∸ 1))
  decodeAt-cong F refl refl refl = refl

-- | Decoding a packed word dispatches on its fields.
decode-fields : ∀ F s se f → se < 2 ^ exp-bits F → f < 2 ^ sig-bits F →
  decode F (signBitOf s * signWeight F + se * 2 ^ sig-bits F + f)
    ≡ decodeAt F s se f (se ℕ.≡ᵇ 0) (se ℕ.≡ᵇ ((2 ^ exp-bits F) ∸ 1))
decode-fields F s se f se< f< =
  decodeAt-cong F
    (trans (cong signOf (field-sign (exp-bits F) (sig-bits F) (signBitOf s) se f (sign<2 s) se< f<))
           (signOf-bit s))
    (field-exp (exp-bits F) (sig-bits F) (signBitOf s) se f (sign<2 s) se< f<)
    (field-frac (exp-bits F) (sig-bits F) (signBitOf s) se f (sign<2 s) se< f<)
