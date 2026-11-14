-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Float.EncodingLaws — the IEEE 754 encoding of level-2 values.
--
-- `InRange F v` says structurally that `v` is a value of the format `F`: an
-- exponent at least the subnormal quantum, an odd significand of at most `p`
-- bits, and a magnitude below `2^(emax + 1)`. This module proves that
--
--   * rounding lands in range (`roundQ-inRange`, `roundDec-inRange`), and
--     so does every value that fits (`fits-inRange`);
--   * a value in range is one that fits (`inRange-fits`), so `fitV` is
--     idempotent (`fitV-idem`);
--   * the encoding of a value in range fits the format's width
--     (`encode-fits`, `round-fits`);
--   * decoding inverts encoding on values in range (`decode-encode`); a
--     format has an exponent bit and a fraction bit (`FloatFormat`).
------------------------------------------------------------------------

module Once.Float.EncodingLaws where

open import Data.Nat as ℕ
  using (ℕ; zero; suc; _+_; _*_; _∸_; _^_; _<_; _≤_; s≤s; z≤n; s≤s⁻¹)
open import Data.Nat.Properties as ℕP
  using ( ≤-refl; ≤-trans; <-≤-trans; ≤-<-trans; ≤-reflexive; <⇒≢; +-identityʳ; +-comm
        ; *-identityʳ; *-monoˡ-≤; *-monoˡ-<; *-cancelˡ-≤; ^-distribˡ-+-*; ^-monoʳ-≤
        ; ^-monoʳ-<; m^n>0; m^n≢0; m+[n∸m]≡n; m∸n≤m; ∸-monoˡ-≤; suc-injective)
open import Data.Nat.DivMod using (_/_; _%_; n/1≡n; n%1≡0)
import Data.Integer as ℤ
open import Data.Integer using (ℤ; +_; -[1+_])
import Data.Integer.Properties as ℤP
open import Data.Bool using (Bool; true; false; T)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

open import Once.Spec.Float.Dyadic using (FloatFormat; bias; bitLen; binary32; binary64)
open Once.Spec.Float.Dyadic.FloatFormat using (exp-bits; sig-bits)
open import Once.Spec.Float.Value
  using ( Sign; pos; neg; FloatVal; fv-zero; fv-num; fv-inf; fv-nan; odd
        ; qmin; quantum; overflows; canon; finish; finishAt; roundAt; roundQ
        ; roundHalfEven; divRHE; lg; lgAt; atLeast; scaleRHE; fitV; Fits)
open import Once.Spec.Float.Decimal using (Decimal; _/10^_; roundDec)
open import Once.Spec.Float.Encoding
  using ( signBitOf; signWeight; maxExpField; zeroW; infW; nanW; normalW; subnormalW
        ; numAt; encode; decodeMax; decodeAt; decode)
import Once.Float.Word as Word
import Once.Spec.Float.Arith as FA

open import Once.Float.DyadicLaws using (combine-bound)
open import Once.Metatheory.Float.Nat
  using (bitLen-upper; bitLen-lower; bitLen-≤; bitLen-pos; bitLen-shift; odd-pow-<)
open import Once.Metatheory.Float.Canon using (canon-spec; canon-odd)
open import Once.Metatheory.Float.Scale using (scaled-≤)
open import Once.Float.EncodingLaws.Fields using (decode-fields)

open import Once.Metatheory.Float.Range

private
  -- A packed word fits the format's width.
  packed-fits : ∀ F s se f → se < 2 ^ exp-bits F → f < 2 ^ sig-bits F →
    signBitOf s * signWeight F + se * 2 ^ sig-bits F + f < 2 ^ (1 + (exp-bits F + sig-bits F))
  packed-fits F s se f se< f< =
    subst (_< 2 ^ (1 + (exp-bits F + sig-bits F)))
      (sym (ℕP.+-assoc (signBitOf s * signWeight F) (se * 2 ^ sig-bits F) f))
      (combine-bound 1 (exp-bits F + sig-bits F) (sign<2 s)
        (combine-bound (exp-bits F) (sig-bits F) se< f<))

  sign-fits : ∀ F s → signBitOf s * signWeight F < 2 ^ (1 + (exp-bits F + sig-bits F))
  sign-fits F s =
    subst (_< 2 ^ (1 + (exp-bits F + sig-bits F))) (+-identityʳ _)
      (combine-bound 1 (exp-bits F + sig-bits F) (sign<2 s) (m^n>0 2 (exp-bits F + sig-bits F)))

  repack : ∀ a f → a + f ≡ a + 0 + f
  repack a f = cong (_+ f) (sym (+-identityʳ a))


------------------------------------------------------------------------
-- encode-fits
------------------------------------------------------------------------

private
  subnormal-fits : ∀ F s M y → (∀ j → y ≡ + j → M * 2 ^ j < 2 ^ sig-bits F)
                 → subnormalW F s M y < 2 ^ (1 + (exp-bits F + sig-bits F))
  subnormal-fits F s M (+ j) h =
    subst (_< 2 ^ (1 + (exp-bits F + sig-bits F))) (sym (repack (signBitOf s * signWeight F) (M * 2 ^ j)))
      (packed-fits F s 0 (M * 2 ^ j) (m^n>0 2 (exp-bits F)) (h j refl))
  subnormal-fits F s M -[1+ _ ] h = sign-fits F s

  num-fits : ∀ F s m e L′ → bitLen (odd m) ≡ suc L′
           → L′ + (suc (sig-bits F) ∸ bitLen (odd m)) ≡ sig-bits F
           → e ℤ.+ + suc L′ ℤ.≤ + (bias F + 1)
           → ∀ z → z ≡ e ℤ.+ + (L′ + bias F)
           → numAt F s (odd m) e z < 2 ^ (1 + (exp-bits F + sig-bits F))
  num-fits F s m e L′ hL hr h3 (+ suc k) hz =
    packed-fits F s (suc k) frac (≤-<-trans (se≤ e k hz h3) (bb<pow (exp-bits F))) frac<
    where open Normal F m L′ hL hr
  num-fits F s m e L′ hL hr h3 (+ zero) hz =
    subnormal-fits F s (odd m) (e ℤ.- qmin F) (λ j hj → sub-bound F m e L′ (+ 0) j hL hz ℤP.≤-refl hj)
  num-fits F s m e L′ hL hr h3 -[1+ x ] hz =
    subnormal-fits F s (odd m) (e ℤ.- qmin F) (λ j hj → sub-bound F m e L′ -[1+ x ] j hL hz ℤ.-≤+ hj)

  nan-mag : ∀ F → nanW F ≤ 2 ^ (exp-bits F + sig-bits F)
  nan-mag F with pos-suc (m^n>0 2 (exp-bits F))
  ... | y , eq =
    ≤-trans (ℕP.+-monoʳ-≤ (maxExpField F) (^-monoʳ-≤ 2 (m∸n≤m (sig-bits F) 1)))
      (≤-reflexive (trans (cong (λ x → (x ∸ 1) * 2 ^ sig-bits F + 2 ^ sig-bits F) eq)
                     (trans (+-comm (y * 2 ^ sig-bits F) (2 ^ sig-bits F))
                       (trans (cong (_* 2 ^ sig-bits F) (sym eq))
                              (sym (^-distribˡ-+-* 2 (exp-bits F) (sig-bits F)))))))

-- | The encoding of a value in range fits the format's width.
encode-fits : ∀ F v → InRange F v → encode F v < 2 ^ (1 + (exp-bits F + sig-bits F))
encode-fits F (fv-zero s) _ = sign-fits F s
encode-fits F (fv-num s m e) (_ , m< , h3) with shape F m m<
... | L′ , hL , hr =
  num-fits F s m e L′ hL hr (subst (λ x → e ℤ.+ + x ℤ.≤ + (bias F + 1)) hL h3) _
    (cong (λ x → e ℤ.+ + (x ∸ 1 + bias F)) hL)
encode-fits F (fv-inf s) _ =
  subst (_< 2 ^ (1 + (exp-bits F + sig-bits F))) (+-identityʳ (infW F s))
    (packed-fits F s (2 ^ exp-bits F ∸ 1) 0 (pred< (m^n>0 2 (exp-bits F))) (m^n>0 2 (sig-bits F)))
encode-fits F fv-nan _ =
  ≤-<-trans (nan-mag F) (^-monoʳ-< 2 (s≤s (s≤s z≤n)) (≤-refl {suc (exp-bits F + sig-bits F)}))

round-fits : ∀ F d → Word.round F d < 2 ^ (1 + (exp-bits F + sig-bits F))
round-fits F d = encode-fits F (roundDec F d) (roundDec-inRange F d)

------------------------------------------------------------------------
-- decode-encode
------------------------------------------------------------------------

private
  decodeMax-pos : ∀ s x → 0 < x → decodeMax s x ≡ fv-nan
  decodeMax-pos s (suc x) _ = refl

  nan-frac< : ∀ sb → 1 ≤ sb → 2 ^ (sb ∸ 1) < 2 ^ sb
  nan-frac< (suc sb) _ = ^-monoʳ-< 2 (s≤s (s≤s z≤n)) (≤-refl {suc sb})

  subnormal-dec : ∀ F s m e y → + 0 ℤ.≤ y
    → (∀ j → y ≡ + j → odd m * 2 ^ j < 2 ^ sig-bits F)
    → (∀ j → y ≡ + j → qmin F ℤ.+ + j ≡ e)
    → decode F (subnormalW F s (odd m) y) ≡ fv-num s m e
  subnormal-dec F s m e (+ j) _ hb he =
    trans (cong (decode F) (repack (signBitOf s * signWeight F) (odd m * 2 ^ j)))
      (trans (decode-fields F s 0 (odd m * 2 ^ j) (m^n>0 2 (exp-bits F)) (hb j refl))
        (trans (canon-odd s m j (qmin F)) (cong (fv-num s m) (he j refl))))

  num-dec : ∀ F → ValidFormat F → ∀ s m e L′ → bitLen (odd m) ≡ suc L′
          → L′ + (suc (sig-bits F) ∸ bitLen (odd m)) ≡ sig-bits F
          → qmin F ℤ.≤ e → e ℤ.+ + suc L′ ℤ.≤ + (bias F + 1)
          → ∀ z → z ≡ e ℤ.+ + (L′ + bias F)
          → decode F (numAt F s (odd m) e z) ≡ fv-num s m e
  num-dec F vf s m e L′ hL hr h1 h3 (+ suc k) hz =
    trans (decode-fields F s (suc k) frac (≤-<-trans sk≤ (bb<pow (exp-bits F))) frac<)
      (trans (cong (decodeAt F s (suc k) frac false)
                   (≡ᵇ-false (<⇒≢ (≤-<-trans sk≤ (bb<max (exp-bits F) (ValidFormat.exp-pos vf))))))
        (trans (cong (λ x → canon x s x (+ suc k ℤ.- + (bias F + sig-bits F))) frac-back)
          (trans (canon-odd s m r (+ suc k ℤ.- + (bias F + sig-bits F)))
            (cong (fv-num s m) exp≡))))
    where
      open Normal F m L′ hL hr
      sk≤ = se≤ e k hz h3
      exp≡ : (+ suc k ℤ.- + (bias F + sig-bits F)) ℤ.+ + r ≡ e
      exp≡ = trans (cong (λ x → (x ℤ.- + (bias F + sig-bits F)) ℤ.+ + r) hz)
               (trans (cong (λ t → ((e ℤ.+ + (L′ + bias F)) ℤ.- + (bias F + t)) ℤ.+ + r) (sym hr))
                      (ZS.back-normal e (+ L′) (+ bias F) (+ r)))
  num-dec F vf s m e L′ hL hr h1 h3 (+ zero) hz =
    subnormal-dec F s m e (e ℤ.- qmin F) (ℤP.i≤j⇒0≤j-i h1)
      (λ j hj → sub-bound F m e L′ (+ 0) j hL hz ℤP.≤-refl hj)
      (λ j hj → trans (cong (λ x → qmin F ℤ.+ x) (sym hj)) (ZS.back-sub e (qmin F)))
  num-dec F vf s m e L′ hL hr h1 h3 -[1+ x ] hz =
    subnormal-dec F s m e (e ℤ.- qmin F) (ℤP.i≤j⇒0≤j-i h1)
      (λ j hj → sub-bound F m e L′ -[1+ x ] j hL hz ℤ.-≤+ hj)
      (λ j hj → trans (cong (λ x → qmin F ℤ.+ x) (sym hj)) (ZS.back-sub e (qmin F)))

-- | Decoding inverts encoding on values in range.
decode-encode-at : ∀ F → ValidFormat F → ∀ v → InRange F v → decode F (encode F v) ≡ v
decode-encode-at F vf (fv-zero s) _ =
  trans (cong (decode F) (sym (trans (+-identityʳ (signBitOf s * signWeight F + 0))
                                     (+-identityʳ (signBitOf s * signWeight F)))))
        (decode-fields F s 0 0 (m^n>0 2 (exp-bits F)) (m^n>0 2 (sig-bits F)))
decode-encode-at F vf (fv-num s m e) (h1 , m< , h3) with shape F m m<
... | L′ , hL , hr =
  num-dec F vf s m e L′ hL hr h1 (subst (λ x → e ℤ.+ + x ℤ.≤ + (bias F + 1)) hL h3) _
    (cong (λ x → e ℤ.+ + (x ∸ 1 + bias F)) hL)
decode-encode-at F vf (fv-inf s) _ =
  trans (cong (decode F) (sym (+-identityʳ (infW F s))))
    (trans (decode-fields F s (2 ^ exp-bits F ∸ 1) 0 (pred< (m^n>0 2 (exp-bits F))) (m^n>0 2 (sig-bits F)))
      (cong₂ (decodeAt F s (2 ^ exp-bits F ∸ 1) 0)
             (≡ᵇ-false (max≢0 (exp-bits F) (ValidFormat.exp-pos vf)))
             (≡ᵇ-refl (2 ^ exp-bits F ∸ 1))))
decode-encode-at F vf fv-nan _ =
  trans (decode-fields F pos (2 ^ exp-bits F ∸ 1) (2 ^ (sig-bits F ∸ 1))
           (pred< (m^n>0 2 (exp-bits F))) (nan-frac< (sig-bits F) (ValidFormat.sig-pos vf)))
    (trans (cong₂ (decodeAt F pos (2 ^ exp-bits F ∸ 1) (2 ^ (sig-bits F ∸ 1)))
                  (≡ᵇ-false (max≢0 (exp-bits F) (ValidFormat.exp-pos vf)))
                  (≡ᵇ-refl (2 ^ exp-bits F ∸ 1)))
           (decodeMax-pos pos (2 ^ (sig-bits F ∸ 1)) (m^n>0 2 (sig-bits F ∸ 1))))

-- | Decoding inverts encoding on the values of a format.
decode-encode : ∀ F v → InRange F v → decode F (encode F v) ≡ v
decode-encode F = decode-encode-at F (valid F)


-- | Negation on words is negation on values (`EncodingLaws.Neg`).
open import Once.Float.EncodingLaws.Neg public using (decode-fneg)
