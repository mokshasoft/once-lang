-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Float.EncodingLaws.Neg — negation on words is negation on values.
--
-- `Float.Word.fneg` flips the sign bit (bit `e + s`) and leaves the stored
-- exponent and fraction alone, whatever the word; `decode` reads those three
-- fields, and a decoded value with the other sign is its negation
-- (`decodeAt-neg`). So `decode (fneg w) ≡ negV (decode w)` for EVERY word,
-- canonical or not.
------------------------------------------------------------------------

module Once.Float.EncodingLaws.Neg where

open import Data.Nat as ℕ
  using (ℕ; zero; suc; _+_; _*_; _∸_; _^_; _<_; _≤_; s≤s; z≤n; NonZero)
open import Data.Nat.Properties as ℕP
  using (≤-trans; <-≤-trans; ≤-reflexive; m^n≢0; ^-distribˡ-+-*; +-comm; +-assoc; +-identityʳ;
         ≤ᵇ⇒≤; ≤⇒≤ᵇ; <⇒≱; ≮⇒≥; m∸n+n≡m; +-monoˡ-<; m≤n+m; n≤1+n)
open import Data.Nat.DivMod
  using (_/_; _%_; m<n⇒m%n≡m; m<n⇒m/n≡0; [m+n]%n≡m%n; [m+kn]%n≡m%n; m≤n⇒[n∸m]%m≡n%m;
         m≡m%n+[m/n]*n; m%n<n; m∣n⇒o%n%m≡o%m; m/n≡1+[m∸n]/n; n/n≡1)
open import Data.Nat.Divisibility using (_∣_; divides)
open import Data.Bool using (Bool; true; false; T)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

import Data.Integer as ℤ
open import Once.Spec.Float.Dyadic using (FloatFormat; modPow; bias)
open Once.Spec.Float.Dyadic.FloatFormat using (exp-bits; sig-bits)
open import Once.Spec.Float.Value using (Sign; pos; neg; flip; FloatVal; fv-zero; fv-num; fv-inf; fv-nan; negV;
  canon; canonAt)
open import Once.Spec.Float.Encoding using (signWeight; signOf; decodeMax; decodeAt; decode)
open import Once.Float.Word using (fneg; fnegAt)

------------------------------------------------------------------------
-- Negating a decoded value: the same fields, the other sign
------------------------------------------------------------------------

canon-neg : ∀ fuel s m e → negV (canon fuel s m e) ≡ canon fuel (flip s) m e
canonAt-neg : ∀ fuel s m e b → negV (canonAt fuel s m e b) ≡ canonAt fuel (flip s) m e b
canon-neg fuel    s zero    e = refl
canon-neg zero    s (suc m) e = refl
canon-neg (suc f) s (suc m) e = canonAt-neg f s (suc m) e ((suc m % 2) ℕ.≡ᵇ 1)
canonAt-neg f s m e true  = refl
canonAt-neg f s m e false = canon-neg f s (m / 2) (e ℤ.+ ℤ.+ 1)

decodeAt-neg : ∀ F s se f b₁ b₂ → negV (decodeAt F s se f b₁ b₂) ≡ decodeAt F (flip s) se f b₁ b₂
decodeAt-neg F s se f true  _     = canon-neg f s f _
decodeAt-neg F s se f false true  = max-neg f
  where
    max-neg : ∀ f → negV (decodeMax s f) ≡ decodeMax (flip s) f
    max-neg zero    = refl
    max-neg (suc _) = refl
decodeAt-neg F s se f false false =
  canon-neg (2 ^ sig-bits F + f) s (2 ^ sig-bits F + f) ((ℤ.+ se) ℤ.- (ℤ.+ (bias F + sig-bits F)))

------------------------------------------------------------------------
-- The sign bit
------------------------------------------------------------------------

private
  -- W = 2^(e+s), the sign bit's weight; 2W the width's modulus.
  2W≡ : ∀ K → 2 ^ suc K ≡ 2 ^ K + 2 ^ K
  2W≡ K = cong (2 ^ K +_) (+-identityʳ (2 ^ K))

  -- A residue below `2W` has sign bit `x / W`, 0 or 1.
  bit0 : ∀ K x → x < 2 ^ K → (_/_ x (2 ^ K) {{m^n≢0 2 K}}) ≡ 0
  bit0 K x x< = m<n⇒m/n≡0 {{m^n≢0 2 K}} x<

  bit1 : ∀ K x → 2 ^ K ≤ x → x < 2 ^ suc K → (_/_ x (2 ^ K) {{m^n≢0 2 K}}) ≡ 1
  bit1 K x W≤ x< =
    trans (m/n≡1+[m∸n]/n {{m^n≢0 2 K}} W≤)
          (cong suc (m<n⇒m/n≡0 {{m^n≢0 2 K}} (∸-lt K x W≤ x<)))
    where
      ∸-lt : ∀ K x → 2 ^ K ≤ x → x < 2 ^ suc K → x ∸ 2 ^ K < 2 ^ K
      ∸-lt K x W≤ x< = ℕP.m<n+o⇒m∸n<o x (2 ^ K) {{m^n≢0 2 K}} (subst (x <_) (2W≡ K) x<)

  -- The residue mod 2W of `w`, and the quotient: `w ≡ x + q * 2W`.
  split : ∀ K w → w ≡ (_%_ w (2 ^ suc K) {{m^n≢0 2 (suc K)}}) + (_/_ w (2 ^ suc K) {{m^n≢0 2 (suc K)}}) * 2 ^ suc K
  split K w = m≡m%n+[m/n]*n w (2 ^ suc K) {{m^n≢0 2 (suc K)}}


  module NS where
    open import Data.Nat.Tactic.RingSolver using (solve-∀)

    borrow : ∀ x W r → x + ((W + W) + r) ≡ ((x + W) + r) + W
    borrow = solve-∀

------------------------------------------------------------------------
-- The flip, on the fields
------------------------------------------------------------------------

module _ (F : FloatFormat) where
  private
    K = exp-bits F + sig-bits F
    W = 2 ^ K
    W2 = 2 ^ suc K
    instance
      nzW  : NonZero W
      nzW  = m^n≢0 2 K
      nz2W : NonZero W2
      nz2W = m^n≢0 2 (suc K)
      nzS  : NonZero (2 ^ sig-bits F)
      nzS  = m^n≢0 2 (sig-bits F)

    W2≡ : W2 ≡ W + W
    W2≡ = 2W≡ K

    W≤W2 : W ≤ W2
    W≤W2 = subst (W ≤_) (sym W2≡) (ℕP.m≤m+n W W)

    T≤ : ∀ {w} → (W ℕ.≤ᵇ w) ≡ true → W ≤ w
    T≤ {w} e = ≤ᵇ⇒≤ W w (subst T (sym e) _)

    F> : ∀ {w} → (W ℕ.≤ᵇ w) ≡ false → w < W
    F> {w} e = ℕP.≰⇒> (λ le → subst T e (≤⇒≤ᵇ le))

    -- | The exponent and fraction fields (below bit `K`) are unchanged.
    low-at : ∀ w b → (W ℕ.≤ᵇ w) ≡ b → fnegAt F w b % W ≡ w % W
    low-at w true  e = m≤n⇒[n∸m]%m≡n%m (T≤ e)
    low-at w false e = [m+n]%n≡m%n w W

    s∣W : 2 ^ sig-bits F ∣ W
    s∣W = divides (2 ^ exp-bits F) (^-distribˡ-+-* 2 (exp-bits F) (sig-bits F))

    -- a residue below `W2` and the sign bit it has
    mod-small : ∀ y → y < W2 → y % W2 ≡ y
    mod-small y y< = m<n⇒m%n≡m y<

    flip-pos : ∀ x → x < W → signOf (x / W) ≡ pos
    flip-pos x x< rewrite bit0 K x x< = refl

    flip-neg : ∀ x → W ≤ x → x < W2 → signOf (x / W) ≡ neg
    flip-neg x W≤ x< rewrite bit1 K x W≤ x< = refl

    -- | The sign bit is flipped.
    sign-at : ∀ w b → (W ℕ.≤ᵇ w) ≡ b
            → signOf ((fnegAt F w b % W2) / W) ≡ flip (signOf ((w % W2) / W))
    sign-at w false e
      rewrite mod-small (w + W) (subst (w + W <_) (sym W2≡) (+-monoˡ-< W (F> e)))
            | mod-small w (<-≤-trans (F> e) W≤W2)
            | flip-neg (w + W) (m≤n+m W w) (subst (w + W <_) (sym W2≡) (+-monoˡ-< W (F> e)))
            | flip-pos w (F> e) = refl
    sign-at w true e = by (W ℕ.≤? x) (split K w)
      where
        x = w % W2
        q = w / W2
        x< : x < W2
        x< = m%n<n w W2
        by : Dec (W ≤ x) → w ≡ x + q * W2
           → signOf (((w ∸ W) % W2) / W) ≡ flip (signOf (x / W))
        by (yes W≤x) ew =
          trans (cong (λ z → signOf (((z ∸ W) % W2) / W)) ew)
            (trans (cong (λ z → signOf ((z % W2) / W)) (ℕP.+-∸-comm (q * W2) W≤x))
              (trans (cong (λ z → signOf (z / W)) (trans ([m+kn]%n≡m%n (x ∸ W) q W2) (mod-small (x ∸ W) (<-≤-trans x∸W< W≤W2))))
                (trans (flip-pos (x ∸ W) x∸W<) (cong flip (sym (flip-neg x W≤x x<))))))
          where
            x∸W< : x ∸ W < W
            x∸W< = ℕP.m<n+o⇒m∸n<o x W (subst (x <_) W2≡ x<)
        by (no x≱W) ew = go q refl
          where
            x<W : x < W
            x<W = ℕP.≰⇒> x≱W
            x+W< : x + W < W2
            x+W< = subst (x + W <_) (sym W2≡) (+-monoˡ-< W x<W)
            go : ∀ q′ → q ≡ q′ → signOf (((w ∸ W) % W2) / W) ≡ flip (signOf (x / W))
            go zero    eq = ⊥-elim (ℕP.<⇒≱ (subst (_< W) (sym (trans ew (cong (λ z → x + z * W2) eq) ⟨trans⟩ ℕP.+-identityʳ x)) x<W) (T≤ e))
              where
                _⟨trans⟩_ : ∀ {a b c : ℕ} → a ≡ b → b ≡ c → a ≡ c
                _⟨trans⟩_ = trans
            go (suc r) eq =
              trans (cong (λ z → signOf (((z ∸ W) % W2) / W)) (trans ew (cong (λ z → x + z * W2) eq)))
                (trans (cong (λ z → signOf (((z ∸ W) % W2) / W)) (expand r))
                  (trans (cong (λ z → signOf ((z % W2) / W)) (ℕP.m+n∸n≡m ((x + W) + r * W2) W))
                    (trans (cong (λ z → signOf (z / W)) (trans ([m+kn]%n≡m%n (x + W) r W2) (mod-small (x + W) x+W<)))
                      (trans (flip-neg (x + W) (m≤n+m W x) x+W<) (cong flip (sym (flip-pos x x<W)))))))
              where
                expand : ∀ r → x + suc r * W2 ≡ ((x + W) + r * W2) + W
                expand r = trans (cong (λ z → x + (z + r * W2)) W2≡) (NS.borrow x W (r * W2))

  -- | The fields `decode` reads of `fneg F w`: the same exponent and
  -- fraction, the other sign.
  fneg-low : ∀ w → modPow (fneg F w) K ≡ modPow w K
  fneg-low w = low-at w _ refl

  fneg-frac : ∀ w → modPow (fneg F w) (sig-bits F) ≡ modPow w (sig-bits F)
  fneg-frac w = trans (sym (m∣n⇒o%n%m≡o%m (2 ^ sig-bits F) W (fneg F w) s∣W))
                  (trans (cong (_% 2 ^ sig-bits F) (fneg-low w)) (m∣n⇒o%n%m≡o%m (2 ^ sig-bits F) W w s∣W))

  fneg-sign : ∀ w → signOf (modPow (fneg F w) (suc K) / signWeight F) ≡ flip (signOf (modPow w (suc K) / signWeight F))
  fneg-sign w = sign-at w _ refl

  private
    dA-cong : ∀ {s₁ s₂ e₁ e₂ f₁ f₂} → s₁ ≡ s₂ → e₁ ≡ e₂ → f₁ ≡ f₂
            → decodeAt F s₁ e₁ f₁ (e₁ ℕ.≡ᵇ 0) (e₁ ℕ.≡ᵇ ((2 ^ exp-bits F) ∸ 1))
              ≡ decodeAt F s₂ e₂ f₂ (e₂ ℕ.≡ᵇ 0) (e₂ ℕ.≡ᵇ ((2 ^ exp-bits F) ∸ 1))
    dA-cong refl refl refl = refl

  -- | Negation on words is negation on values, at every word.
  decode-fneg : ∀ w → decode F (fneg F w) ≡ negV (decode F w)
  decode-fneg w =
    trans (dA-cong (fneg-sign w) (cong (_/ 2 ^ sig-bits F) (fneg-low w)) (fneg-frac w))
          (sym (decodeAt-neg F (signOf (modPow w (suc K) / signWeight F)) (modPow w K / 2 ^ sig-bits F) (modPow w (sig-bits F))
                  (modPow w K / 2 ^ sig-bits F ℕ.≡ᵇ 0) (modPow w K / 2 ^ sig-bits F ℕ.≡ᵇ ((2 ^ exp-bits F) ∸ 1))))
