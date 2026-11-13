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
--   * decoding inverts encoding on values in range (`decode-encode`), for a
--     format with at least one exponent bit and one fraction bit
--     (`ValidFormat`).
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

open import Once.Float.DyadicLaws using (combine-bound)
open import Once.Float.EncodingLaws.Nat
  using (bitLen-upper; bitLen-lower; bitLen-≤; bitLen-pos; bitLen-shift; odd-pow-<)
open import Once.Float.EncodingLaws.Canon using (canon-spec; canon-odd)
open import Once.Float.EncodingLaws.Scale using (scaled-≤)
open import Once.Float.EncodingLaws.Fields using (decode-fields)

------------------------------------------------------------------------
-- The range, and the formats the laws need
------------------------------------------------------------------------

-- | A value of the format `F`, structurally: in the normal or subnormal range.
InRange : FloatFormat → FloatVal → Set
InRange F (fv-zero _)    = ⊤
InRange F (fv-num s m e) =
  (qmin F ℤ.≤ e) × (odd m < 2 ^ suc (sig-bits F))
    × (e ℤ.+ (+ bitLen (odd m)) ℤ.≤ (+ (bias F + 1)))
InRange F (fv-inf _)     = ⊤
InRange F fv-nan         = ⊤

-- | A format with an exponent bit (so the all-ones exponent is not the zero
-- exponent) and a fraction bit (so the canonical NaN's quiet bit exists).
record ValidFormat (F : FloatFormat) : Set where
  field
    exp-pos : 1 ≤ exp-bits F
    sig-pos : 1 ≤ sig-bits F

valid-binary32 : ValidFormat binary32
valid-binary32 = record { exp-pos = s≤s z≤n ; sig-pos = s≤s z≤n }

valid-binary64 : ValidFormat binary64
valid-binary64 = record { exp-pos = s≤s z≤n ; sig-pos = s≤s z≤n }

------------------------------------------------------------------------
-- Small facts
------------------------------------------------------------------------

private
  module ZS where
    open import Data.Integer.Tactic.RingSolver using (solve-∀)

    nrm : ∀ e L b → (e ℤ.+ (+ 1 ℤ.+ L)) ℤ.+ b ≡ + 1 ℤ.+ (e ℤ.+ (L ℤ.+ b))
    nrm = solve-∀

    nrm-rhs : ∀ b → (b ℤ.+ + 1) ℤ.+ b ≡ + 1 ℤ.+ (b ℤ.+ b)
    nrm-rhs = solve-∀

    sub : ∀ e L b s → (e ℤ.- (+ 1 ℤ.- (b ℤ.+ s))) ℤ.+ (+ 1 ℤ.+ L) ≡ (e ℤ.+ (L ℤ.+ b)) ℤ.+ s
    sub = solve-∀

    back-normal : ∀ e L b r → ((e ℤ.+ (L ℤ.+ b)) ℤ.- (b ℤ.+ (L ℤ.+ r))) ℤ.+ r ≡ e
    back-normal = solve-∀

    back-sub : ∀ e q → q ℤ.+ (e ℤ.- q) ≡ e
    back-sub = solve-∀

    fin : ∀ q k L → (q ℤ.+ k) ℤ.+ L ≡ (L ℤ.+ k) ℤ.+ q
    fin = solve-∀

    lg-eq : ∀ L → (+ 1 ℤ.+ L) ℤ.- + 1 ≡ L
    lg-eq = solve-∀

    assoc-sub : ∀ e L s → (e ℤ.+ L) ℤ.- s ≡ e ℤ.+ (L ℤ.- s)
    assoc-sub = solve-∀

    exact : ∀ L e q → (L ℤ.+ (e ℤ.- q)) ℤ.+ q ≡ L ℤ.+ e
    exact = solve-∀

    comm : ∀ a b → a ℤ.+ b ≡ b ℤ.+ a
    comm = solve-∀

  pos-suc : ∀ {n} → 0 < n → Σ ℕ λ n′ → n ≡ suc n′
  pos-suc (s≤s _) = _ , refl

  T→true : ∀ {b} → T b → b ≡ true
  T→true {true} _ = refl

  ¬T→false : ∀ {b} → ¬ T b → b ≡ false
  ¬T→false {true}  ¬t = ⊥-elim (¬t tt)
  ¬T→false {false} _  = refl

  ≡ᵇ-false : ∀ {m n} → m ≢ n → (m ℕ.≡ᵇ n) ≡ false
  ≡ᵇ-false {m} {n} ne = ¬T→false (λ t → ne (ℕP.≡ᵇ⇒≡ m n t))

  ≡ᵇ-refl : ∀ n → (n ℕ.≡ᵇ n) ≡ true
  ≡ᵇ-refl n = T→true (ℕP.≡⇒≡ᵇ n n refl)

  sign<2 : ∀ s → signBitOf s < 2
  sign<2 pos = s≤s z≤n
  sign<2 neg = s≤s (s≤s z≤n)

  pred< : ∀ {n} → 0 < n → n ∸ 1 < n
  pred< (s≤s {n = n} _) = ≤-refl

  -- The bias of an `es`-bit exponent.
  B : ℕ → ℕ
  B es = 2 ^ (es ∸ 1) ∸ 1

  bias-split : ∀ k y → 2 ^ k ≡ suc y → (B (suc k) + B (suc k) ≡ y + y) × (2 ^ suc k ∸ 1 ≡ suc (y + y))
  bias-split k y eq =
    cong (λ x → (x ∸ 1) + (x ∸ 1)) eq ,
    trans (cong (λ x → 2 * x ∸ 1) eq) (trans (ℕP.+-suc y (y + 0)) (cong (λ x → suc (y + x)) (+-identityʳ y)))

  -- `2 · bias` is below every exponent field.
  bb<pow : ∀ es → B es + B es < 2 ^ es
  bb<pow zero    = s≤s z≤n
  bb<pow (suc k) with pos-suc (m^n>0 2 k)
  ... | y , eq with bias-split k y eq
  ...   | bb , mx = ≤-trans (≤-reflexive (trans (cong suc bb) (sym mx))) (m∸n≤m (2 ^ suc k) 1)

  -- … and, with an exponent bit, below the all-ones exponent.
  bb<max : ∀ es → 1 ≤ es → B es + B es < 2 ^ es ∸ 1
  bb<max (suc k) _ with pos-suc (m^n>0 2 k)
  ... | y , eq with bias-split k y eq
  ...   | bb , mx = subst (B (suc k) + B (suc k) <_) (sym mx) (s≤s (≤-reflexive bb))

  max≢0 : ∀ es → 1 ≤ es → 2 ^ es ∸ 1 ≢ 0
  max≢0 es le eq =
    <⇒≢ (≤-trans (s≤s z≤n) (∸-monoˡ-≤ 1 (^-monoʳ-≤ 2 le))) (sym eq)

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
-- The shape of an in-range significand
------------------------------------------------------------------------

private
  -- `bitLen (odd m) = suc L′` with `L′ + r = sig-bits`, `r` the left shift
  -- `encode` applies to a normal significand.
  shape : ∀ F m → odd m < 2 ^ suc (sig-bits F) →
    Σ ℕ λ L′ → (bitLen (odd m) ≡ suc L′)
             × (L′ + (suc (sig-bits F) ∸ bitLen (odd m)) ≡ sig-bits F)
  shape F m m< with pos-suc (bitLen-pos (odd m) (s≤s z≤n))
  ... | L′ , hL =
    L′ , hL ,
    suc-injective (subst (λ x → x + (suc (sig-bits F) ∸ bitLen (odd m)) ≡ suc (sig-bits F)) hL
                         (m+[n∸m]≡n (bitLen-≤ (odd m) (suc (sig-bits F)) m<)))

  module Normal (F : FloatFormat) (m L′ : ℕ) (hL : bitLen (odd m) ≡ suc L′)
                (hr : L′ + (suc (sig-bits F) ∸ bitLen (odd m)) ≡ sig-bits F) where
    r = suc (sig-bits F) ∸ bitLen (odd m)
    S = 2 ^ sig-bits F

    sh< : odd m * 2 ^ r < 2 * S
    sh< = <-≤-trans (*-monoˡ-< (2 ^ r) {{m^n≢0 2 r}} (subst (λ x → odd m < 2 ^ x) hL (bitLen-upper (odd m))))
            (≤-reflexive (trans (sym (^-distribˡ-+-* 2 (suc L′) r)) (cong (λ x → 2 ^ suc x) hr)))

    sh≥ : S ≤ odd m * 2 ^ r
    sh≥ = ≤-trans (≤-reflexive (trans (cong (2 ^_) (sym hr)) (^-distribˡ-+-* 2 L′ r)))
            (*-monoˡ-≤ (2 ^ r) (*-cancelˡ-≤ {2 ^ L′} {odd m} 2 (subst (λ x → 2 ^ x ≤ 2 * odd m) hL
                                               (bitLen-lower (odd m) (s≤s z≤n)))))

    frac = odd m * 2 ^ r ∸ S

    frac-back : S + frac ≡ odd m * 2 ^ r
    frac-back = m+[n∸m]≡n sh≥

    frac< : frac < S
    frac< = subst (frac <_) (+-identityʳ S)
              (ℕP.+-cancelˡ-< S frac (S + 0) (subst (_< 2 * S) (sym frac-back) sh<))

    -- The stored exponent of a normal number is at most `2 · bias`.
    se≤ : ∀ e k → + suc k ≡ e ℤ.+ + (L′ + bias F) → e ℤ.+ + suc L′ ℤ.≤ + (bias F + 1)
        → suc k ≤ bias F + bias F
    se≤ e k hz h3 =
      s≤s⁻¹ (ℤP.drop‿+≤+
        (subst₂ ℤ._≤_
           (trans (ZS.nrm e (+ L′) (+ bias F)) (cong (λ x → + 1 ℤ.+ x) (sym hz)))
           (ZS.nrm-rhs (+ bias F))
           (ℤP.+-monoˡ-≤ (+ bias F) h3)))
      where open import Relation.Binary.PropositionalEquality using (subst₂)

  -- A subnormal significand at the subnormal quantum fits the fraction.
  sub-bound : ∀ F m e L′ z j → bitLen (odd m) ≡ suc L′ → z ≡ e ℤ.+ + (L′ + bias F) → z ℤ.≤ + 0
            → e ℤ.- qmin F ≡ + j → odd m * 2 ^ j < 2 ^ sig-bits F
  sub-bound F m e L′ z j hL hz z≤0 hj =
    <-≤-trans (*-monoˡ-< (2 ^ j) {{m^n≢0 2 j}} (subst (λ x → odd m < 2 ^ x) hL (bitLen-upper (odd m))))
      (≤-trans (≤-reflexive (sym (^-distribˡ-+-* 2 (suc L′) j)))
               (^-monoʳ-≤ 2 (subst (_≤ sig-bits F) (+-comm j (suc L′)) jL≤)))
    where
      open import Relation.Binary.PropositionalEquality using (subst₂)
      jL≤ : j + suc L′ ≤ sig-bits F
      jL≤ = ℤP.drop‿+≤+
              (subst₂ ℤ._≤_
                 (trans (sym (ZS.sub e (+ L′) (+ bias F) (+ sig-bits F)))
                        (cong (ℤ._+ + suc L′) hj))
                 refl
                 (subst (λ x → x ℤ.+ + sig-bits F ℤ.≤ + sig-bits F) hz
                    (ℤP.+-monoˡ-≤ (+ sig-bits F) z≤0)))

  nonneg : ∀ {q e} → q ℤ.≤ e → e ℤ.- q ≡ + ℤ.∣ e ℤ.- q ∣
  nonneg le = sym (ℤP.0≤i⇒+∣i∣≡i (ℤP.i≤j⇒0≤j-i le))

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

------------------------------------------------------------------------
-- Rounding lands in range
------------------------------------------------------------------------

private
  overflow-false : ∀ F M q → overflows F M q ≡ false → + bitLen M ℤ.+ q ℤ.≤ + (bias F + 1)
  overflow-false F M q eq =
    subst (+ bitLen M ℤ.+ q ℤ.≤_) (sym (ℤP.+-pred (+ bias F) (+ 2)))
      (ℤP.i<j⇒i≤pred[j] {j = + (bias F + 2)} (ℤP.≰⇒> (λ le → subst T eq (ℤP.≤⇒≤ᵇ le))))

  finishAt-inRange : ∀ F s M q b → overflows F M q ≡ b → 0 < M → M ≤ 2 ^ suc (sig-bits F)
                   → qmin F ℤ.≤ q → InRange F (finishAt s M q b)
  finishAt-inRange F s M q true  _  _   _  _   = tt
  finishAt-inRange F s M q false ov M>0 M≤ qle with canon-spec s M q M>0
  ... | m , k , eq , oddk =
    subst (InRange F) (sym eq)
      ( ℤP.≤-trans qle (subst (ℤ._≤ q ℤ.+ + k) (ℤP.+-identityʳ q) (ℤP.+-monoʳ-≤ q (ℤ.+≤+ z≤n)))
      , odd-pow-< m k (sig-bits F) (subst (_≤ 2 ^ suc (sig-bits F)) (sym oddk) M≤)
      , subst (ℤ._≤ + (bias F + 1))
          (sym (trans (ZS.fin q (+ k) (+ bitLen (odd m)))
                      (cong (λ x → + x ℤ.+ q)
                            (trans (sym (bitLen-shift (odd m) k (s≤s z≤n))) (cong bitLen oddk)))))
          (overflow-false F M q ov) )

  finish-inRange : ∀ F s M q → M ≤ 2 ^ suc (sig-bits F) → qmin F ℤ.≤ q → InRange F (finish F s M q)
  finish-inRange F s zero    q _  _   = tt
  finish-inRange F s (suc M) q M≤ qle = finishAt-inRange F s (suc M) q _ refl (s≤s z≤n) M≤ qle

-- | The one rounding lands in range.
roundQ-inRange : ∀ F s n E d → InRange F (roundQ F s n E d)
roundQ-inRange F s zero    E d = tt
roundQ-inRange F s (suc n) E d =
  finish-inRange F s _ _ (scaled-≤ F n d E)
    (ℤP.i≤j⊔i ((E ℤ.+ lg (suc n) (suc d)) ℤ.- + sig-bits F) (qmin F))

-- | A literal's value is in range.
roundDec-inRange : ∀ F d → InRange F (roundDec F d)
roundDec-inRange F ((+ n)    /10^ k) = roundQ-inRange F pos n (+ 0) (10 ^ k ∸ 1)
roundDec-inRange F (-[1+ n ] /10^ k) = roundQ-inRange F neg (suc n) (+ 0) (10 ^ k ∸ 1)

-- | A literal's word fits the format's width.
round-fits : ∀ F d → Word.round F d < 2 ^ (1 + (exp-bits F + sig-bits F))
round-fits F d = encode-fits F (roundDec F d) (roundDec-inRange F d)

-- | A value that fits the format is in range.
fits-inRange : ∀ F v → Fits F v → InRange F v
fits-inRange F (fv-zero s)    _  = tt
fits-inRange F (fv-num s m e) eq = subst (InRange F) eq (roundQ-inRange F s (odd m) e 0)
fits-inRange F (fv-inf s)     _  = tt
fits-inRange F fv-nan         _  = tt

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
decode-encode : ∀ F → ValidFormat F → ∀ v → InRange F v → decode F (encode F v) ≡ v
decode-encode F vf (fv-zero s) _ =
  trans (cong (decode F) (sym (trans (+-identityʳ (signBitOf s * signWeight F + 0))
                                     (+-identityʳ (signBitOf s * signWeight F)))))
        (decode-fields F s 0 0 (m^n>0 2 (exp-bits F)) (m^n>0 2 (sig-bits F)))
decode-encode F vf (fv-num s m e) (h1 , m< , h3) with shape F m m<
... | L′ , hL , hr =
  num-dec F vf s m e L′ hL hr h1 (subst (λ x → e ℤ.+ + x ℤ.≤ + (bias F + 1)) hL h3) _
    (cong (λ x → e ℤ.+ + (x ∸ 1 + bias F)) hL)
decode-encode F vf (fv-inf s) _ =
  trans (cong (decode F) (sym (+-identityʳ (infW F s))))
    (trans (decode-fields F s (2 ^ exp-bits F ∸ 1) 0 (pred< (m^n>0 2 (exp-bits F))) (m^n>0 2 (sig-bits F)))
      (cong₂ (decodeAt F s (2 ^ exp-bits F ∸ 1) 0)
             (≡ᵇ-false (max≢0 (exp-bits F) (ValidFormat.exp-pos vf)))
             (≡ᵇ-refl (2 ^ exp-bits F ∸ 1))))
decode-encode F vf fv-nan _ =
  trans (decode-fields F pos (2 ^ exp-bits F ∸ 1) (2 ^ (sig-bits F ∸ 1))
           (pred< (m^n>0 2 (exp-bits F))) (nan-frac< (sig-bits F) (ValidFormat.sig-pos vf)))
    (trans (cong₂ (decodeAt F pos (2 ^ exp-bits F ∸ 1) (2 ^ (sig-bits F ∸ 1)))
                  (≡ᵇ-false (max≢0 (exp-bits F) (ValidFormat.exp-pos vf)))
                  (≡ᵇ-refl (2 ^ exp-bits F ∸ 1)))
           (decodeMax-pos pos (2 ^ (sig-bits F ∸ 1)) (m^n>0 2 (sig-bits F ∸ 1))))

------------------------------------------------------------------------
-- A value in range fits: rounding it at its own format returns it
------------------------------------------------------------------------

private
  -- With `D = 1` the binade estimate is exact: `lg (odd m) 1 = bitLen − 1`.
  lgAt-exact : ∀ M L′ κ b → atLeast M 1 κ ≡ b → κ ≡ + L′ → 2 ^ L′ ≤ M → lgAt κ b ≡ + L′
  lgAt-exact M L′ κ true  _  κ≡ _  = κ≡
  lgAt-exact M L′ _ false eq refl le =
    ⊥-elim (subst T eq (ℕP.≤⇒≤ᵇ (subst (_≤ M) (sym (ℕP.*-identityˡ (2 ^ L′))) le)))

  lg-exact : ∀ m L′ → bitLen (odd m) ≡ suc L′ → lg (odd m) 1 ≡ + L′
  lg-exact m L′ hL =
    lgAt-exact (odd m) L′ _ _ refl
      (trans (cong (λ x → + x ℤ.- + 1) hL) (ZS.lg-eq (+ L′)))
      (*-cancelˡ-≤ {2 ^ L′} {odd m} 2
        (subst (λ x → 2 ^ x ≤ 2 * odd m) hL (bitLen-lower (odd m) (s≤s z≤n))))

  finish-pos : ∀ F s M q → 0 < M → finish F s M q ≡ finishAt s M q (overflows F M q)
  finish-pos F s (suc M) q _ = refl

  -- At a quantum `q ≤ e` the significand is exact, and the value is kept.
  roundAt-exact : ∀ F s m e q → q ℤ.≤ e → e ℤ.+ + bitLen (odd m) ℤ.≤ + (bias F + 1)
                → roundAt F s (odd m) e 0 q ≡ fv-num s m e
  roundAt-exact F s m e q qle h3 =
    trans (cong (λ y → finish F s (scaleRHE (odd m) 0 y) q) jeq)
      (trans (cong (λ x → finish F s x q) div1)
        (trans (finish-pos F s x q x>0)
          (trans (cong (finishAt s x q) no-ov)
            (trans (canon-odd s m j q)
              (cong (fv-num s m) (trans (cong (λ t → q ℤ.+ t) (sym jeq)) (ZS.back-sub e q)))))))
    where
      j = ℤ.∣ e ℤ.- q ∣
      jeq : e ℤ.- q ≡ + j
      jeq = nonneg qle
      x = odd m * 2 ^ j
      x>0 : 0 < x
      x>0 = <-≤-trans (s≤s z≤n) (ℕP.*-monoʳ-≤ (odd m) (m^n>0 2 j))
      div1 : divRHE x 1 ≡ x
      div1 = cong₂ (λ a b → roundHalfEven a b 1) (n/1≡n x) (n%1≡0 x)
      len : + bitLen x ℤ.+ q ≡ e ℤ.+ + bitLen (odd m)
      len = trans (cong (λ t → + t ℤ.+ q) (bitLen-shift (odd m) j (s≤s z≤n)))
              (trans (cong (λ t → (+ bitLen (odd m) ℤ.+ t) ℤ.+ q) (sym jeq))
                (trans (ZS.exact (+ bitLen (odd m)) e q) (ZS.comm (+ bitLen (odd m)) e)))
      no-ov : overflows F x q ≡ false
      no-ov = ¬T→false λ t →
        two≰one (ℕP.+-cancelˡ-≤ (bias F) 2 1
          (ℤP.drop‿+≤+ (ℤP.≤-trans (ℤP.≤ᵇ⇒≤ t) (subst (ℤ._≤ + (bias F + 1)) (sym len) h3))))
        where
          two≰one : ¬ (2 ≤ 1)
          two≰one (s≤s ())

  quantum-≤ : ∀ F e L′ → L′ ≤ sig-bits F → qmin F ℤ.≤ e → quantum F (e ℤ.+ + L′) ℤ.≤ e
  quantum-≤ F e L′ L′≤ h1 =
    ℤP.⊔-lub
      (subst (ℤ._≤ e) (sym (ZS.assoc-sub e (+ L′) (+ sig-bits F)))
        (subst (e ℤ.+ (+ L′ ℤ.- + sig-bits F) ℤ.≤_) (ℤP.+-identityʳ e)
          (ℤP.+-monoʳ-≤ e (ℤP.i≤j⇒i-j≤0 (ℤ.+≤+ L′≤)))))
      h1

-- | A value in range fits its format.
inRange-fits : ∀ F v → InRange F v → Fits F v
inRange-fits F (fv-zero s) _ = refl
inRange-fits F (fv-num s m e) (h1 , m< , h3) with shape F m m<
... | L′ , hL , hr =
  trans (cong (λ l → roundAt F s (odd m) e 0 (quantum F (e ℤ.+ l))) (lg-exact m L′ hL))
    (roundAt-exact F s m e _
      (quantum-≤ F e L′ (subst (L′ ≤_) hr (ℕP.m≤m+n L′ _)) h1) h3)
inRange-fits F (fv-inf s) _ = refl
inRange-fits F fv-nan     _ = refl

-- | `fitV` lands in range.
fitV-inRange : ∀ F v → InRange F (fitV F v)
fitV-inRange F (fv-zero s)    = tt
fitV-inRange F (fv-num s m e) = roundQ-inRange F s (odd m) e 0
fitV-inRange F (fv-inf s)     = tt
fitV-inRange F fv-nan         = tt

-- | Reading a value at a format twice is reading it once.
fitV-idem : ∀ F v → fitV F (fitV F v) ≡ fitV F v
fitV-idem F v = inRange-fits F (fitV F v) (fitV-inRange F v)
