-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Float.EncodingLaws.Scale — the significand `roundQ` computes is at
-- most `2^p`.
--
-- `Lt N D z` says `N / D < 2^z` for an integer `z`, stated for every way of
-- writing `z` as `a − b`, so no case split on the sign of `z` is needed until
-- the end. `lg` is an upper estimate: `N / D < 2^(lg N D + 1)`; at the quantum
-- `q ≥ E + lg − sig-bits`, the scaled value `N · 2^(E − q) / D` is below
-- `2^p`, and rounding it half to even gives at most `2^p`.
------------------------------------------------------------------------

module Once.Float.EncodingLaws.Scale where

open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _*_; _^_; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties as ℕP
  using (≤-trans; <-≤-trans; ≤-<-trans; ≤-reflexive; *-comm; *-identityʳ
        ; *-monoˡ-≤; *-monoʳ-≤; *-monoˡ-<; ^-distribˡ-+-*; m^n≢0; m≤m*n; ≰⇒>)
import Data.Integer as ℤ
open import Data.Integer using (ℤ; +_; -[1+_])
import Data.Integer.Properties as ℤP
open import Data.Bool using (Bool; true; false; T)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Once.Spec.Float.Dyadic using (FloatFormat; bitLen)
open Once.Spec.Float.Dyadic.FloatFormat using (sig-bits)
open import Once.Spec.Float.Value using (atLeast; lgAt; lg; scaleRHE; quantum; qmin)
open import Once.Float.EncodingLaws.Nat using (bitLen-upper; bitLen-lower; divRHE-≤)

-- | `N / D < 2^z`.
Lt : ℕ → ℕ → ℤ → Set
Lt N D z = ∀ a b → z ℤ.+ + b ≡ + a → N * 2 ^ b < D * 2 ^ a

private
  module ZS where
    open import Data.Integer.Tactic.RingSolver using (solve-∀)

    swap : ∀ z b b′ → (z ℤ.+ b) ℤ.+ b′ ≡ (z ℤ.+ b′) ℤ.+ b
    swap = solve-∀

    mono : ∀ z z′ b′ → z ℤ.+ (b′ ℤ.+ (z′ ℤ.- z)) ≡ z′ ℤ.+ b′
    mono = solve-∀

    true-eq : ∀ bN bD → ((bN ℤ.- bD) ℤ.+ + 1) ℤ.+ bD ≡ + 1 ℤ.+ bN
    true-eq = solve-∀

    false-eq : ∀ k → (k ℤ.- + 1) ℤ.+ + 1 ≡ k
    false-eq = solve-∀

    sub-add : ∀ x y → (x ℤ.- y) ℤ.+ y ≡ x
    sub-add = solve-∀

    room : ∀ E l q s → (+ 1 ℤ.+ s) ℤ.- (E ℤ.- q) ≡ (l ℤ.+ + 1) ℤ.+ (q ℤ.- ((E ℤ.+ l) ℤ.- s))
    room = solve-∀

  module NS where
    open import Data.Nat.Tactic.RingSolver using (solve-∀)

    swap : ∀ N x y → (N * x) * y ≡ (N * y) * x
    swap = solve-∀

    assoc : ∀ D x y → (D * x) * y ≡ D * (x * y)
    assoc = solve-∀

    true-rhs : ∀ D x → x * (2 * D) ≡ D * (2 * x)
    true-rhs = solve-∀

    scale-rhs : ∀ D x y → D * (x * y) ≡ x * (D * y)
    scale-rhs = solve-∀

-- | One instance is enough.
Lt-intro : ∀ N D z a b → z ℤ.+ + b ≡ + a → N * 2 ^ b < D * 2 ^ a → Lt N D z
Lt-intro N D z a b eq lt a′ b′ eq′ =
  ℕP.*-cancelʳ-< (2 ^ b) (N * 2 ^ b′) (D * 2 ^ a′) step
  where
    ab : a + b′ ≡ a′ + b
    ab = ℤP.+-injective
           (trans (cong (ℤ._+ + b′) (sym eq)) (trans (ZS.swap z (+ b) (+ b′)) (cong (ℤ._+ + b) eq′)))
    step : (N * 2 ^ b′) * 2 ^ b < (D * 2 ^ a′) * 2 ^ b
    step = subst (_< (D * 2 ^ a′) * 2 ^ b) (NS.swap N (2 ^ b) (2 ^ b′))
             (<-≤-trans (*-monoˡ-< (2 ^ b′) {{m^n≢0 2 b′}} lt)
               (≤-reflexive
                 (trans (NS.assoc D (2 ^ a) (2 ^ b′))
                   (trans (cong (D *_) (sym (^-distribˡ-+-* 2 a b′)))
                     (trans (cong (λ x → D * 2 ^ x) ab)
                       (trans (cong (D *_) (^-distribˡ-+-* 2 a′ b))
                         (sym (NS.assoc D (2 ^ a′) (2 ^ b)))))))))

-- | A larger exponent is a weaker bound.
Lt-mono : ∀ {N D z z′} → Lt N D z → z ℤ.≤ z′ → Lt N D z′
Lt-mono {N} {D} {z} {z′} lt z≤z′ a′ b′ eq′ =
  ≤-<-trans (≤-trans (m≤m*n (N * 2 ^ b′) (2 ^ δ) {{m^n≢0 2 δ}})
                     (≤-reflexive (trans (ℕP.*-assoc N (2 ^ b′) (2 ^ δ)) (cong (N *_) (sym (^-distribˡ-+-* 2 b′ δ))))))
            (lt a′ (b′ + δ) eqδ)
  where
    d≥0 : + 0 ℤ.≤ z′ ℤ.- z
    d≥0 = ℤP.i≤j⇒0≤j-i z≤z′
    δ : ℕ
    δ = ℤ.∣ z′ ℤ.- z ∣
    eqδ : z ℤ.+ + (b′ + δ) ≡ + a′
    eqδ = trans (cong (λ x → z ℤ.+ (+ b′ ℤ.+ x)) (ℤP.0≤i⇒+∣i∣≡i d≥0))
                (trans (ZS.mono z z′ (+ b′)) eq′)

Lt-≡ : ∀ {N D z z′} → z ≡ z′ → Lt N D z → Lt N D z′
Lt-≡ refl lt = lt

private
  ≤ᵇ-false : ∀ m n → (m ℕ.≤ᵇ n) ≡ false → n < m
  ≤ᵇ-false m n eq = ≰⇒> (λ le → subst T eq (ℕP.≤⇒≤ᵇ le))

  atLeast-false : ∀ N D z → atLeast N D z ≡ false → Lt N D z
  atLeast-false N D (+ j) eq =
    Lt-intro N D (+ j) j 0 (ℤP.+-identityʳ (+ j))
      (subst (_< D * 2 ^ j) (sym (*-identityʳ N)) (≤ᵇ-false (D * 2 ^ j) N eq))
  atLeast-false N D -[1+ j ] eq =
    Lt-intro N D -[1+ j ] 0 (suc j) (ℤP.+-inverseˡ (+ suc j))
      (subst (N * 2 ^ suc j <_) (sym (*-identityʳ D)) (≤ᵇ-false D (N * 2 ^ suc j) eq))

  lgAt-upper : ∀ N D κ b → atLeast N D κ ≡ b → κ ≡ (+ bitLen N) ℤ.- (+ bitLen D) → 0 < D
             → Lt N D (lgAt κ b ℤ.+ + 1)
  lgAt-upper N D κ true  _  refl D>0 =
    Lt-intro N D (((+ bitLen N) ℤ.- (+ bitLen D)) ℤ.+ + 1) (suc (bitLen N)) (bitLen D) (ZS.true-eq (+ bitLen N) (+ bitLen D))
      (<-≤-trans (*-monoˡ-< (2 ^ bitLen D) {{m^n≢0 2 (bitLen D)}} (bitLen-upper N))
        (≤-trans (*-monoʳ-≤ (2 ^ bitLen N) (bitLen-lower D D>0))
                 (≤-reflexive (NS.true-rhs D (2 ^ bitLen N)))))
  lgAt-upper N D κ false eq _ _ = Lt-≡ {N} {D} (sym (ZS.false-eq κ)) (atLeast-false N D κ eq)

-- | `N / D < 2^(lg N D + 1)`.
lg-upper : ∀ n d → Lt (suc n) (suc d) (lg (suc n) (suc d) ℤ.+ + 1)
lg-upper n d = lgAt-upper (suc n) (suc d) _ _ refl refl (s≤s z≤n)

-- | Below `2^P` after scaling by `2^z`: rounds to at most `2^P`.
scale-bound : ∀ N d z P → Lt N (suc d) (+ P ℤ.- z) → scaleRHE N d z ≤ 2 ^ P
scale-bound N d (+ j) P lt =
  divRHE-≤ (N * 2 ^ j) (suc d) (2 ^ P)
    (subst (N * 2 ^ j <_) (*-comm (suc d) (2 ^ P)) (lt P j (ZS.sub-add (+ P) (+ j))))
scale-bound N d -[1+ j ] P lt =
  divRHE-≤ N (suc d * 2 ^ suc j) (2 ^ P) {{ℕP.m*n≢0 (suc d) (2 ^ suc j) {{_}} {{m^n≢0 2 (suc j)}}}}
    (subst₂ _<_ (*-identityʳ N)
       (trans (cong (suc d *_) (^-distribˡ-+-* 2 P (suc j))) (NS.scale-rhs (suc d) (2 ^ P) (2 ^ suc j)))
       (lt (P + suc j) 0 (ℤP.+-identityʳ _)))
  where open import Relation.Binary.PropositionalEquality using (subst₂)

-- | The significand `roundQ` computes is at most `2^p`.
scaled-≤ : ∀ F n d E →
  scaleRHE (suc n) d (E ℤ.- quantum F (E ℤ.+ lg (suc n) (suc d))) ≤ 2 ^ suc (sig-bits F)
scaled-≤ F n d E =
  scale-bound (suc n) d (E ℤ.- q) (suc (sig-bits F)) (Lt-mono {suc n} {suc d} (lg-upper n d) room)
  where
    l = lg (suc n) (suc d)
    q = quantum F (E ℤ.+ l)
    room : l ℤ.+ + 1 ℤ.≤ + suc (sig-bits F) ℤ.- (E ℤ.- q)
    room = subst (l ℤ.+ + 1 ℤ.≤_) (sym (ZS.room E l q (+ sig-bits F)))
             (subst (ℤ._≤ (l ℤ.+ + 1) ℤ.+ (q ℤ.- ((E ℤ.+ l) ℤ.- + sig-bits F))) (ℤP.+-identityʳ _)
               (ℤP.+-monoʳ-≤ (l ℤ.+ + 1) (ℤP.i≤j⇒0≤j-i (ℤP.i≤i⊔j ((E ℤ.+ l) ℤ.- + sig-bits F) (qmin F)))))
