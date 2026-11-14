-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Float.Nat — the natural-number facts behind the
-- encoding laws: `bitLen` brackets its argument between powers of two,
-- shifts add to it, an odd significand times a power of two determines both,
-- and round half to even moves a quotient up by at most one.
------------------------------------------------------------------------

module Once.Metatheory.Float.Nat where

open import Data.Nat as ℕ
  using (ℕ; zero; suc; _+_; _*_; _∸_; _^_; _<_; _≤_; _≥_; s≤s; z≤n; s≤s⁻¹; NonZero)
open import Data.Nat.Properties
  using ( ≤-refl; ≤-trans; <-≤-trans; ≤-<-trans; ≤-reflexive; <⇒≤; ≰⇒>; <⇒≢
        ; *-comm; *-assoc; *-identityʳ; +-comm; *-cancelˡ-≤; *-cancelˡ-≡
        ; *-monoˡ-≤; *-monoʳ-≤; *-monoˡ-<; ^-monoʳ-≤; ^-distribˡ-+-*
        ; m^n>0; m^n≢0; ≡ᵇ⇒≡; suc-injective; <⇒≱; ≤-antisym; ≤∧≢⇒<
        ; m≤m*n; ^-monoʳ-<; n≤1+n)
open import Data.Nat.DivMod
  using (_/_; _%_; m≡m%n+[m/n]*n; m%n<n; m/n<m; m/n*n≤m; [m+kn]%n≡m%n; m*n%n≡0
        ; m<n*o⇒m/o<n)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Bool using (Bool; true; false; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import Once.Spec.Float.Dyadic using (bitLen-go; bitLen)
open import Once.Spec.Float.Value using (odd; roundHalfEven; divRHE)

------------------------------------------------------------------------
-- bitLen
------------------------------------------------------------------------

private
  go-zero : ∀ f → bitLen-go f 0 ≡ 0
  go-zero zero    = refl
  go-zero (suc f) = refl

  -- `m` lies below twice its half, plus two.
  half-bound : ∀ m B → m / 2 < 2 ^ B → m < 2 * 2 ^ B
  half-bound m B h< =
    subst (_< 2 * 2 ^ B) (sym (m≡m%n+[m/n]*n m 2))
      (<-≤-trans (step (m%n<n m 2))
        (≤-trans (*-monoˡ-≤ 2 h<) (≤-reflexive (*-comm (2 ^ B) 2))))
    where
      step : m % 2 < 2 → m % 2 + m / 2 * 2 < suc (m / 2) * 2
      step r< = Data.Nat.Properties.+-monoˡ-< (m / 2 * 2) r<

  half≤ : ∀ n → suc n / 2 ≤ n
  half≤ n with m/n<m (suc n) 2 (s≤s (s≤s z≤n))
  ... | s≤s le = le

  go-upper : ∀ f n → n ≤ f → n < 2 ^ bitLen-go f n
  go-upper zero    zero    _        = s≤s z≤n
  go-upper (suc f) zero    _        = s≤s z≤n
  go-upper (suc f) (suc n) (s≤s le) =
    half-bound (suc n) (bitLen-go f (suc n / 2)) (go-upper f (suc n / 2) (≤-trans (half≤ n) le))

  go-lower : ∀ f n → n ≤ f → 0 < n → 2 ^ bitLen-go f n ≤ 2 * n
  go-lower (suc f) (suc n) (s≤s le) _ with suc n / 2 in eq
  ... | zero    rewrite go-zero f = *-monoʳ-≤ 2 (s≤s z≤n)
  ... | suc h   =
    *-monoʳ-≤ 2 (≤-trans (go-lower f (suc h) (subst (_≤ f) eq (≤-trans (half≤ n) le)) (s≤s z≤n))
                         (subst (λ x → 2 * x ≤ suc n) eq
                           (≤-trans (≤-reflexive (*-comm 2 (suc n / 2))) (m/n*n≤m (suc n) 2))))

-- | Every number lies below `2 ^ bitLen`.
bitLen-upper : ∀ n → n < 2 ^ bitLen n
bitLen-upper n = go-upper n n ≤-refl

-- | A positive number is at least `2 ^ (bitLen − 1)`, stated without `∸`.
bitLen-lower : ∀ n → 0 < n → 2 ^ bitLen n ≤ 2 * n
bitLen-lower n = go-lower n n ≤-refl

-- | Below `2 ^ k`: at most `k` bits.
bitLen-≤ : ∀ n k → n < 2 ^ k → bitLen n ≤ k
bitLen-≤ zero    k _  = z≤n
bitLen-≤ (suc n) k n< with bitLen (suc n) ℕ.≤? k
... | yes le = le
... | no ¬le = ⊥-elim (<⇒≱ n< (*-cancelˡ-≤ 2 (≤-trans (^-monoʳ-≤ 2 (≰⇒> ¬le)) (bitLen-lower (suc n) (s≤s z≤n)))))

-- | At least `2 ^ k`: more than `k` bits.
bitLen-≥ : ∀ n k → 2 ^ k ≤ n → suc k ≤ bitLen n
bitLen-≥ n k le with suc k ℕ.≤? bitLen n
... | yes lt = lt
... | no ¬lt = ⊥-elim (<⇒≱ (bitLen-upper n) (≤-trans (^-monoʳ-≤ 2 (s≤s⁻¹ (≰⇒> ¬lt))) le))

bitLen-pos : ∀ n → 0 < n → 1 ≤ bitLen n
bitLen-pos n (s≤s _) = bitLen-≥ n 0 (s≤s z≤n)

private
  shift-aux : ∀ m k B → bitLen m ≡ B → 0 < m → bitLen (m * 2 ^ k) ≡ B + k
  shift-aux m k zero    eq m>0 = ⊥-elim (1+n≰n (subst (1 ≤_) eq (bitLen-pos m m>0) ))
    where open import Data.Nat.Properties using (1+n≰n)
  shift-aux m k (suc B) eq m>0 = ≤-antisym up down
    where
      up : bitLen (m * 2 ^ k) ≤ suc B + k
      up = bitLen-≤ _ _
             (<-≤-trans (*-monoˡ-< (2 ^ k) {{m^n≢0 2 k}} (subst (λ x → m < 2 ^ x) eq (bitLen-upper m)))
                        (≤-reflexive (sym (^-distribˡ-+-* 2 (suc B) k))))
      lowB : 2 ^ B ≤ m
      lowB = *-cancelˡ-≤ 2 (subst (λ x → 2 ^ x ≤ 2 * m) eq (bitLen-lower m m>0))
      down : suc B + k ≤ bitLen (m * 2 ^ k)
      down = bitLen-≥ _ _ (≤-trans (≤-reflexive (^-distribˡ-+-* 2 B k)) (*-monoˡ-≤ (2 ^ k) lowB))

-- | Shifting left by `k` adds `k` bits.
bitLen-shift : ∀ m k → 0 < m → bitLen (m * 2 ^ k) ≡ bitLen m + k
bitLen-shift m k = shift-aux m k (bitLen m) refl

------------------------------------------------------------------------
-- Odd significands
------------------------------------------------------------------------

odd≢even : ∀ a b → odd a ≢ 2 * b
odd≢even a b eq = 1≢0 (trans (sym l) (trans (cong (_% 2) eq) r))
  where
    1≢0 : 1 ≢ 0
    1≢0 ()
    l : odd a % 2 ≡ 1
    l = trans (cong (λ x → suc x % 2) (*-comm 2 a)) ([m+kn]%n≡m%n 1 a 2)
    r : (2 * b) % 2 ≡ 0
    r = trans (cong (_% 2) (*-comm 2 b)) (m*n%n≡0 b 2)

pow-suc : ∀ x i → x * 2 ^ suc i ≡ 2 * (x * 2 ^ i)
pow-suc x i = trans (sym (*-assoc x 2 (2 ^ i)))
                (trans (cong (_* 2 ^ i) (*-comm x 2)) (*-assoc 2 x (2 ^ i)))

-- | `odd a · 2^i` determines `a` and `i`.
odd-pow-inj : ∀ a b i j → odd a * 2 ^ i ≡ odd b * 2 ^ j → a ≡ b × i ≡ j
odd-pow-inj a b zero zero eq =
  *-cancelˡ-≡ a b 2 (suc-injective (trans (sym (*-identityʳ (odd a))) (trans eq (*-identityʳ (odd b))))) , refl
odd-pow-inj a b zero (suc j) eq =
  ⊥-elim (odd≢even a (odd b * 2 ^ j) (trans (sym (*-identityʳ (odd a))) (trans eq (pow-suc (odd b) j))))
odd-pow-inj a b (suc i) zero eq =
  ⊥-elim (odd≢even b (odd a * 2 ^ i) (trans (sym (*-identityʳ (odd b))) (trans (sym eq) (pow-suc (odd a) i))))
odd-pow-inj a b (suc i) (suc j) eq with odd-pow-inj a b i j
  (*-cancelˡ-≡ _ _ 2 (trans (sym (pow-suc (odd a) i)) (trans eq (pow-suc (odd b) j))))
... | a≡b , refl = a≡b , refl

-- | An odd significand whose shift is at most `2 ^ suc P` is below it.
odd-pow-< : ∀ m k P → odd m * 2 ^ k ≤ 2 ^ suc P → odd m < 2 ^ suc P
odd-pow-< m zero P le =
  ≤∧≢⇒< (subst (_≤ 2 ^ suc P) (*-identityʳ (odd m)) le) (odd≢even m (2 ^ P))
odd-pow-< m (suc k) P le =
  ≤-<-trans (≤-trans (m≤m*n (odd m) (2 ^ k) {{m^n≢0 2 k}})
                     (*-cancelˡ-≤ 2 (subst (_≤ 2 ^ suc P) (pow-suc (odd m) k) le)))
            (^-monoʳ-< 2 (s≤s (s≤s z≤n)) {P} {suc P} (s≤s ≤-refl))

------------------------------------------------------------------------
-- Round half to even
------------------------------------------------------------------------

rhe≤ : ∀ q r den → roundHalfEven q r den ≤ suc q
rhe≤ q r den with (2 * r) ℕ.<ᵇ den
... | true  = n≤1+n q
... | false with den ℕ.<ᵇ (2 * r)
...   | true  = ≤-refl
...   | false with (q % 2) ℕ.≡ᵇ 0
...     | true  = n≤1+n q
...     | false = ≤-refl

-- | A quotient below `N` rounds to at most `N`.
divRHE-≤ : ∀ num den N {{_ : NonZero den}} → num < N * den → divRHE num den ≤ N
divRHE-≤ num den N lt = ≤-trans (rhe≤ (num / den) (num % den) den) (m<n*o⇒m/o<n lt)
