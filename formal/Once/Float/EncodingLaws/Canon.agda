-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Float.EncodingLaws.Canon — what `canon` computes: a positive `M` at
-- exponent `e`, given fuel at least `M`, becomes `fv-num s m (e + k)` with
-- `odd m · 2^k ≡ M`; and since that factorisation is unique, `canon` of
-- `odd m · 2^k` returns exactly `m` and `e + k`.
------------------------------------------------------------------------

module Once.Float.EncodingLaws.Canon where

open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _*_; _^_; _<_; _≤_; s≤s; z≤n; s≤s⁻¹)
open import Data.Nat.Properties
  using (≤-trans; <-≤-trans; *-comm; *-identityʳ; ≡ᵇ⇒≡; m^n>0; *-monoʳ-≤; n≢0⇒n>0; <⇒≢)
open import Data.Nat.DivMod using (_/_; _%_; m≡m%n+[m/n]*n; m%n<n; m/n<m)
import Data.Integer as ℤ
open import Data.Integer using (ℤ; +_)
import Data.Integer.Properties as ℤP
open import Data.Product using (Σ; _×_; _,_)
open import Data.Bool using (Bool; true; false; T)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

open import Once.Spec.Float.Value using (Sign; FloatVal; fv-num; odd; canon; canonAt)
open import Once.Float.EncodingLaws.Nat using (pow-suc; odd-pow-inj)

-- | The result of `canon` on a positive significand.
CanonOf : Sign → ℕ → ℤ → FloatVal → Set
CanonOf s M e v = Σ ℕ λ m → Σ ℕ λ k → (v ≡ fv-num s m (e ℤ.+ + k)) × (odd m * 2 ^ k ≡ M)

private
  -- `M % 2` is 0 or 1.
  mod2-cases : ∀ M → M % 2 ≢ 1 → M % 2 ≡ 0
  mod2-cases M ne with M % 2 | m%n<n M 2
  ... | zero    | _             = refl
  ... | suc zero | _            = ⊥-elim (ne refl)
  ... | suc (suc _) | s≤s (s≤s ())

  canonAt-spec : ∀ f s M e b → (M % 2 ℕ.≡ᵇ 1) ≡ b → 0 < M → M ≤ suc f
               → CanonOf s M e (canonAt f s M e b)

  canon-spec′ : ∀ f s M e → 0 < M → M ≤ f → CanonOf s M e (canon f s M e)
  canon-spec′ (suc f) s (suc M) e _ le = canonAt-spec f s (suc M) e _ refl (s≤s z≤n) le

  canonAt-spec f s M e true b≡ M>0 le =
    M / 2 , 0 , cong (fv-num s (M / 2)) (sym (ℤP.+-identityʳ e)) , odd≡
    where
      r≡1 : M % 2 ≡ 1
      r≡1 = ≡ᵇ⇒≡ (M % 2) 1 (subst T (sym b≡) _)
      odd≡ : odd (M / 2) * 1 ≡ M
      odd≡ = trans (*-identityʳ _)
               (sym (trans (m≡m%n+[m/n]*n M 2)
                      (cong₂ _+_ r≡1 (*-comm (M / 2) 2))))
  canonAt-spec f s M e false b≡ M>0 le = step (canon-spec′ f s (M / 2) (e ℤ.+ + 1) h>0 h≤f)
    where
      r≡0 : M % 2 ≡ 0
      r≡0 = mod2-cases M (λ eq → subst T b≡ (subst (λ x → T (x ℕ.≡ᵇ 1)) (sym eq) _))
      M≡ : M ≡ 2 * (M / 2)
      M≡ = trans (m≡m%n+[m/n]*n M 2) (trans (cong (_+ M / 2 * 2) r≡0) (*-comm (M / 2) 2))
      h>0 : 0 < M / 2
      h>0 = n≢0⇒n>0 (λ h0 → <⇒≢ M>0 (sym (trans M≡ (cong (2 *_) h0))))
      h≤f : M / 2 ≤ f
      h≤f = s≤s⁻¹ (<-≤-trans (m/n<m M 2 {{ℕ.>-nonZero M>0}} (s≤s (s≤s z≤n))) le)
      step : CanonOf s (M / 2) (e ℤ.+ + 1) (canon f s (M / 2) (e ℤ.+ + 1))
           → CanonOf s M e (canon f s (M / 2) (e ℤ.+ + 1))
      step (m , k , eq , oddk) =
        m , suc k , trans eq (cong (fv-num s m) (ℤP.+-assoc e (+ 1) (+ k))) ,
        trans (pow-suc (odd m) k) (trans (cong (2 *_) oddk) (sym M≡))

-- | `canon M s M e` on a positive `M`.
canon-spec : ∀ s M e → 0 < M → CanonOf s M e (canon M s M e)
canon-spec s M e M>0 = canon-spec′ M s M e M>0 Data.Nat.Properties.≤-refl

-- | `canon` of `odd m · 2^k` is `m` at `e + k`.
canon-odd : ∀ s m k e → canon (odd m * 2 ^ k) s (odd m * 2 ^ k) e ≡ fv-num s m (e ℤ.+ + k)
canon-odd s m k e with canon-spec s (odd m * 2 ^ k) e (<-≤-trans (s≤s z≤n) (*-monoʳ-≤ (odd m) (m^n>0 2 k)))
... | m′ , k′ , eq , oddk with odd-pow-inj m′ m k′ k oddk
... | refl , refl = eq
