{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Observe — observing bisimilar computations: what one run
-- arrives at, the other arrives at too (`obs-≈`), and a computation that
-- returns at once is observed with no calls (`obs-return`).
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature; call)

module Once.Metatheory.Observe (Σ : Signature) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)
open import Once.Spec.Signature using (BTy; void; unit; int; float; _*_; _+_; module Op)
open Op using (ans)
open import Once.Spec.Effect Σ
open import Data.List using ([])
open import Once.Spec.Observation Σ
open import Once.Spec.Delay using (Delay; module Delay; _⇓_; now⇓; later⇓; _≈D_; mapD; mapStep)
open Delay using (step)
open import Once.Metatheory.Bisim Σ using (≈-sym)

open T∞ using (force)
open _≈_ using (force≈)

module _ (ι : Interp) where
  open Interp ι using (answer)

  -- One step of two observations of bisimilar runs: the same arrival, or
  -- observations of bisimilar runs again.
  data StepRel {X : Set} : (History × End X) ⊎ Delay (History × End X) → (History × End X) ⊎ Delay (History × End X) → Set where
    same : ∀ {o} → StepRel (inj₁ o) (inj₁ o)
    both : ∀ {h c m m′ n} → m ≈ m′ → StepRel (inj₂ (observeFrom ι h c m n)) (inj₂ (observeFrom ι h c m′ n))

  blockRel  : ∀ {X} h c {t t′ : T (X ⊎ T∞ X)} → BlockEq _≈_ t t′ → ∀ n → StepRel (blockObs ι h c t n) (blockObs ι h c t′ n)
  answerRel : ∀ {X} h c (b : BTy) (v : Answer b) {k k′ : _ → T (X ⊎ T∞ X)}
            → (∀ r → BlockEq _≈_ (k r) (k′ r)) → ∀ n → StepRel (answerObs ι h c (resume b v k) n) (answerObs ι h c (resume b v k′) n)
  blockRel h c e             zero    = same
  blockRel h c return≈       (suc n) = same
  blockRel h c (next≈ p)     (suc n) = both p
  blockRel h c (node≈ {o} {a} e) (suc n) = answerRel _ _ (ans o) (answer o h a) e n
  answerRel h c void    v e n = same
  answerRel h c unit    v e n = blockRel h c (e v) n
  answerRel h c int     v e n = blockRel h c (e v) n
  answerRel h c float   v e n = blockRel h c (e v) n
  answerRel h c (a * b) v e n = blockRel h c (e v) n
  answerRel h c (a + b) v e n = blockRel h c (e v) n

  private
    arrive : ∀ {X} {d d′ : Delay (History × End X)} {o} → StepRel (step d) (step d′) → d ⇓ o → d′ ⇓ o
    arrive₁ : ∀ {X} {s s′ : (History × End X) ⊎ Delay (History × End X)} {o d′}
            → StepRel s s′ → s ≡ inj₁ o → step d′ ≡ s′ → d′ ⇓ o
    arrive₂ : ∀ {X} {s s′ : (History × End X) ⊎ Delay (History × End X)} {o d₁ d′}
            → StepRel s s′ → s ≡ inj₂ d₁ → step d′ ≡ s′ → d₁ ⇓ o → d′ ⇓ o
    arrive {d = d} {d′} r (now⇓ eq)      = arrive₁ r eq refl
    arrive {d = d} {d′} r (later⇓ eq d⇓) = arrive₂ r eq refl d⇓
    arrive₁ same refl e′ = now⇓ e′
    arrive₂ (both {h = h} {c = c} {n = n} p) refl e′ d⇓ = later⇓ e′ (arrive (blockRel h c (force≈ p) n) d⇓)

  transfer : ∀ {X} h {m m′ : T∞ X} → m ≈ m′ → ∀ n {o} → observe ι h m n ⇓ o → observe ι h m′ n ⇓ o
  transfer h p n d⇓ = arrive (blockRel h [] (force≈ p) n) d⇓

  obs-≈ : ∀ (h : History) {X : Set} {m m′ : T∞ X} → m ≈ m′ → ∀ n → observe ι h m n ≈D observe ι h m′ n
  obs-≈ h p n = (λ o d⇓ → o , transfer h p n d⇓ , refl) , (λ o d⇓ → o , transfer h (≈-sym p) n d⇓ , refl)

  obs-return : ∀ (h : History) {X : Set} (x : X) n → events ι h (return∞ x) n ⇓ []
  obs-return h x zero    = now⇓ refl
  obs-return h x (suc n) = now⇓ refl
