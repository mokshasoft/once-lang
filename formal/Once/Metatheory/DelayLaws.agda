{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.DelayLaws — arrival through a map, and through two
-- delays that take the same next step.
------------------------------------------------------------------------

module Once.Metatheory.DelayLaws where

open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Once.Spec.Delay using (Delay; module Delay; mapD; mapStep; _⇓_; now⇓; later⇓)
open Delay using (step)

-- What arrives is mapped.
mapD⇓ : ∀ {A B : Set} {f : A → B} {d : Delay A} {a} → d ⇓ a → mapD f d ⇓ f a
mapD⇓ {f = f} (now⇓ e)      = now⇓ (cong (mapStep f) e)
mapD⇓ {f = f} (later⇓ e d⇓) = later⇓ (cong (mapStep f) e) (mapD⇓ d⇓)

private
  unmap₁ : ∀ {A B : Set} {f : A → B} (s : A ⊎ Delay A) {b} → mapStep f s ≡ inj₁ b → ∃[ a ] (s ≡ inj₁ a × f a ≡ b)
  unmap₁ (inj₁ a) refl = a , refl , refl
  unmap₁ (inj₂ d) ()

  unmap₂ : ∀ {A B : Set} {f : A → B} (s : A ⊎ Delay A) {d′} → mapStep f s ≡ inj₂ d′ → ∃[ d₀ ] (s ≡ inj₂ d₀ × d′ ≡ mapD f d₀)
  unmap₂ (inj₁ a) ()
  unmap₂ (inj₂ d) refl = d , refl , refl

-- What arrives through a map came from what arrives before it.
mapD⇓⁻ : ∀ {A B : Set} {f : A → B} {d : Delay A} {b} → mapD f d ⇓ b → ∃[ a ] (d ⇓ a × f a ≡ b)
mapD⇓⁻ {d = d} (now⇓ e) = later₁ (unmap₁ (step d) e)
  where
    later₁ : ∀ {A B : Set} {f : A → B} {d : Delay A} {b} → ∃[ a ] (step d ≡ inj₁ a × f a ≡ b) → ∃[ a ] (d ⇓ a × f a ≡ b)
    later₁ (a , e , fa) = a , now⇓ e , fa
mapD⇓⁻ {f = f} {d = d} (later⇓ e d⇓) = later₂ (unmap₂ (step d) e) d⇓
  where
    later₂ : ∀ {d′ b} → ∃[ d₀ ] (step d ≡ inj₂ d₀ × d′ ≡ mapD f d₀) → d′ ⇓ b → ∃[ a ] (d ⇓ a × f a ≡ b)
    later₂ (d₀ , e₀ , refl) d⇓ = go (mapD⇓⁻ d⇓)
      where
        go : ∀ {b} → ∃[ a ] (d₀ ⇓ a × f a ≡ b) → ∃[ a ] (d ⇓ a × f a ≡ b)
        go (a , d₀⇓ , fa) = a , later⇓ e₀ d₀⇓ , fa

-- Two delays that take the same next step arrive at the same values.
sameStep : ∀ {A : Set} {d d′ : Delay A} {a} → step d ≡ step d′ → d ⇓ a → d′ ⇓ a
sameStep p (now⇓ e)      = now⇓ (trans (sym p) e)
sameStep p (later⇓ e d⇓) = later⇓ (trans (sym p) e) d⇓
