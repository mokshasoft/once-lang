{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Parametricity.Subst — the relational reading commutes
-- with substitution: `A ⟨ τ ⟩` read with a relation per variable relates
-- what `A` relates when each of its variables `j` is read as `τ j`.
--
-- Stated for instances `τ₁`, `τ₂` of `A`'s variables that are the composed
-- ones (`τ j ⟨ σ ⟩`, `τ j ⟨ σ′ ⟩`) up to an equality per variable (`e₁`,
-- `e₂`): a meaning reads a definition at the instance its derivation
-- builds, which is the composed one only up to such equalities. The values
-- are carried across by transport along `E`, the equality of the whole type
-- built from them by the formers' `cong`s; transporting along any other
-- proof is the same (`Transport.uip`). Both ways at once, by recursion on
-- `A` (an arrow's domain turns it round).
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)

module Once.Metatheory.Parametricity.Subst (Σ : Signature) where

open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst; subst₂)
open import Once.Spec.Grade using (mk-kind; Zero; One; Many)
open import Once.Spec.Type
  using (Ty; Type; Fun; TySub; _⟨_⟩; _⟨_⟩F; var; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ; ν; K; Id; _⊕_; _⊗_)
open import Once.Spec.Effect Σ using (toT∞)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ)
open import Once.Spec.Equivalence Σ
open import Once.Metatheory.Parametricity.Identity Σ using (Observed-mono)
open import Once.Metatheory.Parametricity.Transport Σ

-- The equality of a type at two instances, from one per variable.
E  : ∀ {k m} {τ₁ : TySub k 0} {τ : TySub k m} {σ : TySub m 0} → (∀ j → τ₁ j ≡ τ j ⟨ σ ⟩) → (A : Ty k) → A ⟨ τ₁ ⟩ ≡ A ⟨ τ ⟩ ⟨ σ ⟩
EF : ∀ {k m} {τ₁ : TySub k 0} {τ : TySub k m} {σ : TySub m 0} → (∀ j → τ₁ j ≡ τ j ⟨ σ ⟩) → (F : Fun k) → F ⟨ τ₁ ⟩F ≡ F ⟨ τ ⟩F ⟨ σ ⟩F
E e (var j)      = e j
E e Unit         = refl
E e Void         = refl
E e Int          = refl
E e Float        = refl
E e (A * B)      = cong₂ _*_ (E e A) (E e B)
E e (A + B)      = cong₂ _+_ (E e A) (E e B)
E e (A ⇒[ k ] B) = cong₂ (λ a b → a ⇒[ k ] b) (E e A) (E e B)
E e (μ F)        = cong μ (EF e F)
E e (ν F f)      = cong (λ G → ν G f) (EF e F)
EF e (K A)   = cong K (E e A)
EF e Id      = refl
EF e (F ⊕ G) = cong₂ _⊕_ (EF e F) (EF e G)
EF e (F ⊗ G) = cong₂ _⊗_ (EF e F) (EF e G)

module _ {k m : ℕ} (τ : TySub k m) {σ σ′ : TySub m 0} (ρ : RelSub σ σ′)
         {τ₁ τ₂ : TySub k 0} (e₁ : ∀ j → τ₁ j ≡ τ j ⟨ σ ⟩) (e₂ : ∀ j → τ₂ j ≡ τ j ⟨ σ′ ⟩) where

  -- Each of `A`'s variables `j` read as `τ j`, at the instances `τ₁`, `τ₂`.
  ρ∘τ : RelSub τ₁ τ₂
  ρ∘τ = relSub (λ j x y → Rel (τ j) ρ (subst ⟦_⟧ᵛ (e₁ j) x) (subst ⟦_⟧ᵛ (e₂ j) y))

  rel-sub→ : ∀ (A : Ty k) {x y} → Rel A ρ∘τ x y
           → Rel (A ⟨ τ ⟩) ρ (subst T⟦_⟧ (E e₁ A) x) (subst T⟦_⟧ (E e₂ A) y)
  rel-sub← : ∀ (A : Ty k) {x y} → Rel (A ⟨ τ ⟩) ρ x y
           → Rel A ρ∘τ (subst T⟦_⟧ (sym (E e₁ A)) x) (subst T⟦_⟧ (sym (E e₂ A)) y)
  fits→ : ∀ (F : Fun k) → Fits (EF e₁ F) (EF e₂ F) (RelF F ρ∘τ) (RelF (F ⟨ τ ⟩F) ρ)
  fits← : ∀ (F : Fun k) → Fits (sym (EF e₁ F)) (sym (EF e₂ F)) (RelF (F ⟨ τ ⟩F) ρ) (RelF F ρ∘τ)

  rel-sub→ (var j) r = r
  rel-sub→ Unit    r = r
  rel-sub→ Void    r = r
  rel-sub→ Int     r = r
  rel-sub→ Float   r = r
  rel-sub→ (A * B) {x₁ , x₂} {y₁ , y₂} (r , r′) =
    subst₂ (Rel ((A * B) ⟨ τ ⟩) ρ) (sym (fwd-* (E e₁ A) (E e₁ B) x₁ x₂)) (sym (fwd-* (E e₂ A) (E e₂ B) y₁ y₂))
      (rel-sub→ A r , rel-sub→ B r′)
  rel-sub→ (A + B) {inj₁ x} {inj₁ y} r =
    subst₂ (Rel ((A + B) ⟨ τ ⟩) ρ) (sym (fwd-+₁ (E e₁ A) (E e₁ B) x)) (sym (fwd-+₁ (E e₂ A) (E e₂ B) y)) (rel-sub→ A r)
  rel-sub→ (A + B) {inj₂ x} {inj₂ y} r =
    subst₂ (Rel ((A + B) ⟨ τ ⟩) ρ) (sym (fwd-+₂ (E e₁ A) (E e₁ B) x)) (sym (fwd-+₂ (E e₂ A) (E e₂ B) y)) (rel-sub→ B r)
  rel-sub→ (A + B) {inj₁ x} {inj₂ y} ()
  rel-sub→ (A + B) {inj₂ x} {inj₁ y} ()
  rel-sub→ (A ⇒[ mk-kind Zero π ] B) {f} {f′} r =
    subst₂ (λ u u′ → Observed (Rel (B ⟨ τ ⟩) ρ) (toT∞ π u) (toT∞ π u′))
      (sym (app-fwd₀ π (E e₁ A) (E e₁ B) f _)) (sym (app-fwd₀ π (E e₂ A) (E e₂ B) f′ _))
      (obs-subst π (E e₁ B) (E e₂ B) (Observed-mono (rel-sub→ B) r))
  rel-sub→ (A ⇒[ mk-kind One π ] B) {f} {f′} r a a′ s =
    subst₂ (λ u u′ → Observed (Rel (B ⟨ τ ⟩) ρ) (toT∞ π u) (toT∞ π u′))
      (sym (app-fwd₁ π (E e₁ A) (E e₁ B) f a)) (sym (app-fwd₁ π (E e₂ A) (E e₂ B) f′ a′))
      (obs-subst π (E e₁ B) (E e₂ B) (Observed-mono (rel-sub→ B) (r _ _ (rel-sub← A s))))
  rel-sub→ (A ⇒[ mk-kind Many π ] B) {f} {f′} r a a′ s =
    subst₂ (λ u u′ → Observed (Rel (B ⟨ τ ⟩) ρ) (toT∞ π u) (toT∞ π u′))
      (sym (app-fwd π (E e₁ A) (E e₁ B) f a)) (sym (app-fwd π (E e₂ A) (E e₂ B) f′ a′))
      (obs-subst π (E e₁ B) (E e₂ B) (Observed-mono (rel-sub→ B) (r _ _ (rel-sub← A s))))
  rel-sub→ (μ F) r = castμ (EF e₁ F) (EF e₂ F) (fits→ F) r
  rel-sub→ (ν F f) r = castν f (EF e₁ F) (EF e₂ F) (fits→ F) r

  rel-sub← (var j) {x} {y} r = subst₂ (Rel (τ j) ρ) (sym (coe-sym (e₁ j) x)) (sym (coe-sym (e₂ j) y)) r
  rel-sub← Unit    r = r
  rel-sub← Void    r = r
  rel-sub← Int     r = r
  rel-sub← Float   r = r
  rel-sub← (A * B) {x₁ , x₂} {y₁ , y₂} (r , r′) =
    subst₂ (Rel (A * B) ρ∘τ) (sym (sym-* (E e₁ A) (E e₁ B) x₁ x₂)) (sym (sym-* (E e₂ A) (E e₂ B) y₁ y₂))
      (rel-sub← A r , rel-sub← B r′)
  rel-sub← (A + B) {inj₁ x} {inj₁ y} r =
    subst₂ (Rel (A + B) ρ∘τ) (sym (sym-+₁ (E e₁ A) (E e₁ B) x)) (sym (sym-+₁ (E e₂ A) (E e₂ B) y)) (rel-sub← A r)
  rel-sub← (A + B) {inj₂ x} {inj₂ y} r =
    subst₂ (Rel (A + B) ρ∘τ) (sym (sym-+₂ (E e₁ A) (E e₁ B) x)) (sym (sym-+₂ (E e₂ A) (E e₂ B) y)) (rel-sub← B r)
  rel-sub← (A + B) {inj₁ x} {inj₂ y} ()
  rel-sub← (A + B) {inj₂ x} {inj₁ y} ()
  rel-sub← (A ⇒[ mk-kind Zero π ] B) {f} {f′} r =
    subst₂ (λ u u′ → Observed (Rel B ρ∘τ) (toT∞ π u) (toT∞ π u′))
      (sym (app-sym₀ π (E e₁ A) (E e₁ B) f _)) (sym (app-sym₀ π (E e₂ A) (E e₂ B) f′ _))
      (obs-subst π (sym (E e₁ B)) (sym (E e₂ B)) (Observed-mono (rel-sub← B) r))
  rel-sub← (A ⇒[ mk-kind One π ] B) {f} {f′} r a a′ s =
    subst₂ (λ u u′ → Observed (Rel B ρ∘τ) (toT∞ π u) (toT∞ π u′))
      (sym (app-sym₁ π (E e₁ A) (E e₁ B) f a)) (sym (app-sym₁ π (E e₂ A) (E e₂ B) f′ a′))
      (obs-subst π (sym (E e₁ B)) (sym (E e₂ B)) (Observed-mono (rel-sub← B) (r _ _ (rel-sub→ A s))))
  rel-sub← (A ⇒[ mk-kind Many π ] B) {f} {f′} r a a′ s =
    subst₂ (λ u u′ → Observed (Rel B ρ∘τ) (toT∞ π u) (toT∞ π u′))
      (sym (app-sym π (E e₁ A) (E e₁ B) f a)) (sym (app-sym π (E e₂ A) (E e₂ B) f′ a′))
      (obs-subst π (sym (E e₁ B)) (sym (E e₂ B)) (Observed-mono (rel-sub← B) (r _ _ (rel-sub→ A s))))
  rel-sub← (μ F) r = castμˢ (EF e₁ F) (EF e₂ F) (fits← F) r
  rel-sub← (ν F f) r = castνˢ f (EF e₁ F) (EF e₂ F) (fits← F) r

  fits→ (K A)   = fits-K (E e₁ A) (E e₂ A) (rel-sub→ A)
  fits→ Id      = tt
  fits→ (F ⊕ G) = fits-⊕ (EF e₁ F) (EF e₁ G) (EF e₂ F) (EF e₂ G) (fits→ F) (fits→ G)
  fits→ (F ⊗ G) = fits-⊗ (EF e₁ F) (EF e₁ G) (EF e₂ F) (EF e₂ G) (fits→ F) (fits→ G)

  fits← (K A)   = fits-Kˢ (E e₁ A) (E e₂ A) (rel-sub← A)
  fits← Id      = tt
  fits← (F ⊕ G) = fits-⊕ˢ (EF e₁ F) (EF e₁ G) (EF e₂ F) (EF e₂ G) (fits← F) (fits← G)
  fits← (F ⊗ G) = fits-⊗ˢ (EF e₁ F) (EF e₁ G) (EF e₂ F) (EF e₂ G) (fits← F) (fits← G)
