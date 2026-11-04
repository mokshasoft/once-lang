{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Parametricity.Transport — transporting values along
-- equalities of types built by the type formers' `cong`s: a transported
-- pair is the pair of its transported parts, a transported function
-- transports its argument back and its result forwards, and trees and
-- streams are related along their functors' equality when the constants'
-- relations are (`Fits`). Each holds by matching the equalities as `refl`;
-- with K, any two proofs of one type equality are equal (`uip`).
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)

module Once.Metatheory.Parametricity.Transport (Σ : Signature) where

open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Once.Spec.Grade using (Finite; Purity; mk-kind; Zero; One; Many)
open import Once.Spec.Type using (Type; Fun; _*_; _+_; _⇒[_]_; μ; ν; K; _⊕_; _⊗_)
open import Once.Spec.Effect Σ using (M; toT∞; SRel; rK; rId; _r⊕_; _r⊗_)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ; code)
open import Once.Spec.Equivalence Σ using (Observed; RelMu; RelStream)
open import Once.Metatheory.Coherence.Layer Σ using (_⊆ᶜ_; RelNu-mono)
open import Once.Metatheory.Parametricity.Identity Σ using (RelMu-mono)

-- With K, one proof of a type equality.
uip : ∀ {X : Set} {x y : X} (p q : x ≡ y) → p ≡ q
uip refl refl = refl

-- Transporting there and back.
coe-sym : ∀ {C D : Type} (e : C ≡ D) (x : ⟦ D ⟧ᵛ) → subst ⟦_⟧ᵛ e (subst ⟦_⟧ᵛ (sym e) x) ≡ x
coe-sym refl x = refl

sym-coe : ∀ {C D : Type} (e : C ≡ D) (x : ⟦ C ⟧ᵛ) → subst ⟦_⟧ᵛ (sym e) (subst ⟦_⟧ᵛ e x) ≡ x
sym-coe refl x = refl


T⟦_⟧ : Type → Set
T⟦ X ⟧ = ⟦ X ⟧ᵛ

MT : Purity → Type → Set
MT π X = M π ⟦ X ⟧ᵛ

-- products and sums go by their parts
sym-* : ∀ {C₁ C₂ D₁ D₂ : Type} (p : C₁ ≡ D₁) (q : C₂ ≡ D₂) (a : ⟦ D₁ ⟧ᵛ) (b : ⟦ D₂ ⟧ᵛ)
      → subst T⟦_⟧ (sym (cong₂ _*_ p q)) (a , b) ≡ (subst T⟦_⟧ (sym p) a , subst T⟦_⟧ (sym q) b)
sym-* refl refl a b = refl

fwd-* : ∀ {C₁ C₂ D₁ D₂ : Type} (p : C₁ ≡ D₁) (q : C₂ ≡ D₂) (a : ⟦ C₁ ⟧ᵛ) (b : ⟦ C₂ ⟧ᵛ)
      → subst T⟦_⟧ (cong₂ _*_ p q) (a , b) ≡ (subst T⟦_⟧ p a , subst T⟦_⟧ q b)
fwd-* refl refl a b = refl

sym-+₁ : ∀ {C₁ C₂ D₁ D₂ : Type} (p : C₁ ≡ D₁) (q : C₂ ≡ D₂) (a : ⟦ D₁ ⟧ᵛ)
       → subst T⟦_⟧ (sym (cong₂ _+_ p q)) (inj₁ a) ≡ inj₁ (subst T⟦_⟧ (sym p) a)
sym-+₁ refl refl a = refl
sym-+₂ : ∀ {C₁ C₂ D₁ D₂ : Type} (p : C₁ ≡ D₁) (q : C₂ ≡ D₂) (b : ⟦ D₂ ⟧ᵛ)
       → subst T⟦_⟧ (sym (cong₂ _+_ p q)) (inj₂ b) ≡ inj₂ (subst T⟦_⟧ (sym q) b)
sym-+₂ refl refl b = refl
fwd-+₁ : ∀ {C₁ C₂ D₁ D₂ : Type} (p : C₁ ≡ D₁) (q : C₂ ≡ D₂) (a : ⟦ C₁ ⟧ᵛ)
       → subst T⟦_⟧ (cong₂ _+_ p q) (inj₁ a) ≡ inj₁ (subst T⟦_⟧ p a)
fwd-+₁ refl refl a = refl
fwd-+₂ : ∀ {C₁ C₂ D₁ D₂ : Type} (p : C₁ ≡ D₁) (q : C₂ ≡ D₂) (b : ⟦ C₂ ⟧ᵛ)
       → subst T⟦_⟧ (cong₂ _+_ p q) (inj₂ b) ≡ inj₂ (subst T⟦_⟧ q b)
fwd-+₂ refl refl b = refl

-- the computation of a transported function, at a transported argument
app-sym : ∀ π {C₁ C₂ D₁ D₂ : Type} (p : C₁ ≡ D₁) (p′ : C₂ ≡ D₂) (f : ⟦ D₁ ⟧ᵛ → MT π D₂) (a : ⟦ C₁ ⟧ᵛ)
        → subst T⟦_⟧ (sym (cong₂ (λ x y → x ⇒[ mk-kind Many π ] y) p p′)) f a ≡ subst (MT π) (sym p′) (f (subst T⟦_⟧ p a))
app-sym π refl refl f a = refl
app-sym₁ : ∀ π {C₁ C₂ D₁ D₂ : Type} (p : C₁ ≡ D₁) (p′ : C₂ ≡ D₂) (f : ⟦ D₁ ⟧ᵛ → MT π D₂) (a : ⟦ C₁ ⟧ᵛ)
         → subst T⟦_⟧ (sym (cong₂ (λ x y → x ⇒[ mk-kind One π ] y) p p′)) f a ≡ subst (MT π) (sym p′) (f (subst T⟦_⟧ p a))
app-sym₁ π refl refl f a = refl
app-sym₀ : ∀ π {C₁ C₂ D₁ D₂ : Type} (p : C₁ ≡ D₁) (p′ : C₂ ≡ D₂) (f : _ → MT π D₂) u
         → subst T⟦_⟧ (sym (cong₂ (λ x y → x ⇒[ mk-kind Zero π ] y) p p′)) f u ≡ subst (MT π) (sym p′) (f u)
app-sym₀ π refl refl f u = refl

app-fwd : ∀ π {C₁ C₂ D₁ D₂ : Type} (p : C₁ ≡ D₁) (p′ : C₂ ≡ D₂) (f : ⟦ C₁ ⟧ᵛ → MT π C₂) (a : ⟦ D₁ ⟧ᵛ)
        → subst T⟦_⟧ (cong₂ (λ x y → x ⇒[ mk-kind Many π ] y) p p′) f a ≡ subst (MT π) p′ (f (subst T⟦_⟧ (sym p) a))
app-fwd π refl refl f a = refl
app-fwd₁ : ∀ π {C₁ C₂ D₁ D₂ : Type} (p : C₁ ≡ D₁) (p′ : C₂ ≡ D₂) (f : ⟦ C₁ ⟧ᵛ → MT π C₂) (a : ⟦ D₁ ⟧ᵛ)
         → subst T⟦_⟧ (cong₂ (λ x y → x ⇒[ mk-kind One π ] y) p p′) f a ≡ subst (MT π) p′ (f (subst T⟦_⟧ (sym p) a))
app-fwd₁ π refl refl f a = refl
app-fwd₀ : ∀ π {C₁ C₂ D₁ D₂ : Type} (p : C₁ ≡ D₁) (p′ : C₂ ≡ D₂) (f : _ → MT π C₂) u
         → subst T⟦_⟧ (cong₂ (λ x y → x ⇒[ mk-kind Zero π ] y) p p′) f u ≡ subst (MT π) p′ (f u)
app-fwd₀ π refl refl f u = refl

-- observing transported computations
obs-subst : ∀ π {C D C′ D′ : Type} (e : C ≡ D) (e′ : C′ ≡ D′) {R : ⟦ D ⟧ᵛ → ⟦ D′ ⟧ᵛ → Set} {m m′}
          → Observed (λ u v → R (subst T⟦_⟧ e u) (subst T⟦_⟧ e′ v)) (toT∞ π m) (toT∞ π m′)
          → Observed R (toT∞ π (subst (MT π) e m)) (toT∞ π (subst (MT π) e′ m′))
obs-subst π refl refl o = o

-- A functor's constants, related along an equality of the functors.
Fits : ∀ {G G′ H H′ : Fun 0} → G ≡ H → G′ ≡ H′ → SRel (code G) (code G′) → SRel (code H) (code H′) → Set
Fits refl refl q q′ = q ⊆ᶜ q′

fits-K : ∀ {C C′ D D′ : Type} (e : C ≡ D) (e′ : C′ ≡ D′) {Q Q′}
       → (∀ {a b} → Q a b → Q′ (subst T⟦_⟧ e a) (subst T⟦_⟧ e′ b)) → Fits (cong K e) (cong K e′) (rK Q) (rK Q′)
fits-K refl refl h = h

fits-⊕ : ∀ {G₁ G₂ H₁ H₂ G₁′ G₂′ H₁′ H₂′ : Fun 0} (p₁ : G₁ ≡ H₁) (p₂ : G₂ ≡ H₂) (p₁′ : G₁′ ≡ H₁′) (p₂′ : G₂′ ≡ H₂′) {g g′ k k′}
       → Fits p₁ p₁′ g g′ → Fits p₂ p₂′ k k′ → Fits (cong₂ _⊕_ p₁ p₂) (cong₂ _⊕_ p₁′ p₂′) (g r⊕ k) (g′ r⊕ k′)
fits-⊕ refl refl refl refl c d = c , d

fits-⊗ : ∀ {G₁ G₂ H₁ H₂ G₁′ G₂′ H₁′ H₂′ : Fun 0} (p₁ : G₁ ≡ H₁) (p₂ : G₂ ≡ H₂) (p₁′ : G₁′ ≡ H₁′) (p₂′ : G₂′ ≡ H₂′) {g g′ k k′}
       → Fits p₁ p₁′ g g′ → Fits p₂ p₂′ k k′ → Fits (cong₂ _⊗_ p₁ p₂) (cong₂ _⊗_ p₁′ p₂′) (g r⊗ k) (g′ r⊗ k′)
fits-⊗ refl refl refl refl c d = c , d

-- the same, backwards
fits-Kˢ : ∀ {C C′ D D′ : Type} (e : C ≡ D) (e′ : C′ ≡ D′) {Q Q′}
        → (∀ {a b} → Q a b → Q′ (subst T⟦_⟧ (sym e) a) (subst T⟦_⟧ (sym e′) b)) → Fits (sym (cong K e)) (sym (cong K e′)) (rK Q) (rK Q′)
fits-Kˢ refl refl h = h

fits-⊕ˢ : ∀ {G₁ G₂ H₁ H₂ G₁′ G₂′ H₁′ H₂′ : Fun 0} (p₁ : G₁ ≡ H₁) (p₂ : G₂ ≡ H₂) (p₁′ : G₁′ ≡ H₁′) (p₂′ : G₂′ ≡ H₂′) {g g′ k k′}
        → Fits (sym p₁) (sym p₁′) g g′ → Fits (sym p₂) (sym p₂′) k k′ → Fits (sym (cong₂ _⊕_ p₁ p₂)) (sym (cong₂ _⊕_ p₁′ p₂′)) (g r⊕ k) (g′ r⊕ k′)
fits-⊕ˢ refl refl refl refl c d = c , d

fits-⊗ˢ : ∀ {G₁ G₂ H₁ H₂ G₁′ G₂′ H₁′ H₂′ : Fun 0} (p₁ : G₁ ≡ H₁) (p₂ : G₂ ≡ H₂) (p₁′ : G₁′ ≡ H₁′) (p₂′ : G₂′ ≡ H₂′) {g g′ k k′}
        → Fits (sym p₁) (sym p₁′) g g′ → Fits (sym p₂) (sym p₂′) k k′ → Fits (sym (cong₂ _⊗_ p₁ p₂)) (sym (cong₂ _⊗_ p₁′ p₂′)) (g r⊗ k) (g′ r⊗ k′)
fits-⊗ˢ refl refl refl refl c d = c , d

-- trees and streams, along their functors' equality
castμ : ∀ {G H G′ H′ : Fun 0} (p : G ≡ H) (p′ : G′ ≡ H′) {q q′} → Fits p p′ q q′
      → ∀ {x y} → RelMu q x y → RelMu q′ (subst T⟦_⟧ (cong μ p) x) (subst T⟦_⟧ (cong μ p′) y)
castμ refl refl c r = RelMu-mono _ _ c r

castμˢ : ∀ {G H G′ H′ : Fun 0} (p : G ≡ H) (p′ : G′ ≡ H′) {q q′} → Fits (sym p) (sym p′) q q′
       → ∀ {x y} → RelMu q x y → RelMu q′ (subst T⟦_⟧ (sym (cong μ p)) x) (subst T⟦_⟧ (sym (cong μ p′)) y)
castμˢ refl refl c r = RelMu-mono _ _ c r

castν : ∀ (f : Finite) {G H G′ H′ : Fun 0} (p : G ≡ H) (p′ : G′ ≡ H′) {q q′} → Fits p p′ q q′
      → ∀ {v w} → RelStream f q v w
      → RelStream f q′ (subst T⟦_⟧ (cong (λ X → ν X f) p) v) (subst T⟦_⟧ (cong (λ X → ν X f) p′) w)
castν f refl refl c r n = RelNu-mono f _ _ c n (r n)

castνˢ : ∀ (f : Finite) {G H G′ H′ : Fun 0} (p : G ≡ H) (p′ : G′ ≡ H′) {q q′} → Fits (sym p) (sym p′) q q′
       → ∀ {v w} → RelStream f q v w
       → RelStream f q′ (subst T⟦_⟧ (sym (cong (λ X → ν X f) p)) v) (subst T⟦_⟧ (sym (cong (λ X → ν X f) p′)) w)
castνˢ f refl refl c r n = RelNu-mono f _ _ c n (r n)

