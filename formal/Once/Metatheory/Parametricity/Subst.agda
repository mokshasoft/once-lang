{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Parametricity.Subst — the relational reading commutes
-- with substitution: `A ⟨ τ ⟩` read with a relation per variable relates
-- what `A` relates when each of its variables `j` is read as `τ j`.
--
-- The two value sets agree only up to `⟨⟩-∘` (an instance of an instance is
-- the composed instance), which is what the meaning of a reference to a
-- definition transports along (`Spec.Core.Meaning`, `⊢ref`). So the lemma is
-- stated across that transport, both ways at once (an arrow's domain turns
-- it round), by recursion on `A`: at each former `⟨⟩-∘` is a `cong` of the
-- parts' equalities, and transporting a value along it is transporting its
-- parts (each such fact holds by matching the equalities as `refl`). A
-- functor's constants are related along the functor's equality (`Fits`).
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)

module Once.Metatheory.Parametricity.Subst (Σ : Signature) where

open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst; subst₂)
open import Once.Spec.Grade using (Finite; Purity; ArrowKind; mk-kind; Zero; One; Many)
open import Once.Spec.Type
  using (Ty; Type; Fun; TySub; _⟨_⟩; _⟨_⟩F; var; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ; ν; K; Id; _⊕_; _⊗_)
open import Once.Spec.Type.Substitution using (⟨⟩-∘; ⟨⟩F-∘)
open import Once.Spec.Effect Σ using (M; toT∞; SRel; rK; rId; _r⊕_; _r⊗_)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ; code)
open import Once.Spec.Equivalence Σ
open import Once.Metatheory.Coherence.Layer Σ using (_⊆ᶜ_; RelNu-mono)
open import Once.Metatheory.Parametricity.Identity Σ using (Observed-mono; RelMu-mono)

------------------------------------------------------------------------
-- Transporting values along the equalities `⟨⟩-∘` is built from
------------------------------------------------------------------------

private
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

private
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

------------------------------------------------------------------------
-- The lemma
------------------------------------------------------------------------

module _ {k m : ℕ} (τ : TySub k m) {σ σ′ : TySub m 0} (ρ : RelSub σ σ′) where

  -- Each of `A`'s variables `j` read as `τ j`.
  ρ∘τ : RelSub (λ i → τ i ⟨ σ ⟩) (λ i → τ i ⟨ σ′ ⟩)
  ρ∘τ = relSub (λ j → Rel (τ j) ρ)

  private
    e  : ∀ A → A ⟨ τ ⟩ ⟨ σ ⟩ ≡ A ⟨ (λ i → τ i ⟨ σ ⟩) ⟩
    e  A = ⟨⟩-∘ A τ σ
    e′ : ∀ A → A ⟨ τ ⟩ ⟨ σ′ ⟩ ≡ A ⟨ (λ i → τ i ⟨ σ′ ⟩) ⟩
    e′ A = ⟨⟩-∘ A τ σ′

  rel-sub→  : ∀ (A : Ty k) {x y} → Rel A ρ∘τ x y
            → Rel (A ⟨ τ ⟩) ρ (subst T⟦_⟧ (sym (e A)) x) (subst T⟦_⟧ (sym (e′ A)) y)
  rel-sub←  : ∀ (A : Ty k) {x y} → Rel (A ⟨ τ ⟩) ρ x y
            → Rel A ρ∘τ (subst T⟦_⟧ (e A) x) (subst T⟦_⟧ (e′ A) y)
  fits→ : ∀ (F : Fun k) → Fits (sym (⟨⟩F-∘ F τ σ)) (sym (⟨⟩F-∘ F τ σ′)) (RelF F ρ∘τ) (RelF (F ⟨ τ ⟩F) ρ)
  fits← : ∀ (F : Fun k) → Fits (⟨⟩F-∘ F τ σ) (⟨⟩F-∘ F τ σ′) (RelF (F ⟨ τ ⟩F) ρ) (RelF F ρ∘τ)

  rel-sub→ (var j) r = r
  rel-sub→ Unit    r = r
  rel-sub→ Void    r = r
  rel-sub→ Int     r = r
  rel-sub→ Float   r = r
  rel-sub→ (A * B) {x₁ , x₂} {y₁ , y₂} (r , r′) =
    subst₂ (Rel ((A * B) ⟨ τ ⟩) ρ) (sym (sym-* (e A) (e B) x₁ x₂)) (sym (sym-* (e′ A) (e′ B) y₁ y₂))
      (rel-sub→ A r , rel-sub→ B r′)
  rel-sub→ (A + B) {inj₁ x} {inj₁ y} r =
    subst₂ (Rel ((A + B) ⟨ τ ⟩) ρ) (sym (sym-+₁ (e A) (e B) x)) (sym (sym-+₁ (e′ A) (e′ B) y)) (rel-sub→ A r)
  rel-sub→ (A + B) {inj₂ x} {inj₂ y} r =
    subst₂ (Rel ((A + B) ⟨ τ ⟩) ρ) (sym (sym-+₂ (e A) (e B) x)) (sym (sym-+₂ (e′ A) (e′ B) y)) (rel-sub→ B r)
  rel-sub→ (A + B) {inj₁ x} {inj₂ y} ()
  rel-sub→ (A + B) {inj₂ x} {inj₁ y} ()
  rel-sub→ (A ⇒[ mk-kind Zero π ] B) {f} {f′} r =
    subst₂ (λ u u′ → Observed (Rel (B ⟨ τ ⟩) ρ) (toT∞ π u) (toT∞ π u′))
      (sym (app-sym₀ π (e A) (e B) f _)) (sym (app-sym₀ π (e′ A) (e′ B) f′ _))
      (obs-subst π (sym (e B)) (sym (e′ B)) (Observed-mono (rel-sub→ B) r))
  rel-sub→ (A ⇒[ mk-kind One π ] B) {f} {f′} r a a′ s =
    subst₂ (λ u u′ → Observed (Rel (B ⟨ τ ⟩) ρ) (toT∞ π u) (toT∞ π u′))
      (sym (app-sym₁ π (e A) (e B) f a)) (sym (app-sym₁ π (e′ A) (e′ B) f′ a′))
      (obs-subst π (sym (e B)) (sym (e′ B)) (Observed-mono (rel-sub→ B) (r _ _ (rel-sub← A s))))
  rel-sub→ (A ⇒[ mk-kind Many π ] B) {f} {f′} r a a′ s =
    subst₂ (λ u u′ → Observed (Rel (B ⟨ τ ⟩) ρ) (toT∞ π u) (toT∞ π u′))
      (sym (app-sym π (e A) (e B) f a)) (sym (app-sym π (e′ A) (e′ B) f′ a′))
      (obs-subst π (sym (e B)) (sym (e′ B)) (Observed-mono (rel-sub→ B) (r _ _ (rel-sub← A s))))
  rel-sub→ (μ F) r = castμˢ (⟨⟩F-∘ F τ σ) (⟨⟩F-∘ F τ σ′) (fits→ F) r
  rel-sub→ (ν F f) r = castνˢ f (⟨⟩F-∘ F τ σ) (⟨⟩F-∘ F τ σ′) (fits→ F) r

  rel-sub← (var j) r = r
  rel-sub← Unit    r = r
  rel-sub← Void    r = r
  rel-sub← Int     r = r
  rel-sub← Float   r = r
  rel-sub← (A * B) {x₁ , x₂} {y₁ , y₂} (r , r′) =
    subst₂ (Rel (A * B) ρ∘τ) (sym (fwd-* (e A) (e B) x₁ x₂)) (sym (fwd-* (e′ A) (e′ B) y₁ y₂))
      (rel-sub← A r , rel-sub← B r′)
  rel-sub← (A + B) {inj₁ x} {inj₁ y} r =
    subst₂ (Rel (A + B) ρ∘τ) (sym (fwd-+₁ (e A) (e B) x)) (sym (fwd-+₁ (e′ A) (e′ B) y)) (rel-sub← A r)
  rel-sub← (A + B) {inj₂ x} {inj₂ y} r =
    subst₂ (Rel (A + B) ρ∘τ) (sym (fwd-+₂ (e A) (e B) x)) (sym (fwd-+₂ (e′ A) (e′ B) y)) (rel-sub← B r)
  rel-sub← (A + B) {inj₁ x} {inj₂ y} ()
  rel-sub← (A + B) {inj₂ x} {inj₁ y} ()
  rel-sub← (A ⇒[ mk-kind Zero π ] B) {f} {f′} r =
    subst₂ (λ u u′ → Observed (Rel B ρ∘τ) (toT∞ π u) (toT∞ π u′))
      (sym (app-fwd₀ π (e A) (e B) f _)) (sym (app-fwd₀ π (e′ A) (e′ B) f′ _))
      (obs-subst π (e B) (e′ B) (Observed-mono (rel-sub← B) r))
  rel-sub← (A ⇒[ mk-kind One π ] B) {f} {f′} r a a′ s =
    subst₂ (λ u u′ → Observed (Rel B ρ∘τ) (toT∞ π u) (toT∞ π u′))
      (sym (app-fwd₁ π (e A) (e B) f a)) (sym (app-fwd₁ π (e′ A) (e′ B) f′ a′))
      (obs-subst π (e B) (e′ B) (Observed-mono (rel-sub← B) (r _ _ (rel-sub→ A s))))
  rel-sub← (A ⇒[ mk-kind Many π ] B) {f} {f′} r a a′ s =
    subst₂ (λ u u′ → Observed (Rel B ρ∘τ) (toT∞ π u) (toT∞ π u′))
      (sym (app-fwd π (e A) (e B) f a)) (sym (app-fwd π (e′ A) (e′ B) f′ a′))
      (obs-subst π (e B) (e′ B) (Observed-mono (rel-sub← B) (r _ _ (rel-sub→ A s))))
  rel-sub← (μ F) r = castμ (⟨⟩F-∘ F τ σ) (⟨⟩F-∘ F τ σ′) (fits← F) r
  rel-sub← (ν F f) r = castν f (⟨⟩F-∘ F τ σ) (⟨⟩F-∘ F τ σ′) (fits← F) r

  fits→ (K A)   = fits-Kˢ (e A) (e′ A) (rel-sub→ A)
  fits→ Id      = tt
  fits→ (F ⊕ G) = fits-⊕ˢ (⟨⟩F-∘ F τ σ) (⟨⟩F-∘ G τ σ) (⟨⟩F-∘ F τ σ′) (⟨⟩F-∘ G τ σ′) (fits→ F) (fits→ G)
  fits→ (F ⊗ G) = fits-⊗ˢ (⟨⟩F-∘ F τ σ) (⟨⟩F-∘ G τ σ) (⟨⟩F-∘ F τ σ′) (⟨⟩F-∘ G τ σ′) (fits→ F) (fits→ G)

  fits← (K A)   = fits-K (e A) (e′ A) (rel-sub← A)
  fits← Id      = tt
  fits← (F ⊕ G) = fits-⊕ (⟨⟩F-∘ F τ σ) (⟨⟩F-∘ G τ σ) (⟨⟩F-∘ F τ σ′) (⟨⟩F-∘ G τ σ′) (fits← F) (fits← G)
  fits← (F ⊗ G) = fits-⊗ (⟨⟩F-∘ F τ σ) (⟨⟩F-∘ G τ σ) (⟨⟩F-∘ F τ σ′) (⟨⟩F-∘ G τ σ′) (fits← F) (fits← G)
