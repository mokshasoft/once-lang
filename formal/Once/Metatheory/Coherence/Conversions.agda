{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Coherence.Conversions — a coercion is functorial, up to
-- sameness: along `A <: A` it is the identity (`conv-id`), along a composite
-- the composite (`conv-∘`; a derivation of `A <: C` is unique, so it is the
-- composite's).
--
-- By induction on the derivations; at an arrow the effect lift and the map
-- are monad laws up to bisimilarity, and the results are related over runs.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)

module Once.Metatheory.Coherence.Conversions (Σ : Signature) where

open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Spec.Grade using (Purity; fin; mk-kind; Zero; One; Many; _⊑π_; ⊑-pure; ⊑-pa; ⊑-act; ⊑-eff)
open import Once.Spec.Type using (Ty; TySub; _⟨_⟩)
open import Once.Spec.Sub
open import Once.Spec.Effect Σ
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ; conv)
open import Once.Spec.Equivalence Σ using (Same; SameM)
open import Once.Metatheory.Types using (<:-trans; <:-unique; ⊑π-trans)
open import Once.Metatheory.Bisim Σ using (≈-refl; ≈-sym; ≈-trans; ≈-bind; idˡ; idʳ; assoc)
open import Once.Metatheory.Erase Σ using (toT∞-sub; toT∞-fmap)
open import Once.Metatheory.Coherence.Relation Σ
open import Once.Metatheory.Coherence.Conv Σ using (convSame)

private
  -- An effect lift after a map: the map, in `T∞`.
  subFmap≈ : ∀ {π π′} (g : π ⊑π π′) {X Y : Set} (h : X → Y) (m : M π X)
           → toT∞ π′ (sub g (fmap π h m)) ≈ (toT∞ π m >>=∞ λ x → return∞ (h x))
  subFmap≈ {π} g h m = ≈-trans (toT∞-sub g (fmap π h m)) (toT∞-fmap π h m)

  -- Two lifts after two maps: the composite map, in `T∞`.
  subFmap²≈ : ∀ {π π′ π″} (g : π ⊑π π′) (g′ : π′ ⊑π π″) {X Y Z : Set} (h : X → Y) (h′ : Y → Z) (m : M π X)
            → toT∞ π″ (sub g′ (fmap π′ h′ (sub g (fmap π h m)))) ≈ (toT∞ π m >>=∞ λ x → return∞ (h′ (h x)))
  subFmap²≈ {π} {π′} g g′ h h′ m =
    ≈-trans (subFmap≈ g′ h′ (sub g (fmap π h m)))
      (≈-trans (≈-bind (subFmap≈ g h m) (λ y → ≈-refl (return∞ (h′ y))))
        (≈-trans (assoc (toT∞ π m) _ _) (≈-bind (≈-refl (toT∞ π m)) (λ x → idˡ (h x) _))))

  -- Related computations, mapped by functions that relate values.
  mapped : ∀ π {A B : Ty 0} {m m′ : M π ⟦ A ⟧ᵛ} {u : T∞ ⟦ B ⟧ᵛ} {u′ : T∞ ⟦ B ⟧ᵛ} {h h′ : ⟦ A ⟧ᵛ → ⟦ B ⟧ᵛ}
         → u ≈ (toT∞ π m >>=∞ λ x → return∞ (h x)) → u′ ≈ (toT∞ π m′ >>=∞ λ x → return∞ (h′ x))
         → SameM π A m m′ → (∀ {x x′} → Same A x x′ → Same B (h x) (h′ x′))
         → Related (Same B) u u′
  mapped π e e′ s k = ≈-Relatedˡ e (≈-Relatedʳ e′ (bindRel (fromObserved s) λ r → returnRel (k r)))

module _ {m : ℕ} (σ : TySub m 0) where

  conv-id : ∀ {A : Ty m} (p : A <: A) {x x′} → Same (A ⟨ σ ⟩) x x′ → Same (A ⟨ σ ⟩) (conv σ p x) x′
  conv-id sub-void {()}
  conv-id sub-var   s = s
  conv-id sub-unit  s = s
  conv-id sub-int   s = s
  conv-id sub-float s = s
  conv-id (sub-arr {q = Zero} {π} a b g) {f} {f′} s =
    toObserved (mapped π (subFmap≈ g (conv σ b) (f _)) (≈-sym (idʳ (toT∞ π (f′ _)))) s (conv-id b))
  conv-id (sub-arr {q = One} {π} a b g) {f} {f′} s = λ y y′ sy →
    toObserved (mapped π (subFmap≈ g (conv σ b) (f (conv σ a y))) (≈-sym (idʳ (toT∞ π (f′ y′)))) (s _ _ (conv-id a sy)) (conv-id b))
  conv-id (sub-arr {q = Many} {π} a b g) {f} {f′} s = λ y y′ sy →
    toObserved (mapped π (subFmap≈ g (conv σ b) (f (conv σ a y))) (≈-sym (idʳ (toT∞ π (f′ y′)))) (s _ _ (conv-id a sy)) (conv-id b))
  conv-id (sub-* a b) (s , t) = conv-id a s , conv-id b t
  conv-id (sub-+ a b) {inj₁ x} {inj₁ y} s = conv-id a s
  conv-id (sub-+ a b) {inj₂ x} {inj₂ y} s = conv-id b s
  conv-id (sub-+ a b) {inj₁ x} {inj₂ y} ()
  conv-id (sub-+ a b) {inj₂ x} {inj₁ y} ()
  conv-id sub-μ s = s
  conv-id (sub-ν ⊑-pure) s = s
  conv-id (sub-ν ⊑-act)  s = s

  -- Along the composite derivation.
  convT : ∀ {A B C : Ty m} (p : A <: B) (q : B <: C) {x x′}
        → Same (A ⟨ σ ⟩) x x′ → Same (C ⟨ σ ⟩) (conv σ (<:-trans p q) x) (conv σ q (conv σ p x′))
  convT sub-void q {()}
  convT sub-var   q s = convSame σ q s
  convT sub-unit  q s = convSame σ q s
  convT sub-int   q s = convSame σ q s
  convT sub-float q s = convSame σ q s
  convT (sub-arr {q = Zero} {π} a b g) (sub-arr a′ b′ g′) {f} {f′} s =
    toObserved (mapped π (subFmap≈ (⊑π-trans g g′) (conv σ (<:-trans b b′)) (f _))
                       (subFmap²≈ g g′ (conv σ b) (conv σ b′) (f′ _)) s (convT b b′))
  convT (sub-arr {q = One} {π} a b g) (sub-arr a′ b′ g′) {f} {f′} s = λ y y′ sy →
    toObserved (mapped π (subFmap≈ (⊑π-trans g g′) (conv σ (<:-trans b b′)) (f (conv σ (<:-trans a′ a) y)))
                       (subFmap²≈ g g′ (conv σ b) (conv σ b′) (f′ (conv σ a (conv σ a′ y′))))
                       (s _ _ (convT a′ a sy)) (convT b b′))
  convT (sub-arr {q = Many} {π} a b g) (sub-arr a′ b′ g′) {f} {f′} s = λ y y′ sy →
    toObserved (mapped π (subFmap≈ (⊑π-trans g g′) (conv σ (<:-trans b b′)) (f (conv σ (<:-trans a′ a) y)))
                       (subFmap²≈ g g′ (conv σ b) (conv σ b′) (f′ (conv σ a (conv σ a′ y′))))
                       (s _ _ (convT a′ a sy)) (convT b b′))
  convT (sub-* a b) (sub-* a′ b′) (s , t) = convT a a′ s , convT b b′ t
  convT (sub-+ a b) (sub-+ a′ b′) {inj₁ x} {inj₁ y} s = convT a a′ s
  convT (sub-+ a b) (sub-+ a′ b′) {inj₂ x} {inj₂ y} s = convT b b′ s
  convT (sub-+ a b) (sub-+ a′ b′) {inj₁ x} {inj₂ y} ()
  convT (sub-+ a b) (sub-+ a′ b′) {inj₂ x} {inj₁ y} ()
  convT sub-μ q s = convSame σ q s
  convT (sub-ν ⊑-pure) (sub-ν g′)    s = convSame σ (sub-ν g′) s
  convT (sub-ν ⊑-pa)   (sub-ν ⊑-act) s = convSame σ (sub-ν ⊑-pa) s
  convT (sub-ν ⊑-act)  (sub-ν ⊑-act) s = s

  conv-∘ : ∀ {A B C : Ty m} (p : A <: B) (q : B <: C) (r : A <: C) {x x′}
         → Same (A ⟨ σ ⟩) x x′ → Same (C ⟨ σ ⟩) (conv σ r x) (conv σ q (conv σ p x′))
  conv-∘ p q r s rewrite <:-unique r (<:-trans p q) = convT p q s
