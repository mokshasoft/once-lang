{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Erase — every grade's computation, read as a `T∞` tree
-- (`toT∞`), turns the grade's monad operations into `T∞`'s, up to
-- bisimilarity: units, binds (plain and graded), maps, and the morphisms
-- along the order. What a computation is observed as never depends on the
-- grade it was typed at.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature; call)

module Once.Metatheory.Erase (Σ : Signature) where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Once.Spec.Grade using (Purity; pure; act; eff⁺; eff; _·p_; _⊑π_; ⊑-pure; ⊑-pa; ⊑-pe; ⊑-act; ⊑-ae; ⊑-g; ⊑-ge; ⊑-eff)
open import Once.Spec.Effect Σ
open import Once.Metatheory.Bisim Σ

open T∞ using (force)
open _≈_ using (force≈)

embed-bind : ∀ {X Y} (m : T X) (k : X → T Y) → embed (m >>=T k) ≈ (embed m >>=∞ λ x → embed (k x))
force≈ (embed-bind (roll (done x))            k) = ≈-reflS (force (embed (k x)))
force≈ (embed-bind (roll (node (call o a k′))) k) = node≈ λ b → embed-bind (k′ b) k

embed-return : ∀ {X} (x : X) → embed (returnT x) ≈ return∞ x
force≈ (embed-return x) = done≈

forget⁺-bind : ∀ {X Y} (p : T⁺ X) (h : X → T∞ Y) → forget⁺ (p >>=⁺ h) ≈ (forget⁺ p >>=∞ h)
force≈ (forget⁺-bind (call⁺ (call o a k)) h) = node≈ λ b → ≈-refl (k b >>=∞ h)

forget⁺-=<<  : ∀ {X Y} (n : T∞ X) (f : X → T⁺ Y) → forget⁺ (n ⁺=<< f) ≈ (n >>=∞ λ x → forget⁺ (f x))
forget⁺-=<<S : ∀ {X Y} (s : Step X (T∞ X)) (f : X → T⁺ Y)
             → StepEq _≈_ (force (forget⁺ (bindF⁺ s f))) (bindStep s λ x → forget⁺ (f x))
force≈ (forget⁺-=<< n f) = forget⁺-=<<S (force n) f
forget⁺-=<<S (done x)            f = ≈-reflS (force (forget⁺ (f x)))
forget⁺-=<<S (node (call o a k)) f = node≈ λ b → ≈-refl (k b >>=∞ λ x → forget⁺ (f x))

toT∞-return : ∀ {π} (u : pure ⊑π π) {X : Set} (x : X) → toT∞ π (return u x) ≈ return∞ x
toT∞-return ⊑-pure x = ≈-refl (return∞ x)
toT∞-return ⊑-pa   x = embed-return x
toT∞-return ⊑-pe   x = ≈-refl (return∞ x)

toT∞-bind : ∀ π {X Y : Set} (m : M π X) (k : X → M π Y)
          → toT∞ π (bind π m k) ≈ (toT∞ π m >>=∞ λ x → toT∞ π (k x))
toT∞-bind pure m k = ≈-sym (idˡ m (λ x → return∞ (k x)))
toT∞-bind act  m k = embed-bind m k
toT∞-bind eff⁺ m k = forget⁺-bind m (λ x → forget⁺ (k x))
toT∞-bind eff  m k = ≈-refl (m >>=∞ k)

toT∞-bindᵍ : ∀ π₁ π₂ {X Y : Set} (m : M π₁ X) (k : X → M π₂ Y)
           → toT∞ (π₁ ·p π₂) (bindᵍ π₁ π₂ m k) ≈ (toT∞ π₁ m >>=∞ λ x → toT∞ π₂ (k x))
toT∞-bindᵍ pure π₂   m k = ≈-sym (idˡ m (λ x → toT∞ π₂ (k x)))
toT∞-bindᵍ act  pure m k =
  ≈-trans (embed-bind m (λ x → returnT (k x))) (≈-bind (≈-refl (embed m)) (λ x → embed-return (k x)))
toT∞-bindᵍ act  act  m k = embed-bind m k
toT∞-bindᵍ act  eff⁺ m k = forget⁺-=<< (embed m) k
toT∞-bindᵍ act  eff  m k = ≈-refl (embed m >>=∞ k)
toT∞-bindᵍ eff⁺ pure m k = forget⁺-bind m (λ x → return∞ (k x))
toT∞-bindᵍ eff⁺ act  m k = forget⁺-bind m (λ x → embed (k x))
toT∞-bindᵍ eff⁺ eff⁺ m k = forget⁺-bind m (λ x → forget⁺ (k x))
toT∞-bindᵍ eff⁺ eff  m k = forget⁺-bind m k
toT∞-bindᵍ eff  pure m k = ≈-refl (m >>=∞ λ x → return∞ (k x))
toT∞-bindᵍ eff  act  m k = ≈-refl (m >>=∞ λ x → embed (k x))
toT∞-bindᵍ eff  eff⁺ m k = forget⁺-=<< m k
toT∞-bindᵍ eff  eff  m k = ≈-refl (m >>=∞ k)

toT∞-fmap : ∀ π {X Y : Set} (f : X → Y) (m : M π X) → toT∞ π (fmap π f m) ≈ (toT∞ π m >>=∞ λ x → return∞ (f x))
toT∞-fmap pure f m = ≈-sym (idˡ m (λ x → return∞ (f x)))
toT∞-fmap act  f m =
  ≈-trans (embed-bind m (λ x → returnT (f x))) (≈-bind (≈-refl (embed m)) (λ x → embed-return (f x)))
toT∞-fmap eff⁺ f m = forget⁺-bind m (λ x → return∞ (f x))
toT∞-fmap eff  f m = ≈-refl (m >>=∞ λ x → return∞ (f x))

-- Subeffecting is invisible as a tree.
toT∞-sub : ∀ {π π′} (g : π ⊑π π′) {X : Set} (m : M π X) → toT∞ π′ (sub g m) ≈ toT∞ π m
toT∞-sub ⊑-pure m = ≈-refl (return∞ m)
toT∞-sub ⊑-pa   m = embed-return m
toT∞-sub ⊑-pe   m = ≈-refl (return∞ m)
toT∞-sub ⊑-act  m = ≈-refl (embed m)
toT∞-sub ⊑-ae   m = ≈-refl (embed m)
toT∞-sub ⊑-g    m = ≈-refl (forget⁺ m)
toT∞-sub ⊑-ge   m = ≈-refl (forget⁺ m)
toT∞-sub ⊑-eff  m = ≈-refl m

-- Equal computations are bisimilar trees.
eqM→≈ : ∀ π {X : Set} {m m′ : M π X} → EqM π m m′ → toT∞ π m ≈ toT∞ π m′
eqM→≈ pure {m = m} refl = ≈-refl (return∞ m)
eqM→≈ act  {m = m} refl = ≈-refl (embed m)
eqM→≈ eff⁺ e = e
eqM→≈ eff  e = e
