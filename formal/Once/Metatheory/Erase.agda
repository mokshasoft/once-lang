{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Erase — every grade's computation, read in `T∞`
-- (`toT∞`), turns the grade's monad operations into `T∞`'s, up to
-- bisimilarity: units, binds (plain and graded), maps, and the morphisms
-- along the chain. What a computation is observed as never depends on the
-- grade it was typed at.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature; call)

module Once.Metatheory.Erase (Σ : Signature) where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Spec.Grade using (Purity; pure; act; eff; _·p_; _⊑π_; ⊑-pure; ⊑-pa; ⊑-pe; ⊑-act; ⊑-ae; ⊑-eff)
open import Once.Spec.Effect Σ
open import Once.Metatheory.Bisim Σ

open _≈ν_ using (force≈)

embed-bind  : ∀ {X Y} (m : T X) (k : X → T Y) → embed (m >>=T k) ≈ (embed m >>=∞ λ x → embed (k x))
embed-bindB : ∀ {X Y} (m : T X) (k : X → T Y)
            → mapT inj₁ (m >>=T k) ≈B bindBlock (mapT inj₁ m) (λ x → embed (k x))
force≈ (embed-bind m k) = embed-bindB m k
embed-bindB (roll (done x))             k = ≈-reflB (mapT inj₁ (k x))
embed-bindB (roll (node (call o a k′))) k = node≈ λ b → embed-bindB (k′ b) k

embed-return : ∀ {X} (x : X) → embed (returnT x) ≈ return∞ x
force≈ (embed-return x) = return≈

toT∞-return : ∀ π {X : Set} (x : X) → toT∞ π (return π x) ≈ return∞ x
toT∞-return pure x = ≈-refl (return∞ x)
toT∞-return act  x = embed-return x
toT∞-return eff  x = ≈-refl (return∞ x)

toT∞-bind : ∀ π {X Y : Set} (m : M π X) (k : X → M π Y)
          → toT∞ π (bind π m k) ≈ (toT∞ π m >>=∞ λ x → toT∞ π (k x))
toT∞-bind pure m k = ≈-sym (idˡ m (λ x → return∞ (k x)))
toT∞-bind act  m k = embed-bind m k
toT∞-bind eff  m k = ≈-refl (m >>=∞ k)

toT∞-bindᵍ : ∀ π₁ π₂ {X Y : Set} (m : M π₁ X) (k : X → M π₂ Y)
           → toT∞ (π₁ ·p π₂) (bindᵍ π₁ π₂ m k) ≈ (toT∞ π₁ m >>=∞ λ x → toT∞ π₂ (k x))
toT∞-bindᵍ pure π₂   m k = ≈-sym (idˡ m (λ x → toT∞ π₂ (k x)))
toT∞-bindᵍ act  pure m k =
  ≈-trans (embed-bind m (λ x → returnT (k x))) (≈-bind (≈-refl (embed m)) (λ x → embed-return (k x)))
toT∞-bindᵍ act  act  m k = embed-bind m k
toT∞-bindᵍ act  eff  m k = ≈-refl (embed m >>=∞ k)
toT∞-bindᵍ eff  pure m k = ≈-refl (m >>=∞ λ x → return∞ (k x))
toT∞-bindᵍ eff  act  m k = ≈-refl (m >>=∞ λ x → embed (k x))
toT∞-bindᵍ eff  eff  m k = ≈-refl (m >>=∞ k)

toT∞-fmap : ∀ π {X Y : Set} (f : X → Y) (m : M π X) → toT∞ π (fmap π f m) ≈ (toT∞ π m >>=∞ λ x → return∞ (f x))
toT∞-fmap pure f m = ≈-sym (idˡ m (λ x → return∞ (f x)))
toT∞-fmap act  f m =
  ≈-trans (embed-bind m (λ x → returnT (f x))) (≈-bind (≈-refl (embed m)) (λ x → embed-return (f x)))
toT∞-fmap eff  f m = ≈-refl (m >>=∞ λ x → return∞ (f x))

toT∞-sub : ∀ {π π′} (g : π ⊑π π′) {X : Set} (m : M π X) → toT∞ π′ (sub g m) ≈ toT∞ π m
toT∞-sub ⊑-pure m = ≈-refl (return∞ m)
toT∞-sub ⊑-pa   m = embed-return m
toT∞-sub ⊑-pe   m = ≈-refl (return∞ m)
toT∞-sub ⊑-act  m = ≈-refl (embed m)
toT∞-sub ⊑-ae   m = ≈-refl (embed m)
toT∞-sub ⊑-eff  m = ≈-refl m

-- Equal computations as trees are bisimilar in `T∞` (by definition, now).
eqM→≈ : ∀ π {X : Set} {m m′ : M π X} → EqM π m m′ → toT∞ π m ≈ toT∞ π m′
eqM→≈ π e = e
