{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Lawful — each grade is a lawful monad up to its equality
-- `EqM π` (bisimilarity in `T∞`), packaged once so that the recursion laws
-- are proved once for all of them.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature; call)

module Once.Metatheory.Lawful (Σ : Signature) where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Spec.Grade using (Purity; pure; act; eff)
open import Once.Spec.Effect Σ
open import Once.Metatheory.Bisim Σ
open import Once.Metatheory.Erase Σ using (toT∞-bind)
open import Once.Metatheory.Effects Σ using (M-identityˡ; M-identityʳ; M-assoc)

record Lawful (π : Purity) : Set₁ where
  field
    eq-refl   : ∀ {X} (m : M π X) → EqM π m m
    eq-sym    : ∀ {X} {m m′ : M π X} → EqM π m m′ → EqM π m′ m
    eq-trans  : ∀ {X} {m₁ m₂ m₃ : M π X} → EqM π m₁ m₂ → EqM π m₂ m₃ → EqM π m₁ m₃
    bind-cong : ∀ {X Y} {m m′ : M π X} {f g : X → M π Y} → EqM π m m′ → (∀ x → EqM π (f x) (g x))
              → EqM π (bind π m f) (bind π m′ g)
    bind-idˡ  : ∀ {X Y} (x : X) (f : X → M π Y) → EqM π (bind π (return π x) f) (f x)
    bind-idʳ  : ∀ {X} (m : M π X) → EqM π (bind π m (return π)) m
    bind-assoc : ∀ {X Y Z} (m : M π X) (f : X → M π Y) (g : Y → M π Z)
               → EqM π (bind π (bind π m f) g) (bind π m (λ x → bind π (f x) g))
    fmap-bind : ∀ {X Y} (f : X → Y) (m : M π X) → EqM π (fmap π f m) (bind π m (λ x → return π (f x)))

-- One equality at every grade (bisimilarity in `T∞`), so one proof.
lawful : ∀ π → Lawful π
lawful π = record
  { eq-refl = λ m → ≈-refl (toT∞ π m) ; eq-sym = ≈-sym ; eq-trans = ≈-trans
  ; bind-cong = λ {_} {_} {m} {m′} {f} {g} p h →
      ≈-trans (toT∞-bind π m f) (≈-trans (≈-bind p h) (≈-sym (toT∞-bind π m′ g)))
  ; bind-idˡ = M-identityˡ π ; bind-idʳ = M-identityʳ π ; bind-assoc = M-assoc π
  ; fmap-bind = λ f m → ≈-refl (toT∞ π (fmap π f m)) }
