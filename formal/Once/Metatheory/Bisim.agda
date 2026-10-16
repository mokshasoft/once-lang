{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Bisim — bisimilarity on `T∞` (`Spec.Effect`) is an
-- equivalence, `>>=∞` respects it, and `T∞` is a monad up to it.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature; call)

module Once.Metatheory.Bisim (Σ : Signature) where

open import Once.Spec.Effect Σ
open T∞ using (force)
open _≈_ using (force≈)

≈-refl  : ∀ {X} (m : T∞ X) → m ≈ m
≈-reflS : ∀ {X} (s : Step X (T∞ X)) → StepEq _≈_ s s
force≈ (≈-refl m) = ≈-reflS (force m)
≈-reflS (done x)            = done≈
≈-reflS (node (call o a k)) = node≈ λ b → ≈-refl (k b)

≈-sym  : ∀ {X} {m m′ : T∞ X} → m ≈ m′ → m′ ≈ m
≈-symS : ∀ {X} {s s′ : Step X (T∞ X)} → StepEq _≈_ s s′ → StepEq _≈_ s′ s
force≈ (≈-sym p) = ≈-symS (force≈ p)
≈-symS done≈     = done≈
≈-symS (node≈ e) = node≈ λ b → ≈-sym (e b)

≈-trans  : ∀ {X} {m₁ m₂ m₃ : T∞ X} → m₁ ≈ m₂ → m₂ ≈ m₃ → m₁ ≈ m₃
≈-transS : ∀ {X} {s₁ s₂ s₃ : Step X (T∞ X)} → StepEq _≈_ s₁ s₂ → StepEq _≈_ s₂ s₃ → StepEq _≈_ s₁ s₃
force≈ (≈-trans p q) = ≈-transS (force≈ p) (force≈ q)
≈-transS done≈     done≈     = done≈
≈-transS (node≈ e) (node≈ e′) = node≈ λ b → ≈-trans (e b) (e′ b)

-- `>>=∞` respects bisimilarity on both sides.
≈-bind  : ∀ {X Y} {m m′ : T∞ X} {f g : X → T∞ Y} → m ≈ m′ → (∀ x → f x ≈ g x) → (m >>=∞ f) ≈ (m′ >>=∞ g)
≈-bindS : ∀ {X Y} {s s′ : Step X (T∞ X)} {f g : X → T∞ Y} → StepEq _≈_ s s′ → (∀ x → f x ≈ g x)
        → StepEq _≈_ (bindStep s f) (bindStep s′ g)
force≈ (≈-bind p h) = ≈-bindS (force≈ p) h
≈-bindS {s = done x} done≈ h = force≈ (h x)
≈-bindS (node≈ e) h = node≈ λ b → ≈-bind (e b) h

-- The monad laws.
idˡ : ∀ {X Y} (x : X) (f : X → T∞ Y) → (return∞ x >>=∞ f) ≈ f x
force≈ (idˡ x f) = ≈-reflS (force (f x))

idʳ  : ∀ {X} (m : T∞ X) → (m >>=∞ return∞) ≈ m
idʳS : ∀ {X} (s : Step X (T∞ X)) → StepEq _≈_ (bindStep s return∞) s
force≈ (idʳ m) = idʳS (force m)
idʳS (done x)            = done≈
idʳS (node (call o a k)) = node≈ λ b → idʳ (k b)

assoc  : ∀ {X Y Z} (m : T∞ X) (f : X → T∞ Y) (g : Y → T∞ Z)
       → ((m >>=∞ f) >>=∞ g) ≈ (m >>=∞ λ x → f x >>=∞ g)
assocS : ∀ {X Y Z} (s : Step X (T∞ X)) (f : X → T∞ Y) (g : Y → T∞ Z)
       → StepEq _≈_ (bindStep (bindStep s f) g) (bindStep s λ x → f x >>=∞ g)
force≈ (assoc m f g) = assocS (force m) f g
assocS (done x)            f g = ≈-reflS (bindStep (force (f x)) g)
assocS (node (call o a k)) f g = node≈ λ b → assoc (k b) f g
