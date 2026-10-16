{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Bisim — bisimilarity on `T∞` (`Spec.Effect`) is an
-- equivalence, `>>=∞` respects it, and `T∞` is a monad up to it. Each proof
-- walks a block by induction and continues at the block's end by
-- coinduction.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature; call)

module Once.Metatheory.Bisim (Σ : Signature) where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Once.Spec.Effect Σ
open T∞ using (force)
open _≈_ using (force≈)

≈-refl  : ∀ {X} (m : T∞ X) → m ≈ m
≈-reflB : ∀ {X} (t : T (X ⊎ T∞ X)) → BlockEq _≈_ t t
force≈ (≈-refl m) = ≈-reflB (force m)
≈-reflB (roll (done (inj₁ x)))     = return≈
≈-reflB (roll (done (inj₂ m)))     = next≈ (≈-refl m)
≈-reflB (roll (node (call o a k))) = node≈ λ b → ≈-reflB (k b)

≈-sym  : ∀ {X} {m m′ : T∞ X} → m ≈ m′ → m′ ≈ m
≈-symB : ∀ {X} {t t′ : T (X ⊎ T∞ X)} → BlockEq _≈_ t t′ → BlockEq _≈_ t′ t
force≈ (≈-sym p) = ≈-symB (force≈ p)
≈-symB return≈    = return≈
≈-symB (next≈ p)  = next≈ (≈-sym p)
≈-symB (node≈ e)  = node≈ λ b → ≈-symB (e b)

≈-trans  : ∀ {X} {m₁ m₂ m₃ : T∞ X} → m₁ ≈ m₂ → m₂ ≈ m₃ → m₁ ≈ m₃
≈-transB : ∀ {X} {t₁ t₂ t₃ : T (X ⊎ T∞ X)} → BlockEq _≈_ t₁ t₂ → BlockEq _≈_ t₂ t₃ → BlockEq _≈_ t₁ t₃
force≈ (≈-trans p q) = ≈-transB (force≈ p) (force≈ q)
≈-transB return≈    return≈     = return≈
≈-transB (next≈ p)  (next≈ q)   = next≈ (≈-trans p q)
≈-transB (node≈ e)  (node≈ e′)  = node≈ λ b → ≈-transB (e b) (e′ b)

≈-bind  : ∀ {X Y} {m m′ : T∞ X} {f g : X → T∞ Y} → m ≈ m′ → (∀ x → f x ≈ g x) → (m >>=∞ f) ≈ (m′ >>=∞ g)
≈-bindB : ∀ {X Y} {t t′ : T (X ⊎ T∞ X)} {f g : X → T∞ Y} → BlockEq _≈_ t t′ → (∀ x → f x ≈ g x)
        → BlockEq _≈_ (bindBlock t f) (bindBlock t′ g)
force≈ (≈-bind p h) = ≈-bindB (force≈ p) h
≈-bindB {t = roll (done (inj₁ x))} return≈ h = force≈ (h x)
≈-bindB (next≈ p) h = next≈ (≈-bind p h)
≈-bindB (node≈ e) h = node≈ λ b → ≈-bindB (e b) h

idˡ : ∀ {X Y} (x : X) (f : X → T∞ Y) → (return∞ x >>=∞ f) ≈ f x
force≈ (idˡ x f) = ≈-reflB (force (f x))

idʳ  : ∀ {X} (m : T∞ X) → (m >>=∞ return∞) ≈ m
idʳB : ∀ {X} (t : T (X ⊎ T∞ X)) → BlockEq _≈_ (bindBlock t return∞) t
force≈ (idʳ m) = idʳB (force m)
idʳB (roll (done (inj₁ x)))     = return≈
idʳB (roll (done (inj₂ m)))     = next≈ (idʳ m)
idʳB (roll (node (call o a k))) = node≈ λ b → idʳB (k b)

assoc  : ∀ {X Y Z} (m : T∞ X) (f : X → T∞ Y) (g : Y → T∞ Z)
       → ((m >>=∞ f) >>=∞ g) ≈ (m >>=∞ λ x → f x >>=∞ g)
assocB : ∀ {X Y Z} (t : T (X ⊎ T∞ X)) (f : X → T∞ Y) (g : Y → T∞ Z)
       → BlockEq _≈_ (bindBlock (bindBlock t f) g) (bindBlock t λ x → f x >>=∞ g)
force≈ (assoc m f g) = assocB (force m) f g
assocB (roll (done (inj₁ x)))     f g = ≈-reflB (bindBlock (force (f x)) g)
assocB (roll (done (inj₂ m)))     f g = next≈ (assoc m f g)
assocB (roll (node (call o a k))) f g = node≈ λ b → assocB (k b) f g
