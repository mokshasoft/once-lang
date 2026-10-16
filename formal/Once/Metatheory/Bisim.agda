{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Bisim — bisimilarity of streams is an equivalence, and
-- `T∞` (the stream of blocks) is a monad up to it.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature; call)

module Once.Metatheory.Bisim (Σ : Signature) where

open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Once.Spec.Grade using (Finite; pureᶠ; actᶠ)
open import Once.Spec.Polynomial using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF)
open import Once.Spec.Effect Σ

open νM using (outν)
open _≈ν_ using (force≈)

-- The leaves of a `T∞` block: the value, or the rest of the computation.
pattern return≈ = done≈ refl
pattern next≈ p = done≈ p

------------------------------------------------------------------------
-- An equivalence, for every stream
------------------------------------------------------------------------

module _ {G : SFunctor} where
  ≈ν-refl  : ∀ {f : Finite} (v : νM f G) → v ≈ν v
  ≈ν-reflE : ∀ (f : Finite) (l : Mᶠ f (⟦ G ⟧SF (νM f G))) → EqLayer f (LayerEq G _≈ν_) l l
  ≈ν-reflB : ∀ (t : T (⟦ G ⟧SF (νM actᶠ G))) → BlockEq (LayerEq G _≈ν_) t t
  ≈ν-reflL : ∀ {f : Finite} (H : SFunctor) (l : ⟦ H ⟧SF (νM f G)) → LayerEq H _≈ν_ l l
  force≈ (≈ν-refl {f} v) = ≈ν-reflE f (outν v)
  ≈ν-reflE pureᶠ l = ≈ν-reflL G l
  ≈ν-reflE actᶠ  t = ≈ν-reflB t
  ≈ν-reflB (roll (done l))            = done≈ (≈ν-reflL G l)
  ≈ν-reflB (roll (node (call o a k))) = node≈ λ b → ≈ν-reflB (k b)
  ≈ν-reflL (SK B)     x        = refl
  ≈ν-reflL SId        v        = ≈ν-refl v
  ≈ν-reflL (H₁ S⊕ H₂) (inj₁ x) = ≈ν-reflL H₁ x
  ≈ν-reflL (H₁ S⊕ H₂) (inj₂ y) = ≈ν-reflL H₂ y
  ≈ν-reflL (H₁ S⊗ H₂) (x , y)  = ≈ν-reflL H₁ x , ≈ν-reflL H₂ y

  ≈ν-sym  : ∀ {f : Finite} {v w : νM f G} → v ≈ν w → w ≈ν v
  ≈ν-symE : ∀ (f : Finite) {l l′ : Mᶠ f (⟦ G ⟧SF (νM f G))} → EqLayer f (LayerEq G _≈ν_) l l′ → EqLayer f (LayerEq G _≈ν_) l′ l
  ≈ν-symB : ∀ {t t′ : T (⟦ G ⟧SF (νM actᶠ G))} → BlockEq (LayerEq G _≈ν_) t t′ → BlockEq (LayerEq G _≈ν_) t′ t
  ≈ν-symL : ∀ {f : Finite} (H : SFunctor) {l l′ : ⟦ H ⟧SF (νM f G)} → LayerEq H _≈ν_ l l′ → LayerEq H _≈ν_ l′ l
  force≈ (≈ν-sym {f} p) = ≈ν-symE f (force≈ p)
  ≈ν-symE pureᶠ p = ≈ν-symL G p
  ≈ν-symE actᶠ  p = ≈ν-symB p
  ≈ν-symB (done≈ p) = done≈ (≈ν-symL G p)
  ≈ν-symB (node≈ e) = node≈ λ b → ≈ν-symB (e b)
  ≈ν-symL (SK B)     p = sym p
  ≈ν-symL SId        p = ≈ν-sym p
  ≈ν-symL (H₁ S⊕ H₂) {inj₁ x} {inj₁ y} p = ≈ν-symL H₁ p
  ≈ν-symL (H₁ S⊕ H₂) {inj₂ x} {inj₂ y} p = ≈ν-symL H₂ p
  ≈ν-symL (H₁ S⊕ H₂) {inj₁ x} {inj₂ y} ()
  ≈ν-symL (H₁ S⊕ H₂) {inj₂ x} {inj₁ y} ()
  ≈ν-symL (H₁ S⊗ H₂) (p , q) = ≈ν-symL H₁ p , ≈ν-symL H₂ q

  ≈ν-trans  : ∀ {f : Finite} {u v w : νM f G} → u ≈ν v → v ≈ν w → u ≈ν w
  ≈ν-transE : ∀ (f : Finite) {l₁ l₂ l₃ : Mᶠ f (⟦ G ⟧SF (νM f G))}
            → EqLayer f (LayerEq G _≈ν_) l₁ l₂ → EqLayer f (LayerEq G _≈ν_) l₂ l₃ → EqLayer f (LayerEq G _≈ν_) l₁ l₃
  ≈ν-transB : ∀ {t₁ t₂ t₃ : T (⟦ G ⟧SF (νM actᶠ G))}
            → BlockEq (LayerEq G _≈ν_) t₁ t₂ → BlockEq (LayerEq G _≈ν_) t₂ t₃ → BlockEq (LayerEq G _≈ν_) t₁ t₃
  ≈ν-transL : ∀ {f : Finite} (H : SFunctor) {l₁ l₂ l₃ : ⟦ H ⟧SF (νM f G)}
            → LayerEq H _≈ν_ l₁ l₂ → LayerEq H _≈ν_ l₂ l₃ → LayerEq H _≈ν_ l₁ l₃
  force≈ (≈ν-trans {f} p q) = ≈ν-transE f (force≈ p) (force≈ q)
  ≈ν-transE pureᶠ p q = ≈ν-transL G p q
  ≈ν-transE actᶠ  p q = ≈ν-transB p q
  ≈ν-transB (done≈ p) (done≈ q)  = done≈ (≈ν-transL G p q)
  ≈ν-transB (node≈ e) (node≈ e′) = node≈ λ b → ≈ν-transB (e b) (e′ b)
  ≈ν-transL (SK B)     p q = trans p q
  ≈ν-transL SId        p q = ≈ν-trans p q
  ≈ν-transL (H₁ S⊕ H₂) {inj₁ x} {inj₁ y} {inj₁ z} p q = ≈ν-transL H₁ p q
  ≈ν-transL (H₁ S⊕ H₂) {inj₂ x} {inj₂ y} {inj₂ z} p q = ≈ν-transL H₂ p q
  ≈ν-transL (H₁ S⊕ H₂) {inj₁ x} {inj₁ y} {inj₂ z} p ()
  ≈ν-transL (H₁ S⊕ H₂) {inj₁ x} {inj₂ y} () q
  ≈ν-transL (H₁ S⊕ H₂) {inj₂ x} {inj₂ y} {inj₁ z} p ()
  ≈ν-transL (H₁ S⊕ H₂) {inj₂ x} {inj₁ y} () q
  ≈ν-transL (H₁ S⊗ H₂) (p , p′) (q , q′) = ≈ν-transL H₁ p q , ≈ν-transL H₂ p′ q′

------------------------------------------------------------------------
-- `T∞`: its bisimilarity is the stream's at `K X ⊕ Id`
------------------------------------------------------------------------

≈-refl  : ∀ {X} (m : T∞ X) → m ≈ m
≈-refl {X} = ≈ν-refl {G = SK X S⊕ SId}

≈-reflB : ∀ {X} (t : T (X ⊎ T∞ X)) → BlockEq (LayerEq (SK X S⊕ SId) _≈_) t t
≈-reflB {X} = ≈ν-reflB {G = SK X S⊕ SId}

≈-sym  : ∀ {X} {m m′ : T∞ X} → m ≈ m′ → m′ ≈ m
≈-sym {X} = ≈ν-sym {G = SK X S⊕ SId}

≈-symB : ∀ {X} {t t′ : T (X ⊎ T∞ X)} → BlockEq (LayerEq (SK X S⊕ SId) _≈_) t t′ → BlockEq (LayerEq (SK X S⊕ SId) _≈_) t′ t
≈-symB {X} = ≈ν-symB {G = SK X S⊕ SId}

≈-trans  : ∀ {X} {m₁ m₂ m₃ : T∞ X} → m₁ ≈ m₂ → m₂ ≈ m₃ → m₁ ≈ m₃
≈-trans {X} = ≈ν-trans {G = SK X S⊕ SId}

≈-transB : ∀ {X} {t₁ t₂ t₃ : T (X ⊎ T∞ X)}
         → BlockEq (LayerEq (SK X S⊕ SId) _≈_) t₁ t₂ → BlockEq (LayerEq (SK X S⊕ SId) _≈_) t₂ t₃ → BlockEq (LayerEq (SK X S⊕ SId) _≈_) t₁ t₃
≈-transB {X} = ≈ν-transB {G = SK X S⊕ SId}

-- `T∞`'s blocks, related.
_≈B_ : ∀ {X} → T (X ⊎ T∞ X) → T (X ⊎ T∞ X) → Set
_≈B_ {X} = BlockEq (LayerEq (SK X S⊕ SId) _≈_)

------------------------------------------------------------------------
-- The monad laws, up to bisimilarity
------------------------------------------------------------------------

≈-bind  : ∀ {X Y} {m m′ : T∞ X} {f g : X → T∞ Y} → m ≈ m′ → (∀ x → f x ≈ g x) → (m >>=∞ f) ≈ (m′ >>=∞ g)
≈-bindB : ∀ {X Y} {t t′ : T (X ⊎ T∞ X)} {f g : X → T∞ Y} → t ≈B t′ → (∀ x → f x ≈ g x)
        → bindBlock t f ≈B bindBlock t′ g
force≈ (≈-bind p h) = ≈-bindB (force≈ p) h
≈-bindB {t = roll (done (inj₁ x))} {roll (done (inj₁ .x))} return≈ h = force≈ (h x)
≈-bindB {t = roll (done (inj₁ x))} {roll (done (inj₂ _))} (done≈ ()) h
≈-bindB {t = roll (done (inj₂ m))} {roll (done (inj₁ _))} (done≈ ()) h
≈-bindB {t = roll (done (inj₂ m))} {roll (done (inj₂ m′))} (next≈ p) h = next≈ (≈-bind p h)
≈-bindB (node≈ e) h = node≈ λ b → ≈-bindB (e b) h

idˡ : ∀ {X Y} (x : X) (f : X → T∞ Y) → (return∞ x >>=∞ f) ≈ f x
force≈ (idˡ x f) = ≈-reflB (force (f x))

idʳ  : ∀ {X} (m : T∞ X) → (m >>=∞ return∞) ≈ m
idʳB : ∀ {X} (t : T (X ⊎ T∞ X)) → bindBlock t return∞ ≈B t
force≈ (idʳ m) = idʳB (force m)
idʳB (roll (done (inj₁ x)))     = return≈
idʳB (roll (done (inj₂ m)))     = next≈ (idʳ m)
idʳB (roll (node (call o a k))) = node≈ λ b → idʳB (k b)

assoc  : ∀ {X Y Z} (m : T∞ X) (f : X → T∞ Y) (g : Y → T∞ Z)
       → ((m >>=∞ f) >>=∞ g) ≈ (m >>=∞ λ x → f x >>=∞ g)
assocB : ∀ {X Y Z} (t : T (X ⊎ T∞ X)) (f : X → T∞ Y) (g : Y → T∞ Z)
       → bindBlock (bindBlock t f) g ≈B bindBlock t (λ x → f x >>=∞ g)
force≈ (assoc m f g) = assocB (force m) f g
assocB (roll (done (inj₁ x)))     f g = ≈-reflB (bindBlock (force (f x)) g)
assocB (roll (done (inj₂ m)))     f g = next≈ (assoc m f g)
assocB (roll (node (call o a k))) f g = node≈ λ b → assocB (k b) f g
