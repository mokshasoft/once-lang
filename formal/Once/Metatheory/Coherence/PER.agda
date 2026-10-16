{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Coherence.PER — observing to depth `n` is a partial
-- equivalence: symmetric and transitive at every type (not reflexive: a
-- function may tell apart arguments its type calls the same). So is `Same`.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature; call)

module Once.Metatheory.Coherence.PER (Σ : Signature) where

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Once.Spec.Grade using (mk-kind; Zero; One; Many)
open import Once.Spec.Type using (Type; var; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ; ν)
open import Once.Spec.Polynomial using (SFunctor; SK; SId; _S⊕_; _S⊗_)
open import Once.Spec.Effect Σ
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ; code)
open import Once.Spec.Equivalence Σ

open T∞ using (force)
open νM using (outν)

module _ {X : Set} {R : X → X → Set} where
  UpTo-sym : ∀ n → (∀ {x y} → R x y → R y x) → ∀ {m m′} → UpTo n R m m′ → UpTo n R m′ m
  UpTo-sym zero    s p = tt
  UpTo-sym (suc n) s {m} {m′} p = go (force m) (force m′) p
    where go : ∀ a b → NodeUpTo n R a b → NodeUpTo n R b a
          go _ _ (done≈ r) = done≈ (s r)
          go _ _ (node≈ e) = node≈ λ b → UpTo-sym n s (e b)

  UpTo-trans : ∀ n → (∀ {x y z} → R x y → R y z → R x z) → ∀ {m₁ m₂ m₃} → UpTo n R m₁ m₂ → UpTo n R m₂ m₃ → UpTo n R m₁ m₃
  UpTo-trans zero    t p q = tt
  UpTo-trans (suc n) t {m₁} {m₂} {m₃} p q = go (force m₁) (force m₂) (force m₃) p q
    where go : ∀ a b c → NodeUpTo n R a b → NodeUpTo n R b c → NodeUpTo n R a c
          go _ _ _ (done≈ r) (done≈ r′) = done≈ (t r r′)
          go _ _ _ (node≈ e) (node≈ e′) = node≈ λ b → UpTo-trans n t (e b) (e′ b)

LayerEq-sym : ∀ (G : SFunctor) {X} {R : X → X → Set} → (∀ {x y} → R x y → R y x)
            → ∀ {l l′} → LayerEq G R l l′ → LayerEq G R l′ l
LayerEq-sym (SK B) s p = sym p
LayerEq-sym SId    s p = s p
LayerEq-sym (G S⊕ H) s {inj₁ x} {inj₁ y} p = LayerEq-sym G s p
LayerEq-sym (G S⊕ H) s {inj₂ x} {inj₂ y} p = LayerEq-sym H s p
LayerEq-sym (G S⊕ H) s {inj₁ x} {inj₂ y} ()
LayerEq-sym (G S⊕ H) s {inj₂ x} {inj₁ y} ()
LayerEq-sym (G S⊗ H) s (p , q) = LayerEq-sym G s p , LayerEq-sym H s q

LayerEq-trans : ∀ (G : SFunctor) {X} {R : X → X → Set} → (∀ {x y z} → R x y → R y z → R x z)
              → ∀ {l₁ l₂ l₃} → LayerEq G R l₁ l₂ → LayerEq G R l₂ l₃ → LayerEq G R l₁ l₃
LayerEq-trans (SK B) t p q = trans p q
LayerEq-trans SId    t p q = t p q
LayerEq-trans (G S⊕ H) t {inj₁ x} {inj₁ y} {inj₁ z} p q = LayerEq-trans G t p q
LayerEq-trans (G S⊕ H) t {inj₂ x} {inj₂ y} {inj₂ z} p q = LayerEq-trans H t p q
LayerEq-trans (G S⊕ H) t {inj₁ x} {inj₁ y} {inj₂ z} p ()
LayerEq-trans (G S⊕ H) t {inj₁ x} {inj₂ y} {_} () q
LayerEq-trans (G S⊕ H) t {inj₂ x} {inj₂ y} {inj₁ z} p ()
LayerEq-trans (G S⊕ H) t {inj₂ x} {inj₁ y} {_} () q
LayerEq-trans (G S⊗ H) t (p , q) (p′ , q′) = LayerEq-trans G t p p′ , LayerEq-trans H t q q′

νUpTo-sym : ∀ π (G : SFunctor) n {v w} → νUpTo π G n v w → νUpTo π G n w v
νUpTo-sym π G zero    p = tt
νUpTo-sym π G (suc n) {v} {w} p =
  UpTo-sym (suc n) (LayerEq-sym G (νUpTo-sym π G n)) {toT∞ π (outν v)} {toT∞ π (outν w)} p

νUpTo-trans : ∀ π (G : SFunctor) n {u v w} → νUpTo π G n u v → νUpTo π G n v w → νUpTo π G n u w
νUpTo-trans π G zero    p q = tt
νUpTo-trans π G (suc n) {u} {v} {w} p q =
  UpTo-trans (suc n) (LayerEq-trans G (νUpTo-trans π G n)) {toT∞ π (outν u)} {toT∞ π (outν v)} {toT∞ π (outν w)} p q

-- Symmetry and transitivity at each type, with `Same` at the argument types
-- (one type smaller) for the functions.
Same-sym   : ∀ (A : Type) {x y} → Same A x y → Same A y x
Same-trans : ∀ (A : Type) {x y z} → Same A x y → Same A y z → Same A x z
Obs-sym    : ∀ n (A : Type) {x y} → Obs n A x y → Obs n A y x
Obs-trans  : ∀ n (A : Type) {x y z} → Obs n A x y → Obs n A y z → Obs n A x z

Same-sym A s n = Obs-sym n A (s n)
Same-trans A s t n = Obs-trans n A (s n) (t n)

private
  ObsM-sym : ∀ n π (B : Type) {m m′} → ObsM n π B m m′ → ObsM n π B m′ m
  ObsM-sym n π B p = UpTo-sym n (Obs-sym n B) p
  ObsM-trans : ∀ n π (B : Type) {m₁ m₂ m₃} → ObsM n π B m₁ m₂ → ObsM n π B m₂ m₃ → ObsM n π B m₁ m₃
  ObsM-trans n π B p q = UpTo-trans n (Obs-trans n B) p q

Obs-sym n (var ())
Obs-sym n Unit  p = tt
Obs-sym n Void  {()}
Obs-sym n Int   p = sym p
Obs-sym n Float p = sym p
Obs-sym n (μ F) p = sym p
Obs-sym n (A * B) {x , x′} {y , y′} (p , q) = Obs-sym n A p , Obs-sym n B q
Obs-sym n (A + B) {inj₁ x} {inj₁ y} p = Obs-sym n A p
Obs-sym n (A + B) {inj₂ x} {inj₂ y} p = Obs-sym n B p
Obs-sym n (A + B) {inj₁ x} {inj₂ y} ()
Obs-sym n (A + B) {inj₂ x} {inj₁ y} ()
Obs-sym n (A ⇒[ mk-kind Zero π ] B) p = ObsM-sym n π B p
Obs-sym n (A ⇒[ mk-kind One  π ] B) p = λ a a′ s → ObsM-sym n π B (p a′ a (Same-sym A s))
Obs-sym n (A ⇒[ mk-kind Many π ] B) p = λ a a′ s → ObsM-sym n π B (p a′ a (Same-sym A s))
Obs-sym n (ν F π) p = νUpTo-sym π (code F) n p

Obs-trans n (var ())
Obs-trans n Unit  p q = tt
Obs-trans n Void  {()}
Obs-trans n Int   p q = trans p q
Obs-trans n Float p q = trans p q
Obs-trans n (μ F) p q = trans p q
Obs-trans n (A * B) {x , x′} {y , y′} {z , z′} (p , p′) (q , q′) = Obs-trans n A p q , Obs-trans n B p′ q′
Obs-trans n (A + B) {inj₁ x} {inj₁ y} {inj₁ z} p q = Obs-trans n A p q
Obs-trans n (A + B) {inj₂ x} {inj₂ y} {inj₂ z} p q = Obs-trans n B p q
Obs-trans n (A + B) {inj₁ x} {inj₁ y} {inj₂ z} p ()
Obs-trans n (A + B) {inj₁ x} {inj₂ y} () q
Obs-trans n (A + B) {inj₂ x} {inj₂ y} {inj₁ z} p ()
Obs-trans n (A + B) {inj₂ x} {inj₁ y} () q
Obs-trans n (A ⇒[ mk-kind Zero π ] B) p q = ObsM-trans n π B p q
Obs-trans n (A ⇒[ mk-kind One  π ] B) p q =
  λ a a′ s → ObsM-trans n π B (p a a′ s) (q a′ a′ (Same-trans A (Same-sym A s) s))
Obs-trans n (A ⇒[ mk-kind Many π ] B) p q =
  λ a a′ s → ObsM-trans n π B (p a a′ s) (q a′ a′ (Same-trans A (Same-sym A s) s))
Obs-trans n (ν F π) p q = νUpTo-trans π (code F) n p q
