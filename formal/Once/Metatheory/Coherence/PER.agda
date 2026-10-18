{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Coherence.PER — sameness is a partial equivalence:
-- symmetric and transitive at every type (not reflexive: a function may tell
-- apart arguments its type calls the same).
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature; call)

module Once.Metatheory.Coherence.PER (Σ : Signature) where

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Once.Spec.Grade using (Finite; fin; mk-kind; Zero; One; Many)
open import Once.Spec.Type using (Type; var; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ; ν)
open import Once.Spec.Polynomial using (SFunctor; SK; SId; _S⊕_; _S⊗_)
open import Once.Spec.Effect Σ
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ; code)
open import Once.Spec.Equivalence Σ
open import Once.Metatheory.Trace using (WB-sym; WB-trans)

open νM using (outν)

------------------------------------------------------------------------
-- Observations
------------------------------------------------------------------------

module _ {X : Set} {R : X → X → Set} where
  Observed-sym : (∀ {x y} → R x y → R y x) → ∀ {m m′} → Observed R m m′ → Observed R m′ m
  Observed-sym s p w = WB-sym s (p w)

  Observed-trans : (∀ {x y z} → R x y → R y z → R x z) → ∀ {m₁ m₂ m₃} → Observed R m₁ m₂ → Observed R m₂ m₃ → Observed R m₁ m₃
  Observed-trans t p q w = WB-trans t (p w) (q w)

------------------------------------------------------------------------
-- Layers and streams
------------------------------------------------------------------------

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

SameNu-sym : ∀ (f : Finite) (G : SFunctor) n {v w} → SameNu f G n v w → SameNu f G n w v
SameNu-sym f G zero    p = tt
SameNu-sym f G (suc n) p = Observed-sym (LayerEq-sym G (SameNu-sym f G n)) p

SameNu-trans : ∀ (f : Finite) (G : SFunctor) n {u v w} → SameNu f G n u v → SameNu f G n v w → SameNu f G n u w
SameNu-trans f G zero    p q = tt
SameNu-trans f G (suc n) p q = Observed-trans (LayerEq-trans G (SameNu-trans f G n)) p q

------------------------------------------------------------------------
-- Sameness
------------------------------------------------------------------------

-- Symmetry and transitivity at each type, with `Same` at the argument types
-- (one type smaller) for the functions.
Same-sym    : ∀ (A : Type) {x y} → Same A x y → Same A y x
Same-trans  : ∀ (A : Type) {x y z} → Same A x y → Same A y z → Same A x z
SameM-sym   : ∀ π (A : Type) {m m′} → SameM π A m m′ → SameM π A m′ m
SameM-trans : ∀ π (A : Type) {m₁ m₂ m₃} → SameM π A m₁ m₂ → SameM π A m₂ m₃ → SameM π A m₁ m₃
SameM-sym   π A p = Observed-sym (Same-sym A) p
SameM-trans π A p q = Observed-trans (Same-trans A) p q

Same-sym (var ())
Same-sym Unit  p = tt
Same-sym Void  {()}
Same-sym Int   p = sym p
Same-sym Float p = sym p
Same-sym (μ F) p = sym p
Same-sym (A * B) {x , x′} {y , y′} (p , q) = Same-sym A p , Same-sym B q
Same-sym (A + B) {inj₁ x} {inj₁ y} p = Same-sym A p
Same-sym (A + B) {inj₂ x} {inj₂ y} p = Same-sym B p
Same-sym (A + B) {inj₁ x} {inj₂ y} ()
Same-sym (A + B) {inj₂ x} {inj₁ y} ()
Same-sym (A ⇒[ mk-kind Zero π ] B) p = SameM-sym π B p
Same-sym (A ⇒[ mk-kind One  π ] B) p = λ a a′ s → SameM-sym π B (p a′ a (Same-sym A s))
Same-sym (A ⇒[ mk-kind Many π ] B) p = λ a a′ s → SameM-sym π B (p a′ a (Same-sym A s))
Same-sym (ν F f) p n = SameNu-sym f (code F) n (p n)

Same-trans (var ())
Same-trans Unit  p q = tt
Same-trans Void  {()}
Same-trans Int   p q = trans p q
Same-trans Float p q = trans p q
Same-trans (μ F) p q = trans p q
Same-trans (A * B) {x , x′} {y , y′} {z , z′} (p , p′) (q , q′) = Same-trans A p q , Same-trans B p′ q′
Same-trans (A + B) {inj₁ x} {inj₁ y} {inj₁ z} p q = Same-trans A p q
Same-trans (A + B) {inj₂ x} {inj₂ y} {inj₂ z} p q = Same-trans B p q
Same-trans (A + B) {inj₁ x} {inj₁ y} {inj₂ z} p ()
Same-trans (A + B) {inj₁ x} {inj₂ y} () q
Same-trans (A + B) {inj₂ x} {inj₂ y} {inj₁ z} p ()
Same-trans (A + B) {inj₂ x} {inj₁ y} () q
Same-trans (A ⇒[ mk-kind Zero π ] B) p q = SameM-trans π B p q
Same-trans (A ⇒[ mk-kind One  π ] B) p q =
  λ a a′ s → SameM-trans π B (p a a′ s) (q a′ a′ (Same-trans A (Same-sym A s) s))
Same-trans (A ⇒[ mk-kind Many π ] B) p q =
  λ a a′ s → SameM-trans π B (p a a′ s) (q a′ a′ (Same-trans A (Same-sym A s) s))
Same-trans (ν F f) p q n = SameNu-trans f (code F) n (p n) (q n)
