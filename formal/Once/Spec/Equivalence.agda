{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Equivalence — when two meanings are the same.
--
-- Two computations are the same when no world tells them apart: in every
-- world their traces are weakly bisimilar, with ends related by sameness of
-- the values (`Spec.Observation`). This is the kernel of observation, lifted
-- by sameness of values, so it respects `return` and `>>=`. Every grade is
-- observed through its embedding into `T∞`; where a block of calls ends is
-- not observed.
--
-- Two values of a type are the same by recursion on the type: base values
-- are equal; functions take the same arguments to the same computations; two
-- streams are the same when they agree on every finite number of layers:
-- forcing them gives the same layer computations, with equal constants and
-- streams agreeing on one layer fewer at the recursive positions. This is
-- what a coinductive sameness would be: the greatest relation that one layer
-- preserves (`Spec.Metatheory.Sameness`), since a layer is finite and the
-- functors are polynomial.
-- Infinite objects are never compared by `≡`.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)

module Once.Spec.Equivalence (Σ : Signature) where

open import Data.Empty using (⊥)
open import Data.List using ([])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.Spec.Grade using (Finite; fin; Purity; mk-kind; Zero; One; Many)
open import Once.Spec.Type using (Type; var; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ; ν)
open import Once.Spec.Polynomial using (SFunctor)
open import Once.Spec.Effect Σ using (M; T∞; toT∞; νM; module νM; LayerEq)
open νM using (outν)
open import Once.Spec.Observation Σ using (World; trace; _≈ᵗ⟨_⟩_)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ; code)

-- Two computations, as every world observes them, their values related by `R`.
Observed : ∀ {X : Set} → (X → X → Set) → T∞ X → T∞ X → Set
Observed R m m′ = ∀ (w : World) → trace w [] m ≈ᵗ⟨ R ⟩ trace w [] m′

-- The same computation of a set: observed the same, with equal values.
_≃_ : ∀ {X : Set} → T∞ X → T∞ X → Set
m ≃ m′ = Observed _≡_ m m′

infix 4 _≃_

-- Two streams, to `n` layers: forcing them gives the same layer
-- computations, the streams at the recursive positions agreeing to `n - 1`.
SameNu : ∀ (f : Finite) (G : SFunctor) → ℕ → νM f G → νM f G → Set
SameNu f G zero    v w = ⊤
SameNu f G (suc n) v w = Observed (LayerEq G (SameNu f G n)) (toT∞ (fin f) (outν v)) (toT∞ (fin f) (outν w))

-- Two streams: agreeing on every finite number of layers. It is the
-- greatest relation that one layer preserves (`Spec.Metatheory.Sameness`).
SameStream : ∀ (f : Finite) (G : SFunctor) → νM f G → νM f G → Set
SameStream f G v w = ∀ n → SameNu f G n v w

-- No world tells them apart.
Same  : (A : Type) → ⟦ A ⟧ᵛ → ⟦ A ⟧ᵛ → Set
SameM : (π : Purity) (A : Type) → M π ⟦ A ⟧ᵛ → M π ⟦ A ⟧ᵛ → Set
SameM π A m m′ = Observed (Same A) (toT∞ π m) (toT∞ π m′)
Same (var ())
Same Unit    _ _ = ⊤
Same Void    _ _ = ⊤
Same Int     x y = x ≡ y
Same Float   x y = x ≡ y
Same (μ F)   x y = x ≡ y
Same (A * B) (a , b) (a′ , b′) = Same A a a′ × Same B b b′
Same (A + B) (inj₁ a) (inj₁ a′) = Same A a a′
Same (A + B) (inj₂ b) (inj₂ b′) = Same B b b′
Same (A + B) (inj₁ _) (inj₂ _)  = ⊥
Same (A + B) (inj₂ _) (inj₁ _)  = ⊥
Same (A ⇒[ mk-kind Zero π ] B) f g = SameM π B (f _) (g _)
Same (A ⇒[ mk-kind One  π ] B) f g = ∀ a a′ → Same A a a′ → SameM π B (f a) (g a′)
Same (A ⇒[ mk-kind Many π ] B) f g = ∀ a a′ → Same A a a′ → SameM π B (f a) (g a′)
Same (ν F f) v w = SameStream f (code F) v w
