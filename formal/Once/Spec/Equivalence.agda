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
-- are equal; functions take the same arguments to the same computations;
-- two trees have the same shape and the same constants and subtrees; two
-- streams are the same when they agree on every finite number of layers:
-- forcing them gives the same layer computations, with the same constants
-- and streams agreeing on one layer fewer at the recursive positions. This is
-- what a coinductive sameness would be: the greatest relation that one layer
-- preserves (`Spec.Metatheory.Sameness`), since a layer is finite and the
-- functors are polynomial.
-- Infinite objects are never compared by `≡`, nor are functions inside data.
--
-- Each type former's relation is defined once (`RelPair`, `RelSum`,
-- `RelFun`, `RelMu`, `RelStream`, `RelM`), between two value sets; `Same` is
-- their fold over a closed type (plan 0.141 P1).
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)

module Once.Spec.Equivalence (Σ : Signature) where

open import Data.Empty using (⊥)
open import Data.List using ([])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.Spec.Grade using (Finite; fin; Purity; mk-kind; Zero; One; Many)
open import Once.Spec.Type using (Type; Fun; K; Id; _⊕_; _⊗_; var; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ; ν)
open import Once.Spec.Polynomial using (SFunctor; μS; inS)
open import Once.Spec.Effect Σ using (M; T∞; toT∞; νM; module νM; LayerEq; SRel; rK; rId; _r⊕_; _r⊗_; LayerRel; eqRel)
open νM using (outν)
open import Once.Spec.Observation Σ using (World; trace)
open import Once.Spec.Trace using (_≈ᵗ⟨_⟩_)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ; code)

-- Two computations, as every world observes them, their values related by `R`.
-- (Between two value sets, for one program read at two instances of its
-- types; `R` relating a set to itself is the common case.)
Observed : ∀ {X Y : Set} → (X → Y → Set) → T∞ X → T∞ Y → Set
Observed R m m′ = ∀ (w : World) → trace w [] m ≈ᵗ⟨ R ⟩ trace w [] m′

-- The same computation of a set: observed the same, with equal values.
_≃_ : ∀ {X : Set} → T∞ X → T∞ X → Set
m ≃ m′ = Observed _≡_ m m′

infix 4 _≃_

------------------------------------------------------------------------
-- How each type former relates values, given relations for its parts.
-- Defined once: `Same` below is the fold of a closed type with these, and
-- a reading of an open type, a relation for each variable, is too.
------------------------------------------------------------------------

-- Computations of a grade: observed, the values related.
RelM : ∀ (π : Purity) {X Y : Set} → (X → Y → Set) → M π X → M π Y → Set
RelM π R m m′ = Observed R (toT∞ π m) (toT∞ π m′)

-- Pairs: related parts.
RelPair : ∀ {X X′ Y Y′ : Set} → (X → X′ → Set) → (Y → Y′ → Set) → X × Y → X′ × Y′ → Set
RelPair R S (a , b) (a′ , b′) = R a a′ × S b b′

-- Sums: the same side, related contents.
RelSum : ∀ {X X′ Y Y′ : Set} → (X → X′ → Set) → (Y → Y′ → Set) → X ⊎ Y → X′ ⊎ Y′ → Set
RelSum R S (inj₁ a) (inj₁ a′) = R a a′
RelSum R S (inj₂ b) (inj₂ b′) = S b b′
RelSum R S (inj₁ _) (inj₂ _)  = ⊥
RelSum R S (inj₂ _) (inj₁ _)  = ⊥

-- Functions: related arguments to related computations.
RelFun : ∀ (π : Purity) {X X′ Y Y′ : Set} → (X → X′ → Set) → (Y → Y′ → Set) → (X → M π Y) → (X′ → M π Y′) → Set
RelFun π R S f g = ∀ a a′ → R a a′ → RelM π S (f a) (g a′)

-- Trees: the same shape, constants related, subtrees related (`μ` values
-- are finite, so this is a relation by induction).
data RelMu {G G′ : SFunctor} (r : SRel G G′) : μS G → μS G′ → Set where
  inR : ∀ {x y} → LayerRel r (RelMu r) x y → RelMu r (inS x) (inS y)

-- One layer of a relation `R` on streams: forcing them gives layer
-- computations observed the same, with constants related by `r` and `R` at
-- the recursive positions.
OneLayerR : ∀ (f : Finite) {G G′ : SFunctor} → SRel G G′ → (νM f G → νM f G′ → Set) → νM f G → νM f G′ → Set
OneLayerR f r R v w = Observed (LayerRel r R) (toT∞ (fin f) (outν v)) (toT∞ (fin f) (outν w))

-- Two streams, to `n` layers: one layer, the streams at the recursive
-- positions agreeing to `n - 1`.
RelNu : ∀ (f : Finite) {G G′ : SFunctor} → SRel G G′ → ℕ → νM f G → νM f G′ → Set
RelNu f r zero    = λ _ _ → ⊤
RelNu f r (suc n) = OneLayerR f r (RelNu f r n)

-- Two streams: agreeing on every finite number of layers. It is the
-- greatest relation that one layer preserves (`Spec.Metatheory.Sameness`).
RelStream : ∀ (f : Finite) {G G′ : SFunctor} → SRel G G′ → νM f G → νM f G′ → Set
RelStream f r v w = ∀ n → RelNu f r n v w

-- The same, constants equal.
OneLayer : ∀ (f : Finite) (G : SFunctor) → (νM f G → νM f G → Set) → νM f G → νM f G → Set
OneLayer f G = OneLayerR f (eqRel G)

SameNu : ∀ (f : Finite) (G : SFunctor) → ℕ → νM f G → νM f G → Set
SameNu f G = RelNu f (eqRel G)

SameStream : ∀ (f : Finite) (G : SFunctor) → νM f G → νM f G → Set
SameStream f G = RelStream f (eqRel G)

------------------------------------------------------------------------
-- Sameness of a closed type's values: no world tells them apart
------------------------------------------------------------------------

Same  : (A : Type) → ⟦ A ⟧ᵛ → ⟦ A ⟧ᵛ → Set
SameM : (π : Purity) (A : Type) → M π ⟦ A ⟧ᵛ → M π ⟦ A ⟧ᵛ → Set
-- A functor's constants, the same.
SameF : (F : Fun 0) → SRel (code F) (code F)
SameM π A = RelM π (Same A)
Same (var ())
Same Unit    _ _ = ⊤
Same Void    _ _ = ⊤
Same Int     x y = x ≡ y
Same Float   x y = x ≡ y
Same (μ F)   = RelMu (SameF F)
Same (A * B) = RelPair (Same A) (Same B)
Same (A + B) = RelSum (Same A) (Same B)
Same (A ⇒[ mk-kind Zero π ] B) f g = SameM π B (f _) (g _)
Same (A ⇒[ mk-kind One  π ] B) = RelFun π (Same A) (Same B)
Same (A ⇒[ mk-kind Many π ] B) = RelFun π (Same A) (Same B)
Same (ν F f) = RelStream f (SameF F)
SameF (K A)   = rK (Same A)
SameF Id      = rId
SameF (F ⊕ G) = SameF F r⊕ SameF G
SameF (F ⊗ G) = SameF F r⊗ SameF G
