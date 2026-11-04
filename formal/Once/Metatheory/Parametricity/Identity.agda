{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Parametricity.Identity — identity extension: the
-- relational reading of an open type at one instance, each variable related
-- by sameness, relates exactly what sameness of the instance relates
-- (`Spec.Metatheory.Sameness.rel-same`/`same-rel`).
--
-- `Rel` and `Same` are the same fold of the type formers' relations
-- (`Spec.Equivalence`), differing only at a variable, where `Rel` reads
-- `Same (σ i)`: so the two directions go together by recursion on the type
-- (together, because an arrow's domain turns them round), and a functor's
-- constants are compared as relations (`_⊆ᶜ_`), through which trees and
-- streams are monotone.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)

module Once.Metatheory.Parametricity.Identity (Σ : Signature) where

open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Once.Spec.Grade using (mk-kind; Zero; One; Many)
open import Once.Spec.Type using (Ty; Fun; TySub; _⟨_⟩; _⟨_⟩F; var; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ; ν; K; Id; _⊕_; _⊗_)
open import Once.Spec.Effect Σ using (SRel; rK; rId; _r⊕_; _r⊗_; LayerRel)
open import Once.Spec.Equivalence Σ
open import Once.Metatheory.Trace using (WB-mono)
open import Once.Metatheory.Coherence.Layer Σ using (_⊆ᶜ_; RelNu-mono)

-- Observed computations, the values' relation enlarged.
Observed-mono : ∀ {X Y : Set} {R R′ : X → Y → Set} → (∀ {x y} → R x y → R′ x y)
              → ∀ {m m′} → Observed R m m′ → Observed R′ m m′
Observed-mono h p w = WB-mono h (p w)

-- Trees, the constants' relation enlarged.
module _ {G G′} (q q′ : SRel G G′) (c : q ⊆ᶜ q′) where
  RelMu-mono    : ∀ {x y} → RelMu q x y → RelMu q′ x y
  LayerMu-mono  : ∀ {H H′} (k k′ : SRel H H′) → k ⊆ᶜ k′ → ∀ {l l′} → LayerRel k (RelMu q) l l′ → LayerRel k′ (RelMu q′) l l′
  RelMu-mono (inR p) = inR (LayerMu-mono q q′ c p)
  LayerMu-mono (rK Q)   (rK Q′)    d p = d p
  LayerMu-mono rId      rId        d p = RelMu-mono p
  LayerMu-mono (g r⊕ h) (g′ r⊕ h′) (d , e) {inj₁ x} {inj₁ y} p = LayerMu-mono g g′ d p
  LayerMu-mono (g r⊕ h) (g′ r⊕ h′) (d , e) {inj₂ x} {inj₂ y} p = LayerMu-mono h h′ e p
  LayerMu-mono (g r⊕ h) (g′ r⊕ h′) d {inj₁ x} {inj₂ y} ()
  LayerMu-mono (g r⊕ h) (g′ r⊕ h′) d {inj₂ x} {inj₁ y} ()
  LayerMu-mono (g r⊗ h) (g′ r⊗ h′) (d , e) (p , p′) = LayerMu-mono g g′ d p , LayerMu-mono h h′ e p′

------------------------------------------------------------------------
-- Identity extension
------------------------------------------------------------------------

rel-same : ∀ {m} (A : Ty m) (σ : TySub m 0) {x y} → Rel A (sameSub σ) x y → Same (A ⟨ σ ⟩) x y
same-rel : ∀ {m} (A : Ty m) (σ : TySub m 0) {x y} → Same (A ⟨ σ ⟩) x y → Rel A (sameSub σ) x y
relF⊆    : ∀ {m} (F : Fun m) (σ : TySub m 0) → RelF F (sameSub σ) ⊆ᶜ SameF (F ⟨ σ ⟩F)
sameF⊆   : ∀ {m} (F : Fun m) (σ : TySub m 0) → SameF (F ⟨ σ ⟩F) ⊆ᶜ RelF F (sameSub σ)

rel-same (var i) σ p = p
rel-same Unit    σ p = p
rel-same Void    σ p = p
rel-same Int     σ p = p
rel-same Float   σ p = p
rel-same (μ F)   σ p = RelMu-mono _ _ (relF⊆ F σ) p
rel-same (A * B) σ {a , b} {a′ , b′} (p , q) = rel-same A σ p , rel-same B σ q
rel-same (A + B) σ {inj₁ a} {inj₁ a′} p = rel-same A σ p
rel-same (A + B) σ {inj₂ b} {inj₂ b′} p = rel-same B σ p
rel-same (A + B) σ {inj₁ a} {inj₂ b′} ()
rel-same (A + B) σ {inj₂ b} {inj₁ a′} ()
rel-same (A ⇒[ mk-kind Zero π ] B) σ p = Observed-mono (rel-same B σ) p
rel-same (A ⇒[ mk-kind One  π ] B) σ p a a′ s = Observed-mono (rel-same B σ) (p a a′ (same-rel A σ s))
rel-same (A ⇒[ mk-kind Many π ] B) σ p a a′ s = Observed-mono (rel-same B σ) (p a a′ (same-rel A σ s))
rel-same (ν F f) σ p n = RelNu-mono f _ _ (relF⊆ F σ) n (p n)

same-rel (var i) σ p = p
same-rel Unit    σ p = p
same-rel Void    σ p = p
same-rel Int     σ p = p
same-rel Float   σ p = p
same-rel (μ F)   σ p = RelMu-mono _ _ (sameF⊆ F σ) p
same-rel (A * B) σ {a , b} {a′ , b′} (p , q) = same-rel A σ p , same-rel B σ q
same-rel (A + B) σ {inj₁ a} {inj₁ a′} p = same-rel A σ p
same-rel (A + B) σ {inj₂ b} {inj₂ b′} p = same-rel B σ p
same-rel (A + B) σ {inj₁ a} {inj₂ b′} ()
same-rel (A + B) σ {inj₂ b} {inj₁ a′} ()
same-rel (A ⇒[ mk-kind Zero π ] B) σ p = Observed-mono (same-rel B σ) p
same-rel (A ⇒[ mk-kind One  π ] B) σ p a a′ s = Observed-mono (same-rel B σ) (p a a′ (rel-same A σ s))
same-rel (A ⇒[ mk-kind Many π ] B) σ p a a′ s = Observed-mono (same-rel B σ) (p a a′ (rel-same A σ s))
same-rel (ν F f) σ p n = RelNu-mono f _ _ (sameF⊆ F σ) n (p n)

relF⊆ (K A)   σ = rel-same A σ
relF⊆ Id      σ = tt
relF⊆ (F ⊕ G) σ = relF⊆ F σ , relF⊆ G σ
relF⊆ (F ⊗ G) σ = relF⊆ F σ , relF⊆ G σ

sameF⊆ (K A)   σ = same-rel A σ
sameF⊆ Id      σ = tt
sameF⊆ (F ⊕ G) σ = sameF⊆ F σ , sameF⊆ G σ
sameF⊆ (F ⊗ G) σ = sameF⊆ F σ , sameF⊆ G σ
