{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Parametricity.Comp — related computations, and the
-- semantic operations on data, between two value sets.
--
-- `Coherence.Layer` relates computations of one type by sameness; a
-- derivation read at two instances of its type variables computes over two
-- value sets, related by the relational reading of its type. Here the same
-- constructions for any relation: computations whose runs are related
-- (`RC`), closed under the graded `return`, `>>=` and sub-effecting; and the
-- fold, unfold and forcing over two functors whose constants are related by
-- an `SRel` (no equality of constants is needed, so no well-formedness).
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)

module Once.Metatheory.Parametricity.Comp (Σ : Signature) where

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Once.Spec.Grade using (Finite; fin; Purity; pure; _·p_; _⊑π_)
open import Once.Spec.Polynomial using (SFunctor; _S⊕_; _S⊗_; ⟦_⟧SF; μS; inS; sfmap)
open import Once.Spec.Effect Σ
open import Once.Spec.Domain Σ using (foldM; layerM)
open import Once.Spec.Equivalence Σ using (Observed; RelMu; inR; RelNu)
open import Once.Metatheory.Erase Σ
open import Once.Metatheory.Unfold Σ using (module Unfold)
open import Once.Metatheory.Coherence.Relation Σ
open import Once.Metatheory.Coherence.Layer Σ using (relatedFmap)

open νM using (outν)

------------------------------------------------------------------------
-- Related computations
------------------------------------------------------------------------

record RC (π π′ : Purity) {X Y : Set} (R : X → Y → Set) (m : M π X) (m′ : M π′ Y) : Set where
  constructor rc
  field runsᶜ : Related R (toT∞ π m) (toT∞ π′ m′)
open RC

module _ {X Y : Set} {R : X → Y → Set} where
  rcPure : ∀ {x y} → R x y → RC pure pure R x y
  rcPure r = rc (returnRel r)

  rcPure⁻ : ∀ {x y} → RC pure pure R x y → R x y
  rcPure⁻ p = returnRel⁻ (runsᶜ p)

  rcSubˡ : ∀ {π₀ π π′} (g : π ⊑π π₀) {m m′} → RC π π′ R m m′ → RC π₀ π′ R (sub g m) m′
  rcSubˡ g {m = m} p = rc (≈-Relatedˡ (toT∞-sub g m) (runsᶜ p))

  rcSubʳ : ∀ {π π₀ π′} (g : π′ ⊑π π₀) {m m′} → RC π π′ R m m′ → RC π π₀ R m (sub g m′)
  rcSubʳ g {m′ = m′} p = rc (≈-Relatedʳ (toT∞-sub g m′) (runsᶜ p))

  -- Observed computations are related runs.
  rcObs : ∀ π π′ {m m′} → Observed R (toT∞ π m) (toT∞ π′ m′) → RC π π′ R m m′
  rcObs π π′ o = rc (fromObserved o)

  obsRC : ∀ {π π′ m m′} → RC π π′ R m m′ → Observed R (toT∞ π m) (toT∞ π′ m′)
  obsRC p = toObserved (runsᶜ p)

module _ {X X′ Y Y′ : Set} {R : X → X′ → Set} {R′ : Y → Y′ → Set} where
  rcBindᵍ : ∀ {π₁ π₂ π₁′ π₂′} {m m′} {k : X → M π₂ Y} {k′ : X′ → M π₂′ Y′}
          → RC π₁ π₁′ R m m′ → (∀ {x x′} → R x x′ → RC π₂ π₂′ R′ (k x) (k′ x′))
          → RC (π₁ ·p π₂) (π₁′ ·p π₂′) R′ (bindᵍ π₁ π₂ m k) (bindᵍ π₁′ π₂′ m′ k′)
  rcBindᵍ {π₁} {π₂} {π₁′} {π₂′} {m} {m′} {k} {k′} p h =
    rc (≈-Relatedˡ (toT∞-bindᵍ π₁ π₂ m k) (≈-Relatedʳ (toT∞-bindᵍ π₁′ π₂′ m′ k′) (bindRel (runsᶜ p) λ s → runsᶜ (h s))))

  rcBind : ∀ {π π′} {m m′} {k : X → M π Y} {k′ : X′ → M π′ Y′}
         → RC π π′ R m m′ → (∀ {x x′} → R x x′ → RC π π′ R′ (k x) (k′ x′))
         → RC π π′ R′ (bind π m k) (bind π′ m′ k′)
  rcBind {π} {π′} {m} {m′} {k} {k′} p h =
    rc (≈-Relatedˡ (toT∞-bind π m k) (≈-Relatedʳ (toT∞-bind π′ m′ k′) (bindRel (runsᶜ p) λ s → runsᶜ (h s))))

  rcFmap : ∀ {π π′} {m m′} {f : X → Y} {f′ : X′ → Y′}
         → RC π π′ R m m′ → (∀ {x x′} → R x x′ → R′ (f x) (f′ x′))
         → RC π π′ R′ (fmap π f m) (fmap π′ f′ m′)
  rcFmap {π} {π′} {m} {m′} {f} {f′} p h =
    rc (≈-Relatedˡ (toT∞-fmap π f m) (≈-Relatedʳ (toT∞-fmap π′ f′ m′) (bindRel (runsᶜ p) λ s → returnRel (h s))))

------------------------------------------------------------------------
-- Layers between two functors
------------------------------------------------------------------------

LayerRel-map : ∀ {G G′} (q : SRel G G′) {X X′ Y Y′} {R : X → X′ → Set} {R′ : Y → Y′ → Set} {g : X → Y} {g′ : X′ → Y′}
             → (∀ {x y} → R x y → R′ (g x) (g′ y)) → ∀ {l l′} → LayerRel q R l l′ → LayerRel q R′ (sfmap G g l) (sfmap G′ g′ l′)
LayerRel-map (rK Q)   h p = p
LayerRel-map rId      h p = h p
LayerRel-map (q r⊕ k) h {inj₁ x} {inj₁ y} p = LayerRel-map q h p
LayerRel-map (q r⊕ k) h {inj₂ x} {inj₂ y} p = LayerRel-map k h p
LayerRel-map (q r⊕ k) h {inj₁ x} {inj₂ y} ()
LayerRel-map (q r⊕ k) h {inj₂ x} {inj₁ y} ()
LayerRel-map (q r⊗ k) h (p , p′) = LayerRel-map q h p , LayerRel-map k h p′

LayerRel-∀ : ∀ {G G′} (q : SRel G G′) {X Y} {R : ℕ → X → Y → Set} {l l′}
           → (∀ n → LayerRel q (R n) l l′) → LayerRel q (λ x y → ∀ n → R n x y) l l′
LayerRel-∀ (rK Q)   h = h 0
LayerRel-∀ rId      h = h
LayerRel-∀ (q r⊕ k) {l = inj₁ x} {inj₁ y} h = LayerRel-∀ q h
LayerRel-∀ (q r⊕ k) {l = inj₂ x} {inj₂ y} h = LayerRel-∀ k h
LayerRel-∀ (q r⊕ k) {l = inj₁ x} {inj₂ y} h = ⊥-elim (h 0)
LayerRel-∀ (q r⊕ k) {l = inj₂ x} {inj₁ y} h = ⊥-elim (h 0)
LayerRel-∀ (q r⊗ k) h = LayerRel-∀ q (λ n → proj₁ (h n)) , LayerRel-∀ k (λ n → proj₂ (h n))

------------------------------------------------------------------------
-- The fold of related trees
------------------------------------------------------------------------

module FoldR (π : Purity) {G G′ : SFunctor} (q : SRel G G′) {X Y : Set} (R : X → Y → Set)
             (alg : ⟦ G ⟧SF X → M π X) (alg′ : ⟦ G′ ⟧SF Y → M π Y)
             (h : ∀ {l l′} → LayerRel q R l l′ → RC π π R (alg l) (alg′ l′)) where
  foldRel  : ∀ {v v′} → RelMu q v v′ → RC π π R (foldM π G alg v) (foldM π G′ alg′ v′)
  layerRel : ∀ {H H′} (k : SRel H H′) {x x′} → LayerRel k (RelMu q) x x′
           → Related (LayerRel k R) (toT∞ π (layerM π G H alg x)) (toT∞ π (layerM π G′ H′ alg′ x′))
  foldRel {inS x} {inS x′} (inR p) =
    rc (≈-Relatedˡ (toT∞-bind π (layerM π G G alg x) alg)
         (≈-Relatedʳ (toT∞-bind π (layerM π G′ G′ alg′ x′) alg′) (bindRel (layerRel q p) λ le → runsᶜ (h le))))
  layerRel (rK Q) {x} {x′} p =
    ≈-Relatedˡ (toT∞-return π x) (≈-Relatedʳ (toT∞-return π x′) (returnRel p))
  layerRel rId p = runsᶜ (foldRel p)
  layerRel {H₁ S⊕ H₂} {H₁′ S⊕ H₂′} (k₁ r⊕ k₂) {inj₁ x} {inj₁ x′} p =
    ≈-Relatedˡ (toT∞-fmap π inj₁ (layerM π G H₁ alg x))
      (≈-Relatedʳ (toT∞-fmap π inj₁ (layerM π G′ H₁′ alg′ x′)) (relatedFmap (layerRel k₁ p) λ p → p))
  layerRel {H₁ S⊕ H₂} {H₁′ S⊕ H₂′} (k₁ r⊕ k₂) {inj₂ y} {inj₂ y′} p =
    ≈-Relatedˡ (toT∞-fmap π inj₂ (layerM π G H₂ alg y))
      (≈-Relatedʳ (toT∞-fmap π inj₂ (layerM π G′ H₂′ alg′ y′)) (relatedFmap (layerRel k₂ p) λ p → p))
  layerRel (k₁ r⊕ k₂) {inj₁ x} {inj₂ y′} ()
  layerRel (k₁ r⊕ k₂) {inj₂ y} {inj₁ x′} ()
  layerRel {H₁ S⊗ H₂} {H₁′ S⊗ H₂′} (k₁ r⊗ k₂) {x , y} {x′ , y′} (p , p′) =
    ≈-Relatedˡ (toT∞-bind π (layerM π G H₁ alg x) _)
      (≈-Relatedʳ (toT∞-bind π (layerM π G′ H₁′ alg′ x′) _)
        (bindRel (layerRel k₁ p) λ {u} {u′} r →
          ≈-Relatedˡ (toT∞-bind π (layerM π G H₂ alg y) _)
            (≈-Relatedʳ (toT∞-bind π (layerM π G′ H₂′ alg′ y′) _)
              (bindRel (layerRel k₂ p′) λ {v} {v′} r′ →
                ≈-Relatedˡ (toT∞-return π (u , v)) (≈-Relatedʳ (toT∞-return π (u′ , v′)) (returnRel (r , r′)))))))

------------------------------------------------------------------------
-- The unfold of related states, and forcing related streams
------------------------------------------------------------------------

module AnaR (f : Finite) {G G′ : SFunctor} (q : SRel G G′) {A A′ : Set} (RA : A → A′ → Set)
            (c : A → Mᶠ f (⟦ G ⟧SF A)) (c′ : A′ → Mᶠ f (⟦ G′ ⟧SF A′))
            (h : ∀ {a a′} → RA a a′ → Related (LayerRel q RA) (toT∞ (fin f) (c a)) (toT∞ (fin f) (c′ a′))) where
  private
    module U  = Unfold G
    module U′ = Unfold G′

  anaRel : ∀ n {a a′} → RA a a′ → RelNu f q n (ana f G c a) (ana f G′ c′ a′)
  anaRel zero    s = tt
  anaRel (suc n) {a} {a′} s =
    toObserved (≈-Relatedˡ (U.unfold-out≈ f c a) (≈-Relatedʳ (U′.unfold-out≈ f c′ a′)
                 (≈-Relatedˡ (toT∞-fmap (fin f) (sfmap G (ana f G c)) (c a))
                   (≈-Relatedʳ (toT∞-fmap (fin f) (sfmap G′ (ana f G′ c′)) (c′ a′))
                     (relatedFmap (h s) (LayerRel-map q (anaRel n)))))))

-- Forcing streams related to every depth gives related layer computations.
outRelR : ∀ (f : Finite) {G G′ : SFunctor} (q : SRel G G′) {v : νM f G} {v′ : νM f G′} → (∀ n → RelNu f q n v v′)
        → Related (λ l l′ → LayerRel q (λ x y → ∀ n → RelNu f q n x y) l l′) (toT∞ (fin f) (outν v)) (toT∞ (fin f) (outν v′))
outRelR f q s = Related-mono (LayerRel-∀ q) (Related-∀ λ n → fromObserved (s (suc n)))
