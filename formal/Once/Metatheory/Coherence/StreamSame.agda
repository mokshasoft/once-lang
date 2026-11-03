{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Coherence.StreamSame — sameness of streams is the
-- greatest fixed point of its one-layer step, as a coinductive sameness
-- would be.
--
-- `Step R v w`: forcing `v` and `w` gives layer computations observed the
-- same, with constants related by `q` and `R` at the recursive positions.
-- The relation of streams is agreement on every finite number of layers,
-- `∀ n → RelNu n` (`Spec.Equivalence`; `Same` at `ν F f` is the one with
-- `q` relating constants by `Same`). It is
--   * a fixed point: `Same ⇔ Step Same` (`same-out`, `same-in`), and
--   * the greatest one: every `R ⊆ Step R` lies inside it (`same-coind`).
-- The fixed point needs `Step` to commute with `∀ n`: a layer is finite, so
-- in each world it is one run with one pair of values (`Related-∀`), and
-- the functor is polynomial (`LayerEq-∀`).
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)

module Once.Metatheory.Coherence.StreamSame (Σ : Signature) where

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Once.Spec.Grade using (Finite; fin)
open import Once.Spec.Polynomial using (SFunctor; ⟦_⟧SF)
open import Once.Spec.Effect Σ using (νM; module νM; toT∞; SRel; rK; rId; _r⊕_; _r⊗_; LayerRel)
open import Once.Spec.Equivalence Σ using (Observed; RelNu; RelStream)
open import Once.Metatheory.Coherence.Relation Σ using (Related-∀; Related-mono; fromObserved; toObserved)

open νM using (outν)

module _ {G G′ : SFunctor} (q : SRel G G′) where
  -- A layer, its positions related by a larger relation.
  LayerRel-map : ∀ {X Y} {R R′ : X → Y → Set} → (∀ {x y} → R x y → R′ x y)
               → ∀ {H H′} (h : SRel H H′) {l l′} → LayerRel h R l l′ → LayerRel h R′ l l′
  LayerRel-map k (rK Q)   p = p
  LayerRel-map k rId      p = k p
  LayerRel-map k (g r⊕ h) {inj₁ x} {inj₁ y} p = LayerRel-map k g p
  LayerRel-map k (g r⊕ h) {inj₂ x} {inj₂ y} p = LayerRel-map k h p
  LayerRel-map k (g r⊕ h) {inj₁ x} {inj₂ y} ()
  LayerRel-map k (g r⊕ h) {inj₂ x} {inj₁ y} ()
  LayerRel-map k (g r⊗ h) (p , p′) = LayerRel-map k g p , LayerRel-map k h p′

  -- A polynomial layer commutes with `∀ n`.
  LayerRel-∀ : ∀ {H H′} (h : SRel H H′) {X Y : Set} {R : ℕ → X → Y → Set} {l l′}
             → (∀ n → LayerRel h (R n) l l′) → LayerRel h (λ x y → ∀ n → R n x y) l l′
  LayerRel-∀ (rK Q) p = p zero
  LayerRel-∀ rId    p = p
  LayerRel-∀ (g r⊕ h) {l = inj₁ x} {inj₁ y} p = LayerRel-∀ g p
  LayerRel-∀ (g r⊕ h) {l = inj₂ x} {inj₂ y} p = LayerRel-∀ h p
  LayerRel-∀ (g r⊕ h) {l = inj₁ x} {inj₂ y} p = ⊥-elim (p zero)
  LayerRel-∀ (g r⊕ h) {l = inj₂ x} {inj₁ y} p = ⊥-elim (p zero)
  LayerRel-∀ (g r⊗ h) p = LayerRel-∀ g (λ n → proj₁ (p n)) , LayerRel-∀ h (λ n → proj₂ (p n))

module _ (f : Finite) {G G′ : SFunctor} (q : SRel G G′) where
  -- One layer of the relation.
  Step : (νM f G → νM f G′ → Set) → νM f G → νM f G′ → Set
  Step R v w = Observed (LayerRel q R) (toT∞ (fin f) (outν v)) (toT∞ (fin f) (outν w))

  private
    Step-mono : ∀ {R R′ : νM f G → νM f G′ → Set} → (∀ {v w} → R v w → R′ v w) → ∀ {v w} → Step R v w → Step R′ v w
    Step-mono h p = toObserved (Related-mono (LayerRel-map q h q) (fromObserved p))

  -- Related streams are related one layer down …
  same-out : ∀ {v w} → RelStream f q v w → Step (RelStream f q) v w
  same-out {v} {w} s = toObserved {m = toT∞ (fin f) (outν v)} {toT∞ (fin f) (outν w)}
                         (Related-mono (LayerRel-∀ q q) (Related-∀ λ n → fromObserved (s (suc n))))

  -- … and streams related one layer down are related.
  same-in : ∀ {v w} → Step (RelStream f q) v w → RelStream f q v w
  same-in p zero    = tt
  same-in {v} {w} p (suc n) = Step-mono (λ s → s n) {v} {w} p

  -- Any relation that is preserved by one layer lies inside it.
  same-coind : ∀ (R : νM f G → νM f G′ → Set) → (∀ {v w} → R v w → Step R v w)
             → ∀ {v w} → R v w → RelStream f q v w
  same-coind R h r zero    = tt
  same-coind R h {v} {w} r (suc n) = Step-mono (λ r′ → same-coind R h r′ n) {v} {w} (h r)
