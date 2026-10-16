{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Coherence.StreamSame — sameness of streams is the
-- greatest fixed point of its one-layer step, as a coinductive sameness
-- would be.
--
-- `Step R v w`: forcing `v` and `w` gives layer computations observed the
-- same, with equal constants and `R` at the recursive positions. `Same` at
-- `ν F f` is agreement on every finite number of layers, `∀ n → SameNu n`
-- (`Spec.Equivalence`). It is
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
open import Once.Spec.Polynomial using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF)
open import Once.Spec.Effect Σ using (νM; module νM; toT∞; LayerEq)
open import Once.Spec.Equivalence Σ using (Observed; SameNu)
open import Once.Metatheory.Coherence.Relation Σ using (Related-∀; Related-mono; LayerEq-mono; fromObserved; toObserved)

open νM using (outν)

-- One layer of sameness.
Step : ∀ (f : Finite) (G : SFunctor) → (νM f G → νM f G → Set) → νM f G → νM f G → Set
Step f G R v w = Observed (LayerEq G R) (toT∞ (fin f) (outν v)) (toT∞ (fin f) (outν w))

-- Sameness of streams, as `Same (ν F f)` states it.
SameS : ∀ (f : Finite) (G : SFunctor) → νM f G → νM f G → Set
SameS f G v w = ∀ n → SameNu f G n v w

-- A polynomial layer commutes with `∀ n`.
LayerEq-∀ : ∀ (G : SFunctor) {X : Set} {R : ℕ → X → X → Set} {l l′ : ⟦ G ⟧SF X}
          → (∀ n → LayerEq G (R n) l l′) → LayerEq G (λ x y → ∀ n → R n x y) l l′
LayerEq-∀ (SK B) p = p zero
LayerEq-∀ SId    p = p
LayerEq-∀ (G S⊕ H) {l = inj₁ x} {inj₁ y} p = LayerEq-∀ G p
LayerEq-∀ (G S⊕ H) {l = inj₂ x} {inj₂ y} p = LayerEq-∀ H p
LayerEq-∀ (G S⊕ H) {l = inj₁ x} {inj₂ y} p = ⊥-elim (p zero)
LayerEq-∀ (G S⊕ H) {l = inj₂ x} {inj₁ y} p = ⊥-elim (p zero)
LayerEq-∀ (G S⊗ H) p = LayerEq-∀ G (λ n → proj₁ (p n)) , LayerEq-∀ H (λ n → proj₂ (p n))

module _ (f : Finite) (G : SFunctor) where
  private
    Step-mono : ∀ {R R′ : νM f G → νM f G → Set} → (∀ {v w} → R v w → R′ v w) → ∀ {v w} → Step f G R v w → Step f G R′ v w
    Step-mono h p = toObserved (Related-mono (LayerEq-mono G h) (fromObserved p))

  -- Same streams are the same one layer down …
  same-out : ∀ {v w} → SameS f G v w → Step f G (SameS f G) v w
  same-out {v} {w} s = toObserved {m = toT∞ (fin f) (outν v)} {toT∞ (fin f) (outν w)} (Related-mono (LayerEq-∀ G) (Related-∀ λ n → fromObserved (s (suc n))))

  -- … and streams the same one layer down are the same.
  same-in : ∀ {v w} → Step f G (SameS f G) v w → SameS f G v w
  same-in p zero    = tt
  same-in {v} {w} p (suc n) = Step-mono (λ s → s n) {v} {w} p

  -- Any relation that is preserved by one layer lies inside sameness.
  same-coind : ∀ (R : νM f G → νM f G → Set) → (∀ {v w} → R v w → Step f G R v w)
             → ∀ {v w} → R v w → SameS f G v w
  same-coind R h r zero    = tt
  same-coind R h {v} {w} r (suc n) = Step-mono (λ r′ → same-coind R h r′ n) {v} {w} (h r)
