{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Coherence.Conv — a coercion along `A <: B`
-- (`Spec.Domain.conv`) maps the same values to the same values: at arrows
-- it composes with related computations; at codata it re-grades every
-- layer (`subν`): each layer's computation is the old one mapped, up to
-- bisimilarity, so the layers stay related.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature; call)

module Once.Metatheory.Coherence.Conv (Σ : Signature) where

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Once.Spec.Grade using (Finite; pureᶠ; actᶠ; fin; pure; act; eff; mk-kind; Zero; One; Many; _⊑π_; ⊑-pure; ⊑-pa; ⊑-act)
open import Once.Spec.Type using (Ty; TySub; _⟨_⟩; _⟨_⟩F)
open import Once.Spec.Sub
open import Once.Spec.Polynomial using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF)
open import Once.Spec.Effect Σ
open import Once.Spec.Domain Σ
open import Once.Spec.Equivalence Σ
open import Once.Metatheory.Coherence.Relation Σ
open import Once.Metatheory.Coherence.Layer Σ

open _≈ν_ using (force≈)
open νM using (outν)
open import Once.Metatheory.Bisim Σ using (return≈)

------------------------------------------------------------------------
-- Re-grading codata
------------------------------------------------------------------------

module _ (G : SFunctor) where
  -- The coalgebra of the `pure → act` coercion: each layer, as a block with no call.
  private
    up : νM pureᶠ G → T (⟦ G ⟧SF (νM pureᶠ G))
    up u = returnT (outν u)

  lpaRel : ∀ H {R R′} → (∀ {x y} → R x y → R′ (subν ⊑-pa G x) (subν ⊑-pa G y)) → ∀ {l l′}
         → LayerEq H R l l′ → LayerEq H R′ (mapA G H up l) (mapA G H up l′)
  lpaRel (SK B)     h p = p
  lpaRel SId        h p = h p
  lpaRel (H₁ S⊕ H₂) h {inj₁ x} {inj₁ y} p = lpaRel H₁ h p
  lpaRel (H₁ S⊕ H₂) h {inj₂ x} {inj₂ y} p = lpaRel H₂ h p
  lpaRel (H₁ S⊕ H₂) h {inj₁ x} {inj₂ y} ()
  lpaRel (H₁ S⊕ H₂) h {inj₂ x} {inj₁ y} ()
  lpaRel (H₁ S⊗ H₂) h (p , q) = lpaRel H₁ h p , lpaRel H₂ h q

  subνUp : ∀ {f f′} (g : fin f ⊑π fin f′) n {v v′} → SameNu f G n v v′ → SameNu f′ G n (subν g G v) (subν g G v′)

  private
    -- The re-graded layer computation is the old one, mapped.
    pa≈ : ∀ (v : νM pureᶠ G) → toT∞ act (outν (subν ⊑-pa G v)) ≈ (toT∞ pure (outν v) >>=∞ λ l → return∞ (mapA G G up l))
    force≈ (pa≈ v) = return≈

  subνUp ⊑-pure n p = p
  subνUp ⊑-act  n p = p
  subνUp ⊑-pa zero    p = tt
  subνUp ⊑-pa (suc n) {v} {v′} p =
    toObserved (≈-Relatedˡ (pa≈ v) (≈-Relatedʳ (pa≈ v′) (relatedFmap (fromObserved p) (lpaRel G (subνUp ⊑-pa n)))))

------------------------------------------------------------------------
-- Coercions
------------------------------------------------------------------------

convSame : ∀ {m} (σ : TySub m 0) {A B : Ty m} (p : A <: B) {x y}
         → Same (A ⟨ σ ⟩) x y → Same (B ⟨ σ ⟩) (conv σ p x) (conv σ p y)
convSame σ sub-void {()}
convSame σ sub-var   s = s
convSame σ sub-unit  s = s
convSame σ sub-int   s = s
convSame σ sub-float s = s
convSame σ (sub-arr {A} {A′} {B} {B′} {q = Zero} {π} {π′} a b g) {f} {f′} s =
  lamZero {π = π′} {A = A′ ⟨ σ ⟩} {B = B′ ⟨ σ ⟩}
    (relSubˡ {π′} {π} {π′} g (relSubʳ {π} {π′} {π} g
      (relFmap {π} {π} {B ⟨ σ ⟩} {B′ ⟨ σ ⟩} (appZero {π = π} {A = A ⟨ σ ⟩} {B = B ⟨ σ ⟩} s) (convSame σ b))))
convSame σ (sub-arr {A} {A′} {B} {B′} {q = One} {π} {π′} a b g) {f} {f′} s =
  lamOne {π = π′} {A = A′ ⟨ σ ⟩} {B = B′ ⟨ σ ⟩} λ sa →
    relSubˡ {π′} {π} {π′} g (relSubʳ {π} {π′} {π} g
      (relFmap {π} {π} {B ⟨ σ ⟩} {B′ ⟨ σ ⟩} (appOne {π = π} {A = A ⟨ σ ⟩} {B = B ⟨ σ ⟩} s (convSame σ a sa)) (convSame σ b)))
convSame σ (sub-arr {A} {A′} {B} {B′} {q = Many} {π} {π′} a b g) {f} {f′} s =
  lamMany {π = π′} {A = A′ ⟨ σ ⟩} {B = B′ ⟨ σ ⟩} λ sa →
    relSubˡ {π′} {π} {π′} g (relSubʳ {π} {π′} {π} g
      (relFmap {π} {π} {B ⟨ σ ⟩} {B′ ⟨ σ ⟩} (appMany {π = π} {A = A ⟨ σ ⟩} {B = B ⟨ σ ⟩} s (convSame σ a sa)) (convSame σ b)))
convSame σ (sub-* a b) {x₁ , x₂} {y₁ , y₂} (s , t) = convSame σ a s , convSame σ b t
convSame σ (sub-+ a b) {inj₁ x} {inj₁ y} s = convSame σ a s
convSame σ (sub-+ a b) {inj₂ x} {inj₂ y} s = convSame σ b s
convSame σ (sub-+ a b) {inj₁ x} {inj₂ y} ()
convSame σ (sub-+ a b) {inj₂ x} {inj₁ y} ()
convSame σ sub-μ s = s
convSame σ (sub-ν {F = F} g) s = λ n → subνUp (code (F ⟨ σ ⟩F)) g n (s n)
