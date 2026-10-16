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
open import Once.Spec.Grade using (pure; act; eff; mk-kind; Zero; One; Many; _⊑π_; ⊑-pure; ⊑-pa; ⊑-pe; ⊑-act; ⊑-ae; ⊑-eff)
open import Once.Spec.Type using (Ty; TySub; _⟨_⟩; _⟨_⟩F)
open import Once.Spec.Sub
open import Once.Spec.Polynomial using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF)
open import Once.Spec.Effect Σ
open import Once.Spec.Domain Σ
open import Once.Spec.Equivalence Σ
open import Once.Metatheory.Coherence.Relation Σ
open import Once.Metatheory.Coherence.Layer Σ

open T∞ using (force)
open _≈_ using (force≈)
open νM using (outν)

------------------------------------------------------------------------
-- Re-grading codata
------------------------------------------------------------------------

module _ (G : SFunctor) where
  lpaRel : ∀ H {R R′} → (∀ {x y} → R x y → R′ (νpa G x) (νpa G y)) → ∀ {l l′}
         → LayerEq H R l l′ → LayerEq H R′ (lpa G H l) (lpa G H l′)
  lpaRel (SK B)     h p = p
  lpaRel SId        h p = h p
  lpaRel (H₁ S⊕ H₂) h {inj₁ x} {inj₁ y} p = lpaRel H₁ h p
  lpaRel (H₁ S⊕ H₂) h {inj₂ x} {inj₂ y} p = lpaRel H₂ h p
  lpaRel (H₁ S⊕ H₂) h {inj₁ x} {inj₂ y} ()
  lpaRel (H₁ S⊕ H₂) h {inj₂ x} {inj₁ y} ()
  lpaRel (H₁ S⊗ H₂) h (p , q) = lpaRel H₁ h p , lpaRel H₂ h q

  lpeRel : ∀ H {R R′} → (∀ {x y} → R x y → R′ (νpe G x) (νpe G y)) → ∀ {l l′}
         → LayerEq H R l l′ → LayerEq H R′ (lpe G H l) (lpe G H l′)
  lpeRel (SK B)     h p = p
  lpeRel SId        h p = h p
  lpeRel (H₁ S⊕ H₂) h {inj₁ x} {inj₁ y} p = lpeRel H₁ h p
  lpeRel (H₁ S⊕ H₂) h {inj₂ x} {inj₂ y} p = lpeRel H₂ h p
  lpeRel (H₁ S⊕ H₂) h {inj₁ x} {inj₂ y} ()
  lpeRel (H₁ S⊕ H₂) h {inj₂ x} {inj₁ y} ()
  lpeRel (H₁ S⊗ H₂) h (p , q) = lpeRel H₁ h p , lpeRel H₂ h q

  laeRel : ∀ H {R R′} → (∀ {x y} → R x y → R′ (νae G x) (νae G y)) → ∀ {l l′}
         → LayerEq H R l l′ → LayerEq H R′ (lae G H l) (lae G H l′)
  laeRel (SK B)     h p = p
  laeRel SId        h p = h p
  laeRel (H₁ S⊕ H₂) h {inj₁ x} {inj₁ y} p = laeRel H₁ h p
  laeRel (H₁ S⊕ H₂) h {inj₂ x} {inj₂ y} p = laeRel H₂ h p
  laeRel (H₁ S⊕ H₂) h {inj₁ x} {inj₂ y} ()
  laeRel (H₁ S⊕ H₂) h {inj₂ x} {inj₁ y} ()
  laeRel (H₁ S⊗ H₂) h (p , q) = laeRel H₁ h p , laeRel H₂ h q

  subνUp : ∀ {π π′} (g : π ⊑π π′) n {v v′} → νUpTo π G n v v′ → νUpTo π′ G n (subν g G v) (subν g G v′)

  private
    -- Each re-graded layer computation is the old one, mapped.
    pa≈ : ∀ (v : νM pure G) → toT∞ act (outν (νpa G v)) ≈ (toT∞ pure (outν v) >>=∞ λ l → return∞ (lpa G G l))
    force≈ (pa≈ v) = return≈

    pe≈ : ∀ (v : νM pure G) → toT∞ eff (outν (νpe G v)) ≈ (toT∞ pure (outν v) >>=∞ λ l → return∞ (lpe G G l))
    force≈ (pe≈ v) = return≈

    aeB : ∀ (t : T (⟦ G ⟧SF (νM act G))) → BlockEq _≈_ (bae G t) (bindBlock (mapT inj₁ t) λ l → return∞ (lae G G l))
    aeB (roll (done l))            = return≈
    aeB (roll (node (call o a k))) = node≈ λ b → aeB (k b)

    ae≈ : ∀ (v : νM act G) → toT∞ eff (outν (νae G v)) ≈ (toT∞ act (outν v) >>=∞ λ l → return∞ (lae G G l))
    force≈ (ae≈ v) = aeB (outν v)

    regrade : ∀ {π π′} {f : ⟦ G ⟧SF (νM π G) → ⟦ G ⟧SF (νM π′ G)} {R R′} → (∀ {l l′} → LayerEq G R l l′ → LayerEq G R′ (f l) (f l′))
            → ∀ {v v′ : νM π G} {w w′ : νM π′ G} → toT∞ π′ (outν w) ≈ (toT∞ π (outν v) >>=∞ λ l → return∞ (f l))
            → toT∞ π′ (outν w′) ≈ (toT∞ π (outν v′) >>=∞ λ l → return∞ (f l))
            → (∀ k → UpTo k (LayerEq G R) (toT∞ π (outν v)) (toT∞ π (outν v′)))
            → ∀ k → UpTo k (LayerEq G R′) (toT∞ π′ (outν w)) (toT∞ π′ (outν w′))
    regrade h e e′ p = toUpTo (≈-Relatedˡ e (≈-Relatedʳ e′ (relatedFmap (fromUpTo p) h)))

  subνUp ⊑-pure n p = p
  subνUp ⊑-act  n p = p
  subνUp ⊑-eff  n p = p
  subνUp ⊑-pa   zero    p = tt
  subνUp ⊑-pa   (suc n) {v} {v′} p =
    regrade (lpaRel G (subνUp ⊑-pa n)) {v = v} {v′} {νpa G v} {νpa G v′} (pa≈ v) (pa≈ v′) p
  subνUp ⊑-pe   zero    p = tt
  subνUp ⊑-pe   (suc n) {v} {v′} p =
    regrade (lpeRel G (subνUp ⊑-pe n)) {v = v} {v′} {νpe G v} {νpe G v′} (pe≈ v) (pe≈ v′) p
  subνUp ⊑-ae   zero    p = tt
  subνUp ⊑-ae   (suc n) {v} {v′} p =
    regrade (laeRel G (subνUp ⊑-ae n)) {v = v} {v′} {νae G v} {νae G v′} (ae≈ v) (ae≈ v′) p

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
