{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Coherence.Conv — a coercion along `A <: B`
-- (`Spec.Domain.conv`) maps the same values to the same values: at arrows
-- it composes with related computations; at codata it re-grades every
-- layer (`subν`), which keeps each layer, so the layers stay related.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature; call)

module Once.Metatheory.Coherence.Conv (Σ : Signature) where

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Once.Spec.Grade using (pure; act; eff⁺; eff; mk-kind; Zero; One; Many; _⊑π_; ⊑-pure; ⊑-pa; ⊑-pe; ⊑-act; ⊑-ae; ⊑-g; ⊑-ge; ⊑-eff)
open import Once.Spec.Type using (Ty; TySub; _⟨_⟩; _⟨_⟩F)
open import Once.Spec.Sub
open import Once.Spec.Polynomial using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF)
open import Once.Spec.Effect Σ
open import Once.Spec.Domain Σ
open import Once.Spec.Equivalence Σ
open import Once.Metatheory.Coherence.Relation Σ
open import Once.Metatheory.Coherence.Layer Σ

open T∞ using (force)
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

  lgeRel : ∀ H {R R′} → (∀ {x y} → R x y → R′ (νge G x) (νge G y)) → ∀ {l l′}
         → LayerEq H R l l′ → LayerEq H R′ (lge G H l) (lge G H l′)
  lgeRel (SK B)     h p = p
  lgeRel SId        h p = h p
  lgeRel (H₁ S⊕ H₂) h {inj₁ x} {inj₁ y} p = lgeRel H₁ h p
  lgeRel (H₁ S⊕ H₂) h {inj₂ x} {inj₂ y} p = lgeRel H₂ h p
  lgeRel (H₁ S⊕ H₂) h {inj₁ x} {inj₂ y} ()
  lgeRel (H₁ S⊕ H₂) h {inj₂ x} {inj₁ y} ()
  lgeRel (H₁ S⊗ H₂) h (p , q) = lgeRel H₁ h p , lgeRel H₂ h q

  subνUp : ∀ {π π′} (g : π ⊑π π′) n {v v′} → νUpTo π G n v v′ → νUpTo π′ G n (subν g G v) (subν g G v′)

  private
    paStep : ∀ n {v v′} → νUpTo pure G (suc n) v v′ → νUpTo act G (suc n) (νpa G v) (νpa G v′)
    paStep n {v} {v′} p = go p
      where go : NodeUpTo n (LayerEq G (νUpTo pure G n)) (done (outν v)) (done (outν v′))
               → NodeUpTo n (LayerEq G (νUpTo act G n)) (done (lpa G G (outν v))) (done (lpa G G (outν v′)))
            go (done≈ le) = done≈ (lpaRel G (subνUp ⊑-pa n) le)

    peStep : ∀ n {v v′} → νUpTo pure G (suc n) v v′ → νUpTo eff G (suc n) (νpe G v) (νpe G v′)
    peStep n {v} {v′} p = go p
      where go : NodeUpTo n (LayerEq G (νUpTo pure G n)) (done (outν v)) (done (outν v′))
               → NodeUpTo n (LayerEq G (νUpTo eff G n)) (done (lpe G G (outν v))) (done (lpe G G (outν v′)))
            go (done≈ le) = done≈ (lpeRel G (subνUp ⊑-pe n) le)

    taeUp : ∀ n k (t t′ : T (⟦ G ⟧SF (νM act G)))
          → UpTo k (LayerEq G (νUpTo act G n)) (embed t) (embed t′)
          → UpTo k (LayerEq G (νUpTo eff G n)) (tae G t) (tae G t′)
    taeUp n zero    t t′ p = tt
    taeUp n (suc k) (roll (done l)) (roll (done l′)) (done≈ le) = done≈ (laeRel G (subνUp ⊑-ae n) le)
    taeUp n (suc k) (roll (node (call o a κ))) (roll (node (call .o .a κ′))) (node≈ e) =
      node≈ λ b → taeUp n k (κ b) (κ′ b) (e b)
    taeUp n (suc k) (roll (done l)) (roll (node (call o a κ))) ()
    taeUp n (suc k) (roll (node (call o a κ))) (roll (done l′)) ()

    tgeUp  : ∀ n k (m m′ : T∞ (⟦ G ⟧SF (νM eff⁺ G)))
           → UpTo k (LayerEq G (νUpTo eff⁺ G n)) m m′
           → UpTo k (LayerEq G (νUpTo eff G n)) (tge G m) (tge G m′)
    tgeUpS : ∀ n k (s s′ : Step (⟦ G ⟧SF (νM eff⁺ G)) (T∞ (⟦ G ⟧SF (νM eff⁺ G))))
           → NodeUpTo k (LayerEq G (νUpTo eff⁺ G n)) s s′
           → NodeUpTo k (LayerEq G (νUpTo eff G n)) (sge G s) (sge G s′)
    tgeUp n zero    m m′ p = tt
    tgeUp n (suc k) m m′ p = tgeUpS n k (force m) (force m′) p
    tgeUpS n k (done l) (done l′) (done≈ le) = done≈ (lgeRel G (subνUp ⊑-ge n) le)
    tgeUpS n k (node (call o a κ)) (node (call .o .a κ′)) (node≈ e) = node≈ λ b → tgeUp n k (κ b) (κ′ b) (e b)

    rgeUp : ∀ n k (p p′ : T⁺ (⟦ G ⟧SF (νM eff⁺ G)))
          → UpTo (suc k) (LayerEq G (νUpTo eff⁺ G n)) (forget⁺ p) (forget⁺ p′)
          → UpTo (suc k) (LayerEq G (νUpTo eff G n)) (rge G p) (rge G p′)
    rgeUp n k (call⁺ (call o a κ)) (call⁺ (call .o .a κ′)) (node≈ e) = node≈ λ b → tgeUp n k (κ b) (κ′ b) (e b)

  subνUp ⊑-pure n p = p
  subνUp ⊑-act  n p = p
  subνUp ⊑-g    n p = p
  subνUp ⊑-eff  n p = p
  subνUp ⊑-pa   zero    p = tt
  subνUp ⊑-pa   (suc n) {v} {v′} p = paStep n {v} {v′} p
  subνUp ⊑-pe   zero    p = tt
  subνUp ⊑-pe   (suc n) {v} {v′} p = peStep n {v} {v′} p
  subνUp ⊑-ae   zero    p = tt
  subνUp ⊑-ae   (suc n) {v} {v′} p = taeUp n (suc n) (outν v) (outν v′) p
  subνUp ⊑-ge   zero    p = tt
  subνUp ⊑-ge   (suc n) {v} {v′} p = rgeUp n n (outν v) (outν v′) p

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
convSame σ (sub-* a b) {x₁ , x₂} {y₁ , y₂} s =
  λ n → convSame σ a (λ k → proj₁ (s k)) n , convSame σ b (λ k → proj₂ (s k)) n
convSame σ (sub-+ a b) {inj₁ x} {inj₁ y} s = convSame σ a s
convSame σ (sub-+ a b) {inj₂ x} {inj₂ y} s = convSame σ b s
convSame σ (sub-+ a b) {inj₁ x} {inj₂ y} s = ⊥-elim (s 0)
convSame σ (sub-+ a b) {inj₂ x} {inj₁ y} s = ⊥-elim (s 0)
convSame σ sub-μ s = s
convSame σ (sub-ν {F = F} g) s = λ n → subνUp (code (F ⟨ σ ⟩F)) g n (s n)
