{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws.Sums — the coproduct laws of the core
-- (`Spec.Metatheory.Equations`): β for any scrutinee (its effects run, then
-- one arm).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature; OneName)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Laws.Sums (Σ : Signature) (u : OneName Σ) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Data.Unit using (tt)
open import Function using (flip)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Spec.Grade using (Quantity; Zero; One; Many)
open import Once.Spec.Type using (Ty; KCtx; _⟨_⟩; _+_)
open import Once.Spec.Context using (Ctx; _▸_)
open import Once.Spec.Core.Syntax
open import Once.Spec.Core.Typing Σ S
open import Once.Spec.Core.Meaning Σ fmt S
open import Once.Spec.Effect Σ using (T∞; _>>=∞_; return∞; _≈_)
open import Once.Spec.Equivalence Σ using (Same)
open import Once.Spec.Metatheory using (_≅_)
open import Once.Metatheory.Bisim Σ using (≈-refl; ≈-sym; ≈-trans; ≈-bind; idˡ; assoc)
open import Once.Metatheory.Coherence.Relation Σ using (Related; Related-flip; Related-mono; ≈-Relatedˡ; ≈-Relatedʳ; bindRel)
open import Once.Metatheory.Coherence.Layer Σ using (rel; runs)
open import Once.Metatheory.Coherence.PER Σ using (Same-sym)
open import Once.Metatheory.Coherence.Uniqueness Σ S using (ty-unique)
open import Once.Metatheory.Laws.Tools Σ u fmt S
open import Once.Metatheory.Laws.Views Σ u fmt S

module _ {m : ℕ} {Δ : KCtx m} where

  case-inl : ∀ {n} {Γ : Ctx m n} {Ψ B C qℓ qr π a l rr}
             (d : Δ ⊩ Γ ⊢[ Ψ ] case qℓ qr (inl B a) l rr ∷ C ! π)
             (d′ : Δ ⊩ Γ ⊢[ Ψ ] let′ qℓ a l ∷ C ! π) → _≅_ Σ fmt S d d′
  case-inl {Γ = Γ} {C = C} {qℓ} {qr} {π} d d′ δ sd σ r γ sγ = sameM {C ⟨ σ ⟩} {π} (rel (go (viewCase d base) (viewLet d′ base)))
    where
      open Views δ sd σ r γ sγ

      go : CaseView d γ → LetView d′ γ → _~_ {C} (⟪ d ⟫ γ) (⟪ d′ ⟫ γ)
      go (caseView {A = A} {B} ds dl dr {es} {ec} rs rc eqL) L = goI (viewInl ds rs) L
        where
          K : _ → T∞ _
          K = [ (λ x → ⟪ dl ⟫▸ ec (slot qℓ x)) , (λ y → ⟪ dr ⟫▸ ec (slot qr y)) ]′

          Kcong : ∀ {x x′} → Same ((A + B) ⟨ σ ⟩) x x′ → _~_ {C} (K x) (K x′)
          Kcong {inj₁ x} {inj₁ x′} s = runs (fl▸ dl dl rc rc (slotAgree σ {A} qℓ qℓ s))
          Kcong {inj₂ y} {inj₂ y′} s = runs (fl▸ dr dr rc rc (slotAgree σ {B} qr qr s))
          Kcong {inj₁ x} {inj₂ y′} ()
          Kcong {inj₂ y} {inj₁ x′} ()

          -- the scrutinee's value is a left one
          goI : InlView ds es → LetView d′ γ → _~_ {C} (⟪ d ⟫ γ) (⟪ d′ ⟫ γ)
          goI (inlView da {γ₀} r₀ eqI) (letView de db rb sem) with ty-unique da de
          ... | refl = ~trans {C} eqL (~trans {C} (bindRel eqI (λ {x} {y} s → Kcong {x} {y} s)) (≈-Relatedˡ unit₁ (letEnd qℓ da r₀ dl rc de db rb sem)))
            where
              unit₁ : ((⟪ da ⟫ γ₀ >>=∞ λ x → return∞ (inj₁ x)) >>=∞ K) ≈ (⟪ da ⟫ γ₀ >>=∞ λ x → K (inj₁ x))
              unit₁ = ≈-trans (assoc _ _ _) (≈-bind (≈-refl _) λ x → idˡ (inj₁ x) K)
