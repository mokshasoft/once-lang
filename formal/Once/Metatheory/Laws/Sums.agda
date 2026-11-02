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
open import Data.Fin using (zero)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Data.Unit using (tt)
open import Function using (flip)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Spec.Grade using (Quantity; Zero; One; Many)
open import Once.Spec.Type using (Ty; KCtx; _⟨_⟩; _+_)
open import Once.Spec.Context using (Ctx; _▸_; _∷_)
open import Once.Spec.Core.Syntax
open import Once.Spec.Core.Typing Σ S
open import Once.Spec.Core.Meaning Σ fmt S
open import Once.Spec.Effect Σ using (T∞; _>>=∞_; return∞; _≈_)
open import Once.Spec.Equivalence Σ using (Same)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ)
open import Once.Spec.Metatheory using (_≅_)
open import Once.Metatheory.Bisim Σ using (≈-refl; ≈-sym; ≈-trans; ≈-bind; idˡ; idʳ; assoc)
open import Once.Metatheory.Coherence.Relation Σ using (Related; Related-flip; Related-mono; ≈-Relatedˡ; ≈-Relatedʳ; bindRel; returnRel)
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

  case-inr : ∀ {n} {Γ : Ctx m n} {Ψ A C qℓ qr π a l rr}
             (d : Δ ⊩ Γ ⊢[ Ψ ] case qℓ qr (inr A a) l rr ∷ C ! π)
             (d′ : Δ ⊩ Γ ⊢[ Ψ ] let′ qr a rr ∷ C ! π) → _≅_ Σ fmt S d d′
  case-inr {Γ = Γ} {C = C} {qℓ} {qr} {π} d d′ δ sd σ r γ sγ = sameM {C ⟨ σ ⟩} {π} (rel (go (viewCase d base) (viewLet d′ base)))
    where
      open Views δ sd σ r γ sγ

      go : CaseView d γ → LetView d′ γ → _~_ {C} (⟪ d ⟫ γ) (⟪ d′ ⟫ γ)
      go (caseView {A = A} {B} ds dl dr {es} {ec} rs rc eqL) L = goI (viewInr ds rs) L
        where
          K : _ → T∞ _
          K = [ (λ x → ⟪ dl ⟫▸ ec (slot qℓ x)) , (λ y → ⟪ dr ⟫▸ ec (slot qr y)) ]′

          Kcong : ∀ {x x′} → Same ((A + B) ⟨ σ ⟩) x x′ → _~_ {C} (K x) (K x′)
          Kcong {inj₁ x} {inj₁ x′} s = runs (fl▸ dl dl rc rc (slotAgree σ {A} qℓ qℓ s))
          Kcong {inj₂ y} {inj₂ y′} s = runs (fl▸ dr dr rc rc (slotAgree σ {B} qr qr s))
          Kcong {inj₁ x} {inj₂ y′} ()
          Kcong {inj₂ y} {inj₁ x′} ()

          -- the scrutinee's value is a right one
          goI : InrView ds es → LetView d′ γ → _~_ {C} (⟪ d ⟫ γ) (⟪ d′ ⟫ γ)
          goI (inrView da {γ₀} r₀ eqI) (letView de db rb sem) with ty-unique da de
          ... | refl = ~trans {C} eqL (~trans {C} (bindRel eqI (λ {x} {y} s → Kcong {x} {y} s)) (≈-Relatedˡ unit₁ (letEnd qr da r₀ dr rc de db rb sem)))
            where
              unit₁ : ((⟪ da ⟫ γ₀ >>=∞ λ x → return∞ (inj₂ x)) >>=∞ K) ≈ (⟪ da ⟫ γ₀ >>=∞ λ x → K (inj₂ x))
              unit₁ = ≈-trans (assoc _ _ _) (≈-bind (≈-refl _) λ x → idˡ (inj₂ x) K)

  case-η : ∀ {n} {Γ : Ctx m n} {Ψ A B qℓ qr π s}
           (d : Δ ⊩ Γ ⊢[ Ψ ] case qℓ qr s (inl B (var zero)) (inr A (var zero)) ∷ A + B ! π)
           (d′ : Δ ⊩ Γ ⊢[ Ψ ] s ∷ A + B ! π) → _≅_ Σ fmt S d d′
  case-η {Γ = Γ} {A = A} {B} {qℓ} {qr} {π} d d′ δ sd σ r γ sγ = sameM {(A + B) ⟨ σ ⟩} {π} (rel (go (viewCase d base)))
    where
      open Views δ sd σ r γ sγ

      ret : ∀ {X : Ty m} {x y : ⟦ X ⟨ σ ⟩ ⟧ᵛ} → Same (X ⟨ σ ⟩) x y → _~_ {X} (return∞ x) (return∞ y)
      ret s = returnRel s

      subSame : ∀ {X : Ty m} {w x y : ⟦ X ⟨ σ ⟩ ⟧ᵛ} → w ≡ x → Same (X ⟨ σ ⟩) x y → Same (X ⟨ σ ⟩) w y
      subSame refl s = s

      armL : ∀ {Ψc π₂ ec} (dl : Δ ⊩ (Γ ▸ A) ⊢[ qℓ ∷ Ψc ] inl B (var zero) ∷ A + B ! π₂) → Res ec
           → ∀ {x y} → Same (A ⟨ σ ⟩) x y → _~_ {A + B} (⟪ dl ⟫▸ ec (slot qℓ x)) (return∞ (inj₁ y))
      armL {Ψc} {ec = ec} dl rc {x} {y} s =
        ~trans {A + B} (W.InlView.eq V)
          (~trans {A + B} (≈-Relatedʳ (≈-sym (idˡ w (λ z → return∞ (inj₁ z))))
                             (bindRel (proj₂ vv) (λ s′ → returnRel s′)))
                          (ret {A + B} (subSame {A} (look0 σ qℓ (proj₁ vv)) s)))
        where
          module W = Views δ sd σ r {Γ = Γ ▸ A} {Ψ = qℓ ∷ Ψc} (ec , slot qℓ x)
                           (sameEnv▸ σ qℓ (sameEnvOf rc) (slotAgree σ {A} qℓ qℓ (sameRefl (A ⟨ σ ⟩) s)))
          V = W.viewInl dl W.base
          vv = W.varVal (W.InlView.da V) (W.InlView.r₀ V)
          w = lookupᵛ σ (Γ ▸ A) zero (restrict σ {Γ = Γ ▸ A} (proj₁ vv) (ec , slot qℓ {⟦ A ⟨ σ ⟩ ⟧ᵛ} x))

      armR : ∀ {Ψc π₂ ec} (dr : Δ ⊩ (Γ ▸ B) ⊢[ qr ∷ Ψc ] inr A (var zero) ∷ A + B ! π₂) → Res ec
           → ∀ {x y} → Same (B ⟨ σ ⟩) x y → _~_ {A + B} (⟪ dr ⟫▸ ec (slot qr x)) (return∞ (inj₂ y))
      armR {Ψc} {ec = ec} dr rc {x} {y} s =
        ~trans {A + B} (W.InrView.eq V)
          (~trans {A + B} (≈-Relatedʳ (≈-sym (idˡ w (λ z → return∞ (inj₂ z))))
                             (bindRel (proj₂ vv) (λ s′ → returnRel s′)))
                          (ret {A + B} (subSame {B} (look0 σ qr (proj₁ vv)) s)))
        where
          module W = Views δ sd σ r {Γ = Γ ▸ B} {Ψ = qr ∷ Ψc} (ec , slot qr x)
                           (sameEnv▸ σ qr (sameEnvOf rc) (slotAgree σ {B} qr qr (sameRefl (B ⟨ σ ⟩) s)))
          V = W.viewInr dr W.base
          vv = W.varVal (W.InrView.db V) (W.InrView.r₀ V)
          w = lookupᵛ σ (Γ ▸ B) zero (restrict σ {Γ = Γ ▸ B} (proj₁ vv) (ec , slot qr {⟦ B ⟨ σ ⟩ ⟧ᵛ} x))

      go : CaseView d γ → _~_ {A + B} (⟪ d ⟫ γ) (⟪ d′ ⟫ γ)
      go (caseView ds dl dr {es} {ec} rs rc eqL) with ty-unique ds d′
      ... | refl = ~trans {A + B} eqL
                     (≈-Relatedʳ (≈-sym (idʳ (⟪ d′ ⟫ γ)))
                       (bindRel (runs (fl ds d′ rs base)) (λ {x} {y} s → Kret {x} {y} s)))
        where
          Kret : ∀ {x y} → Same ((A + B) ⟨ σ ⟩) x y
               → _~_ {A + B} ([ (λ a → ⟪ dl ⟫▸ ec (slot qℓ a)) , (λ b → ⟪ dr ⟫▸ ec (slot qr b)) ]′ x) (return∞ y)
          Kret {inj₁ x} {inj₁ y} s = armL dl rc s
          Kret {inj₂ x} {inj₂ y} s = armR dr rc s
          Kret {inj₁ x} {inj₂ y} ()
          Kret {inj₂ x} {inj₁ y} ()
