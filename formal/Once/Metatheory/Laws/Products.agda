{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws.Products — the product laws of the core and `Unit`
-- terminal (`Spec.Metatheory.Equations`). The side that a law drops is
-- effect-free: its derivations return (`ProdV.pureRet`, by `transfer`).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature; OneName)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Laws.Products (Σ : Signature) (u : OneName Σ) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Spec.Grade using (pure)
open import Once.Spec.Type using (Ty; KCtx; _⟨_⟩; _*_; Unit)
open import Once.Spec.Context using (Ctx)
open import Once.Spec.Core.Syntax
open import Once.Spec.Core.Typing Σ S
open import Once.Spec.Core.Meaning Σ fmt S
open import Once.Spec.Effect Σ using (T∞; _>>=∞_; return∞; _≈_)
open import Once.Spec.Equivalence Σ using (Same)
open import Once.Spec.Metatheory using (_≅_; Pure)
open import Once.Metatheory.Bisim Σ using (≈-refl; ≈-sym; ≈-trans; ≈-bind; idˡ; idʳ; assoc)
open import Once.Metatheory.Coherence.Relation Σ using (Related; ≈-Relatedˡ; ≈-Relatedʳ; bindRel; returnRel)
open import Once.Metatheory.Coherence.Layer Σ using (rel; runs; relPure⁻)
open import Once.Metatheory.Coherence.Uniqueness Σ S using (ty-unique)
open import Once.Metatheory.Laws.Tools Σ u fmt S
open import Once.Metatheory.Laws.Views Σ u fmt S

module _ {m : ℕ} {Δ : KCtx m} where

  fst-pair : ∀ {n} {Γ : Ctx m n} {Ψ A B π a b}
           → Pure Σ fmt S Δ Γ b B
           → (d : Δ ⊩ Γ ⊢[ Ψ ] fst (pair a b) ∷ A ! π)
             (d′ : Δ ⊩ Γ ⊢[ Ψ ] a ∷ A ! π) → _≅_ Σ fmt S d d′
  fst-pair {Γ = Γ} {A = A} {B} {π} (_ , pb) d d′ δ sd σ r γ sγ = sameM {A ⟨ σ ⟩} {π} (rel (go (viewFst d base)))
    where
      open Views δ sd σ r γ sγ
      open ProdV δ sd σ r γ sγ

      go : FstView d γ → _~_ {A} (⟪ d ⟫ γ) (⟪ d′ ⟫ γ)
      go (fstView dp r₀ eqF) = goP (viewPair dp r₀)
        where
          goP : PairView dp _ → _~_ {A} (⟪ d ⟫ γ) (⟪ d′ ⟫ γ)
          goP (pairView da db {ea} {eb} ra rb eqP) with ty-unique db pb
          ... | refl =
            ~trans {A} eqF
              (~trans {A} (bindRel eqP (λ s → returnRel (proj₁ s)))
                (≈-Relatedˡ norm
                  (≈-Relatedʳ (≈-sym (idʳ (⟪ d′ ⟫ γ)))
                    (bindRel (runs (fl da d′ ra base)) K))))
            where
              g : _ → T∞ _
              g v = return∞ (proj₁ v)
              norm : ((⟪ da ⟫ ea >>=∞ λ x → ⟪ db ⟫ eb >>=∞ λ y → return∞ (x , y)) >>=∞ g)
                   ≈ (⟪ da ⟫ ea >>=∞ λ x → ⟪ db ⟫ eb >>=∞ λ _ → return∞ x)
              norm = ≈-trans (assoc _ _ g) (≈-bind (≈-refl _) λ x →
                       ≈-trans (assoc _ _ g) (≈-bind (≈-refl _) λ y → idˡ (x , y) g))
              K : ∀ {x x′} → Same (A ⟨ σ ⟩) x x′ → _~_ {A} (⟪ db ⟫ eb >>=∞ λ _ → return∞ x) (return∞ x′)
              K {x} {x′} s = ≈-Relatedʳ (≈-sym (idˡ (⟦ transfer pb db ⟧ δ σ r eb) (λ _ → return∞ x′)))
                               (bindRel (pureRet db pb rb) (λ _ → returnRel s))

  snd-pair : ∀ {n} {Γ : Ctx m n} {Ψ A B π a b}
           → Pure Σ fmt S Δ Γ a A
           → (d : Δ ⊩ Γ ⊢[ Ψ ] snd (pair a b) ∷ B ! π)
             (d′ : Δ ⊩ Γ ⊢[ Ψ ] b ∷ B ! π) → _≅_ Σ fmt S d d′
  snd-pair {Γ = Γ} {A = A} {B} {π} (_ , pa) d d′ δ sd σ r γ sγ = sameM {B ⟨ σ ⟩} {π} (rel (go (viewSnd d base)))
    where
      open Views δ sd σ r γ sγ
      open ProdV δ sd σ r γ sγ

      go : SndView d γ → _~_ {B} (⟪ d ⟫ γ) (⟪ d′ ⟫ γ)
      go (sndView dp r₀ eqS) = goP (viewPair dp r₀)
        where
          goP : PairView dp _ → _~_ {B} (⟪ d ⟫ γ) (⟪ d′ ⟫ γ)
          goP (pairView da db {ea} {eb} ra rb eqP) with ty-unique da pa
          ... | refl =
            ~trans {B} eqS
              (~trans {B} (bindRel eqP (λ s → returnRel (proj₂ s)))
                (≈-Relatedˡ norm
                  (≈-Relatedʳ (≈-sym (idˡ (⟦ transfer pa da ⟧ δ σ r ea) (λ _ → ⟪ d′ ⟫ γ)))
                    (bindRel (pureRet da pa ra) (λ _ → ≈-Relatedʳ (≈-sym (idʳ (⟪ d′ ⟫ γ)))
                                                         (bindRel (runs (fl db d′ rb base)) (λ s → returnRel s)))))))
            where
              g : _ → T∞ _
              g v = return∞ (proj₂ v)
              norm : ((⟪ da ⟫ ea >>=∞ λ x → ⟪ db ⟫ eb >>=∞ λ y → return∞ (x , y)) >>=∞ g)
                   ≈ (⟪ da ⟫ ea >>=∞ λ _ → ⟪ db ⟫ eb >>=∞ λ y → return∞ y)
              norm = ≈-trans (assoc _ _ g) (≈-bind (≈-refl _) λ x →
                       ≈-trans (assoc _ _ g) (≈-bind (≈-refl _) λ y → idˡ (x , y) g))

  pair-η : ∀ {n} {Γ : Ctx m n} {Ψ A B π p}
         → Pure Σ fmt S Δ Γ p (A * B)
         → (d : Δ ⊩ Γ ⊢[ Ψ ] pair (fst p) (snd p) ∷ A * B ! π)
           (d′ : Δ ⊩ Γ ⊢[ Ψ ] p ∷ A * B ! π) → _≅_ Σ fmt S d d′
  pair-η {Γ = Γ} {A = A} {B} {π} (_ , pp) d d′ δ sd σ r γ sγ = sameM {(A * B) ⟨ σ ⟩} {π} (rel (go (viewPair d base)))
    where
      open Views δ sd σ r γ sγ
      open ProdV δ sd σ r γ sγ

      v₀ = ⟦ transfer pp d′ ⟧ δ σ r γ

      go : PairView d γ → _~_ {A * B} (⟪ d ⟫ γ) (⟪ d′ ⟫ γ)
      go (pairView da db {ea} {eb} ra rb eqP) = goFS (viewFst da ra) (viewSnd db rb)
        where
          goFS : FstView da ea → SndView db eb → _~_ {A * B} (⟪ d ⟫ γ) (⟪ d′ ⟫ γ)
          goFS (fstView dp₁ {e₁} r₁ eqF) (sndView dp₂ {e₂} r₂ eqS) with ty-unique dp₁ pp | ty-unique dp₂ pp
          ... | refl | refl =
            ~trans {A * B} eqP
              (~trans {A * B}
                (bindRel {f = λ x → ⟪ db ⟫ eb >>=∞ λ y → return∞ (x , y)} {g = λ x → return∞ b₂ >>=∞ λ y → return∞ (x , y)}
                  sa (λ {x} {x′} sx → bindRel sb (λ sy → returnRel (sx , sy))))
                (≈-Relatedˡ (≈-trans (idˡ a₁ _) (idˡ b₂ _))
                  (~trans {A * B} (returnRel (proj₁ s₁₀ , proj₂ s₂₀)) (~sym {A * B} (pureRet d′ pp base)))))
            where
              v₁ = ⟦ transfer pp dp₁ ⟧ δ σ r e₁
              v₂ = ⟦ transfer pp dp₂ ⟧ δ σ r e₂
              a₁ = proj₁ v₁
              b₂ = proj₂ v₂
              -- the first component is `v₁`'s, the second `v₂`'s; both `p`'s values, the same as `v₀`
              sa : _~_ {A} (⟪ da ⟫ ea) (return∞ a₁)
              sa = ~trans {A} eqF (≈-Relatedʳ (≈-sym (idˡ v₁ (λ v → return∞ (proj₁ v))))
                                    (bindRel (pureRet dp₁ pp r₁) (λ s → returnRel (proj₁ s))))
              sb : _~_ {B} (⟪ db ⟫ eb) (return∞ b₂)
              sb = ~trans {B} eqS (≈-Relatedʳ (≈-sym (idˡ v₂ (λ v → return∞ (proj₂ v))))
                                    (bindRel (pureRet dp₂ pp r₂) (λ s → returnRel (proj₂ s))))
              s₁₀ : Same ((A * B) ⟨ σ ⟩) v₁ v₀
              s₁₀ = relPure⁻ (fl (transfer pp dp₁) (transfer pp d′) r₁ base)
              s₂₀ : Same ((A * B) ⟨ σ ⟩) v₂ v₀
              s₂₀ = relPure⁻ (fl (transfer pp dp₂) (transfer pp d′) r₂ base)

  unit-η : ∀ {n} {Γ : Ctx m n} {Ψ π t}
         → Pure Σ fmt S Δ Γ t Unit
         → (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ Unit ! π)
           (d′ : Δ ⊩ Γ ⊢[ Ψ ] unit ∷ Unit ! π) → _≅_ Σ fmt S d d′
  unit-η {π = π} (_ , pt) d d′ δ sd σ r γ sγ =
    sameM {Unit} {π} (rel (~trans {Unit} (pureRet d pt base) (~trans {Unit} (returnRel tt) (~sym {Unit} (pureRet d′ ⊢unit base)))))
    where
      open Views δ sd σ r γ sγ
      open ProdV δ sd σ r γ sγ
