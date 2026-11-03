{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws.MapCov — what a derivation of `mapᶜ`'s body fixes
-- about the type it maps (`Laws.MapSem.Cov`): an arrow's domain is the same
-- at both ends, and a functor's constants are base types at both ends.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Laws.MapCov (Σ : Signature) {s : ℕ} (S : Defs s) where

open import Data.Fin using () renaming (zero to fz; suc to fs)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Once.Spec.Grade using (Quantity; mk-kind; Purity)
open import Once.Spec.Type using (Ty; Fun; KCtx; WFFun; wf-K; wf-Id; wf-⊕; wf-⊗; ⟦_⟧F; _⟨_⟩; _⟨_⟩F; _⇒[_]_; _*_; _+_;
                                  var; Unit; Void; Int; Float; μ; ν; K; Id; _⊕_; _⊗_; at₀)
open import Once.Spec.Context using (Ctx; _▸_; _∷_)
open import Once.Spec.Core.Syntax
open import Once.Spec.Core.Derived using (mapAtᶜ; mapLayerᶜ)
open import Once.Spec.Core.Typing Σ S
open import Once.Metatheory.Laws.Strengthen Σ S using (varTy)
open import Once.Metatheory.Laws.MapSem Σ using (module MapAt)

module _ {m : ℕ} {Δ : KCtx m} where

  -- Any derivation of a former: its premises, the type it has.
  lamInv : ∀ {n} {Γ : Ctx m n} {Ψ X q π Y π₀ t} → Δ ⊩ Γ ⊢[ Ψ ] lam X q π t ∷ Y ! π₀
         → Σ[ B ∈ Ty m ] Σ[ q′ ∈ Quantity ] Σ[ Ψ₀ ∈ _ ] (Y ≡ X ⇒[ mk-kind q π ] B) × (Δ ⊩ Γ ▸ X ⊢[ q′ ∷ Ψ₀ ] t ∷ B ! π)
  lamInv (⊢lam {Ψ = Ψ₀} {q′ = q′} {B = B} le d) = B , q′ , Ψ₀ , refl , d
  lamInv (⊢sub-use _ d) = lamInv d
  lamInv (⊢sub-eff _ d) = lamInv d

  letInv : ∀ {n} {Γ : Ctx m n} {Ψ q Y π e b} → Δ ⊩ Γ ⊢[ Ψ ] let′ q e b ∷ Y ! π
         → Σ[ X ∈ Ty m ] Σ[ Ψ₁ ∈ _ ] Σ[ Ψ₂ ∈ _ ] Σ[ π₁ ∈ Purity ] Σ[ π₂ ∈ Purity ]
             (Δ ⊩ Γ ⊢[ Ψ₁ ] e ∷ X ! π₁) × (Δ ⊩ Γ ▸ X ⊢[ q ∷ Ψ₂ ] b ∷ Y ! π₂)
  letInv (⊢let {A = X} de db) = X , _ , _ , _ , _ , de , db
  letInv (⊢sub-use _ d) = letInv d
  letInv (⊢sub-eff _ d) = letInv d

  inlInv : ∀ {n} {Γ : Ctx m n} {Ψ Z X Y π t} → Δ ⊩ Γ ⊢[ Ψ ] inl Z t ∷ X + Y ! π → Σ[ Ψ₀ ∈ _ ] Σ[ π₀ ∈ Purity ] (Δ ⊩ Γ ⊢[ Ψ₀ ] t ∷ X ! π₀)
  inlInv (⊢inl d) = _ , _ , d
  inlInv (⊢sub-use _ d) = inlInv d
  inlInv (⊢sub-eff _ d) = inlInv d

  inrInv : ∀ {n} {Γ : Ctx m n} {Ψ Z X Y π t} → Δ ⊩ Γ ⊢[ Ψ ] inr Z t ∷ X + Y ! π → Σ[ Ψ₀ ∈ _ ] Σ[ π₀ ∈ Purity ] (Δ ⊩ Γ ⊢[ Ψ₀ ] t ∷ Y ! π₀)
  inrInv (⊢inr d) = _ , _ , d
  inrInv (⊢sub-use _ d) = inrInv d
  inrInv (⊢sub-eff _ d) = inrInv d

  outInv : ∀ {n} {Γ : Ctx m n} {Ψ X π t} → Δ ⊩ Γ ⊢[ Ψ ] out t ∷ X ! π
         → Σ[ F ∈ Fun m ] Σ[ f ∈ _ ] Σ[ Ψ₀ ∈ _ ] Σ[ π₀ ∈ Purity ] (X ≡ ⟦ F ⟧F (ν F f)) × WFFun Δ F × (Δ ⊩ Γ ⊢[ Ψ₀ ] t ∷ ν F f ! π₀)
  outInv (⊢out wf d) = _ , _ , _ , _ , refl , wf , d
  outInv (⊢sub-use _ d) = outInv d
  outInv (⊢sub-eff _ d) = outInv d

  rollInv : ∀ {n} {Γ : Ctx m n} {Ψ F π t} → Δ ⊩ Γ ⊢[ Ψ ] roll F t ∷ μ F ! π
          → WFFun Δ F × Σ[ Ψ₀ ∈ _ ] Σ[ π₀ ∈ Purity ] (Δ ⊩ Γ ⊢[ Ψ₀ ] t ∷ ⟦ F ⟧F (μ F) ! π₀)
  rollInv (⊢roll wf d) = wf , _ , _ , d
  rollInv (⊢sub-use _ d) = rollInv d
  rollInv (⊢sub-eff _ d) = rollInv d

  wf₁ : ∀ {F G : Fun m} → WFFun Δ (F ⊕ G) → WFFun Δ F
  wf₁ (wf-⊕ a b) = a
  wf₂ : ∀ {F G : Fun m} → WFFun Δ (F ⊕ G) → WFFun Δ G
  wf₂ (wf-⊕ a b) = b
  wf₁⊗ : ∀ {F G : Fun m} → WFFun Δ (F ⊗ G) → WFFun Δ F
  wf₁⊗ (wf-⊗ a b) = a
  wf₂⊗ : ∀ {F G : Fun m} → WFFun Δ (F ⊗ G) → WFFun Δ G
  wf₂⊗ (wf-⊗ a b) = b

  dom≡ : ∀ {X Y Z Z′ : Ty m} {k k′} → (Y ⇒[ k ] Z) ≡ (X ⇒[ k′ ] Z′) → Y ≡ X
  dom≡ refl = refl
  cod≡ : ∀ {X Y Z Z′ : Ty m} {k k′} → (Y ⇒[ k ] Z) ≡ (X ⇒[ k′ ] Z′) → Z ≡ Z′
  cod≡ refl = refl

  module Covs {σ} (A B : Ty m) where
    open MapAt Δ σ A B

    mutual
      covOf : ∀ {n} {Γ : Ctx m n} {Ψ π} T {h x} → Δ ⊩ Γ ⊢[ Ψ ] mapAtᶜ A B T h x ∷ T ⟨ at₀ B ⟩ ! π → Cov T
      covOf (var fz)     d = tt
      covOf (var (fs i)) d = tt
      covOf Unit  d = tt
      covOf Void  d = tt
      covOf Int   d = tt
      covOf Float d = tt
      covOf (T₁ * T₂) (⊢pair d₁ d₂) = covOf T₁ d₁ , covOf T₂ d₂
      covOf (T₁ * T₂) (⊢sub-use _ d) = covOf (T₁ * T₂) d
      covOf (T₁ * T₂) (⊢sub-eff _ d) = covOf (T₁ * T₂) d
      covOf (T₁ + T₂) (⊢case ds dl dr) with inlInv dl | inrInv dr
      ... | _ , _ , d₁ | _ , _ , d₂ = covOf T₁ d₁ , covOf T₂ d₂
      covOf (T₁ + T₂) (⊢sub-use _ d) = covOf (T₁ + T₂) d
      covOf (T₁ + T₂) (⊢sub-eff _ d) = covOf (T₁ + T₂) d
      covOf (T₁ ⇒[ mk-kind q π ] T₂) d with lamInv d
      ... | B′ , q′ , Ψ₀ , eqT , dt with cod≡ eqT
      ...   | refl with letInv dt
      ...     | _ , _ , _ , _ , _ , de , db = sym (dom≡ eqT) , covOf T₂ db
      covOf (μ G) (⊢fold wfA da dt) with lamInv da
      ... | B′ , q′ , Ψ₀ , eqT , dr with cod≡ eqT
      ...   | refl with rollInv dr
      ...     | wfB , _ , _ , dl = covL G wfA wfB dl
      covOf (μ G) (⊢sub-use _ d) = covOf (μ G) d
      covOf (μ G) (⊢sub-eff _ d) = covOf (μ G) d
      covOf (ν G f) (⊢unfold wfB dc dt) with lamInv dc
      ... | B′ , q′ , Ψ₀ , eqT , db with dom≡ eqT | cod≡ eqT
      ...   | refl | refl with letInv db
      ...     | _ , _ , _ , _ , _ , de , dl with outInv de
      ...       | _ , _ , _ , _ , refl , wfA , dv with varTy dv
      ...         | refl = covL G wfA wfB dl
      covOf (ν G f) (⊢sub-use _ d) = covOf (ν G f) d
      covOf (ν G f) (⊢sub-eff _ d) = covOf (ν G f) d

      covL : ∀ {n} {Γ : Ctx m n} {Ψ π} {R : Ty m} H {h y} → WFFun Δ (H ⟨ at₀ A ⟩F) → WFFun Δ (H ⟨ at₀ B ⟩F)
           → Δ ⊩ Γ ⊢[ Ψ ] mapLayerᶜ A B R H h y ∷ ⟦ H ⟨ at₀ B ⟩F ⟧F R ! π → CovF H
      covL (K C) (wf-K bA) (wf-K bB) d = covOf C d , bA , bB
      covL Id wfA wfB d = tt
      covL (H₁ ⊕ H₂) wfA wfB (⊢case ds dl dr) with inlInv dl | inrInv dr
      ... | _ , _ , d₁ | _ , _ , d₂ = covL H₁ (wf₁ wfA) (wf₁ wfB) d₁ , covL H₂ (wf₂ wfA) (wf₂ wfB) d₂
      covL (H₁ ⊕ H₂) wfA wfB (⊢sub-use _ d) = covL (H₁ ⊕ H₂) wfA wfB d
      covL (H₁ ⊕ H₂) wfA wfB (⊢sub-eff _ d) = covL (H₁ ⊕ H₂) wfA wfB d
      covL (H₁ ⊗ H₂) wfA wfB (⊢pair d₁ d₂) = covL H₁ (wf₁⊗ wfA) (wf₁⊗ wfB) d₁ , covL H₂ (wf₂⊗ wfA) (wf₂⊗ wfB) d₂
      covL (H₁ ⊗ H₂) wfA wfB (⊢sub-use _ d) = covL (H₁ ⊗ H₂) wfA wfB d
      covL (H₁ ⊗ H₂) wfA wfB (⊢sub-eff _ d) = covL (H₁ ⊗ H₂) wfA wfB d
