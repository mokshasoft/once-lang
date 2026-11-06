{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws.MapV.Map — the map lemma `bodyMap`: the dispatch over the type that
-- ties the cases of `Sum`, `Lam` and `Fix` together. The only recursive definitions.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature; OneName)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Laws.MapV.Map (Σ : Signature) (u : OneName Σ) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

open import Data.Nat using (suc)
open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)
open import Once.Spec.Grade using (Quantity; Zero; One; Many; mk-kind; Purity; pure; positionGrade; 0≤q; _·p_)
open import Once.Spec.Type using (Ty; Fun; KCtx; WFFun; ⟦_⟧F; _⟨_⟩F; K; Id; _⊕_; _⊗_; TySub; Respects; ∅ₖ; _⟨_⟩; _⇒[_]_; _*_; _+_; var; Unit; Void; Int; Float; μ; ν;
                                  at₀)
open import Once.Spec.Context using (Ctx; _▸_; _∷_; Usage; lookup; _⊑ᵘ_; _⊑∷_)
open import Once.Spec.Core.Syntax
open import Once.Spec.Core.Derived using (mapAtᶜ; mapLayerᶜ)
open import Once.Spec.Core.Typing Σ S
open import Once.Spec.Core.Meaning Σ fmt S
open import Once.Spec.Effect Σ using (T∞; _>>=∞_; return∞; toT∞; fmap)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ; code; toL; fromL; foldM; layerM)
open import Once.Spec.Polynomial using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF; μS; inS)
open import Once.Spec.Effect Σ using (LayerEq; νM; ana)
open νM using (outν)
open import Once.Spec.Grade using (Finite; fin)
open import Once.Spec.Equivalence Σ using (Same; SameM)
open import Once.Spec.Metatheory using (SameDefs; SameEnv)
open import Once.Metatheory.Bisim Σ using (≈-sym; ≈-trans; ≈-bind; ≈-refl; idˡ; assoc)
open import Once.Metatheory.Coherence.Relation Σ using (Related; ≈-Relatedˡ; ≈-Relatedʳ; bindRel; returnRel; returnRel⁻; toObserved; fromObserved; LayerEq-mono)
open import Once.Metatheory.Laws.MapLaws Σ using (module CovWF)
open import Once.Metatheory.Coherence.Layer Σ using (appZero; rel; runs; module Functor; module Fold; module Ana; outRel; LayerEq-∀; relatedFmap)
open import Once.Metatheory.Erase Σ using (toT∞-fmap; toT∞-bindᵍ)
open import Once.Metatheory.Coherence.PER Σ using (Same-sym)
open import Once.Metatheory.Laws.Tools Σ u fmt S
open import Once.Metatheory.Laws.Views Σ u fmt S
open import Once.Metatheory.Laws.Strengthen Σ S using (varTy; str)
open import Once.Metatheory.Laws.Compose Σ u fmt S using (ValAt; valAt0; module CompV; ≡→≈)
open import Once.Metatheory.Laws.ComposeG Σ u fmt S using (callRel)
open import Once.Metatheory.Laws.MapSem Σ using (module MapAt; Occ; OccF; p-var; p-*ˡ; p-*ʳ; p-+ˡ; p-+ʳ; p-⇒ʳ; p-μ; p-ν; p-K; p-⊕ˡ; p-⊕ʳ; p-⊗ˡ; p-⊗ʳ)
open import Once.Metatheory.Laws.MapV Σ u fmt S using (module MapV)
open import Once.Metatheory.Laws.MapV.Sum Σ u fmt S using (module MapVSum)
open import Once.Metatheory.Laws.MapV.Lam Σ u fmt S using (module MapVLam)
open import Once.Metatheory.Laws.MapV.Fix Σ u fmt S using (module MapVFix)

module MapVMap {m : ℕ} {Δ : KCtx m} (δ : DefSem) (sd : SameDefs Σ fmt S δ) (σ : TySub m 0) (r : Respects Δ ∅ₖ σ)
            (A B : Ty m) where
  open MapAt Δ σ A B
  open MapV δ sd σ r A B
  open Reads
  open MapVSum δ sd σ r A B
  open MapVLam δ sd σ r A B
  open MapVFix δ sd σ r A B

  -- The dispatch: the only recursive definitions.
  bodyMapT  : ∀ T → BodyAt T
  layerMapT : ∀ R H → LayerAt R H
  bodyMapT (var fz)     = bodyVar0
  bodyMapT (var (fs i)) γ sγ c Rh Rx sx Hc db ra = rd Rx db ra
  bodyMapT Unit         γ sγ c Rh Rx sx Hc db ra = rd Rx db ra
  bodyMapT Void         γ sγ c Rh Rx sx Hc db ra = rd Rx db ra
  bodyMapT Int          γ sγ c Rh Rx sx Hc db ra = rd Rx db ra
  bodyMapT Float        γ sγ c Rh Rx sx Hc db ra = rd Rx db ra
  bodyMapT (T₁ * T₂)    = bodyProd {T₁} {T₂} (bodyMapT T₁) (bodyMapT T₂)
  bodyMapT (T₁ + T₂)    = bodySum {T₁} {T₂} (bodyMapT T₁) (bodyMapT T₂)
  bodyMapT (T₁ ⇒[ mk-kind Zero π ] T₂) = bodyLam0 {T₁} {T₂} {π} (bodyMapT T₂)
  bodyMapT (T₁ ⇒[ mk-kind One π ] T₂)  = bodyLam1 {T₁} {T₂} {π} (bodyMapT T₂)
  bodyMapT (T₁ ⇒[ mk-kind Many π ] T₂) = bodyLamω {T₁} {T₂} {π} (bodyMapT T₂)
  bodyMapT (μ G)        = bodyMu {G} (layerMapT (μ (G ⟨ at₀ B ⟩F)) G)
  bodyMapT (ν G f)      = bodyNu {G} {f} (layerMapT (ν (G ⟨ at₀ A ⟩F) f) G)
  layerMapT R (K C)     γ sγ c Rh Ry sy Hc d ra = bodyMapT C γ sγ (proj₁ c) Rh Ry sy (λ o → Hc (p-K o)) d ra
  layerMapT R Id        γ sγ c Rh Ry sy Hc d ra = rd Ry d ra
  layerMapT R (H₁ ⊗ H₂) = layerProd {R} {H₁} {H₂} (layerMapT R H₁) (layerMapT R H₂)
  layerMapT R (H₁ ⊕ H₂) = layerSum {R} {H₁} {H₂} (layerMapT R H₁) (layerMapT R H₂)

  bodyMap : ∀ {n} {Γ : Ctx m n} {Ψ} (γ : Env σ Γ Ψ) (sγ : SameEnv Σ fmt S σ Γ Ψ γ) T (c : Cov T) {φ : Fn T}
              {F : Ty m} {hv : ⟦ F ⟨ σ ⟩ ⟧ᵛ} {xv : VA T} {h x : Tm S m n}
          → Reads γ sγ h F hv → Reads γ sγ x (T ⟨ at₀ A ⟩) xv → Same (T ⟨ at₀ A ⟩ ⟨ σ ⟩) xv xv → HCall T φ F hv
          → ∀ {Ψa π} (db : Δ ⊩ Γ ⊢[ Ψa ] mapAtᶜ A B T h x ∷ T ⟨ at₀ B ⟩ ! π) {γa} → Views.Res δ sd σ r γ sγ γa
          → Related (Same (T ⟨ at₀ B ⟩ ⟨ σ ⟩)) (toT∞ π (⟦ db ⟧ δ σ r γa)) (return∞ (mapS T c φ xv))
  bodyMap γ sγ T = bodyMapT T γ sγ
