{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws.FoldRoll — the recursion schemes, inside the language
-- (`Spec.Metatheory.Equations.fold-roll`, `out-unfold`): folding a rolled
-- layer is the algebra after the layer map of the fold; forcing an unfold
-- is the layer map of the unfold after the coalgebra. The fold's argument
-- runs once on each side, its effects included.
------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc)
open import Once.Spec.Signature using (Signature; OneName)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Laws.FoldRoll (Σ : Signature) (u : OneName Σ) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Sum using (inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)
open import Once.Spec.Grade using (Quantity; Many; mk-kind; Purity; pure; _⊑π_; ⊑-pure)
open import Once.Spec.Type using (Ty; Fun; KCtx; WFFun; TySub; Respects; ∅ₖ; _⟨_⟩; _⟨_⟩F; _⇒[_]_; μ; ⟦_⟧F; at₀)
open import Once.Spec.Context using (Ctx)
open import Once.Spec.Core.Syntax
open import Once.Spec.Core.Derived using (composeᶜ; cataᶜ; inᶜ; layerᶜ; mapᶜ)
open import Once.Spec.Core.Typing Σ S
open import Once.Spec.Core.Meaning Σ fmt S
open import Once.Spec.Effect Σ using (M; sub; T∞; _>>=∞_; return∞; toT∞)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ; code; toL; fromL; foldM)
open import Once.Spec.Polynomial using (inS; sfmap)
open import Once.Spec.Equivalence Σ using (Same)
open import Once.Spec.Metatheory using (_≅_; Pure)
open import Once.Metatheory.Bisim Σ using (≈-sym; ≈-trans; ≈-bind; ≈-refl; idˡ; idʳ; assoc)
open import Once.Metatheory.Laws.Compose Σ u fmt S using (≡→≈)
open import Once.Metatheory.Coherence.Relation Σ using (Related; ≈-Relatedˡ; ≈-Relatedʳ; bindRel; returnRel; returnRel⁻; toObserved; fromObserved)
open import Once.Metatheory.Coherence.Layer Σ using (rel; runs; module Functor)
open import Once.Metatheory.Coherence.PER Σ using (Same-sym; Same-trans)
open import Once.Metatheory.Coherence.Uniqueness Σ S using (ty-unique)
open import Once.Metatheory.Laws.Tools Σ u fmt S
open import Once.Metatheory.Laws.Views Σ u fmt S
open import Once.Metatheory.Laws.Categorical Σ u fmt S using (toSameP; fromSameP)
open import Once.Metatheory.Laws.MapSem Σ using (module MapAt)
open import Once.Metatheory.Laws.MapLaws Σ using (module MapResp)
open import Once.Metatheory.Laws.MapTop Σ u fmt S using (module MapTopV)
open import Once.Metatheory.Laws.LayerTy using (layerT; layerTy)
open import Once.Metatheory.Laws.LayerSem Σ using (module LayerSem)
open import Once.Metatheory.Laws.CataSem Σ u fmt S using (module CataV)
open import Once.Metatheory.Laws.CataLaws Σ u fmt S using (cataTy; kind≡; module Transport)
open import Once.Metatheory.Laws.MapCov Σ S using (letInv; lamInv; foldInv; dom≡; cod≡)
open import Once.Metatheory.Laws.Strengthen Σ S using (varTy)
open import Once.Metatheory.Laws.MapV Σ u fmt S using (module MapV)
open import Once.Metatheory.Coherence.Layer Σ using (appMany)

module _ {m : ℕ} {Δ : KCtx m} where

  -- A `cataᶜ` of an algebra at `⟦ F ⟧F A ⇒ A` returns `A`.
  cataCod : ∀ {n} {Γ : Ctx m n} {Ψ π W F A alg Ψp}
          → Δ ⊩ Γ ⊢[ Ψ ] cataᶜ F pure alg ∷ μ F ⇒[ mk-kind Many pure ] W ! π
          → Δ ⊩ Γ ⊢[ Ψp ] alg ∷ ⟦ F ⟧F A ⇒[ mk-kind Many pure ] A ! pure → W ≡ A
  cataCod d dp with letInv d
  ... | E , _ , _ , _ , _ , dalg , db with lamInv db
  ...   | W′ , _ , _ , refl , dt with foldInv dt
  ...     | wf , _ , _ , _ , dv = cod≡ {Δ = Δ} (trans (varTy dv) (ty-unique dalg dp))

  -- Folding a rolled layer: the algebra, after the layer map of the fold.
  fold-roll : ∀ {n} {Γ : Ctx m n} {Ψ F A π alg t}
            → Pure Σ fmt S Δ Γ alg (⟦ F ⟧F A ⇒[ mk-kind Many pure ] A)
            → (d : Δ ⊩ Γ ⊢[ Ψ ] fold F alg (roll F t) ∷ A ! π)
              (d′ : Δ ⊩ Γ ⊢[ Ψ ] app alg (app (layerᶜ F (μ F) A (cataᶜ F pure alg)) t) ∷ A ! π)
            → _≅_ Σ fmt S d d′
  fold-roll {Γ = Γ} {Ψ} {F} {A} {π} {alg} {t} (Ψp , dp) d d′ δ sd σ r γ sγ = sameM {A ⟨ σ ⟩} {π} (rel GO)
    where
      open Views δ sd σ r γ sγ
      open ProdV δ sd σ r γ sγ using (pureRet)
      module CV = CataV δ sd σ r
      module MT = MapTopV δ sd σ r (μ F) A
      module LS = LayerSem σ
      module FR = MapV.FoldR δ sd σ r A A γ sγ
      module FV = FunV δ sd σ r γ sγ
      open Transport δ σ r
      L  = ⟦ F ⟧F (μ F)
      FA = ⟦ F ⟧F A
      AT = FA ⇒[ mk-kind Many pure ] A
      MA = μ F ⇒[ mk-kind Many pure ] A
      eTT : (L ⇒[ mk-kind Many pure ] FA) ≡ (layerT F ⟨ at₀ (μ F) ⟩ ⇒[ mk-kind Many pure ] layerT F ⟨ at₀ A ⟩)
      eTT = cong₂ (λ P Q → P ⇒[ mk-kind Many pure ] Q) (sym (layerTy F (μ F))) (sym (layerTy F A))
      inv : V L → V (μ F)
      inv l = inS (toL σ F (μ F) l)

      GO : _~_ {A} (⟪ d ⟫ γ) (⟪ d′ ⟫ γ)
      GO with FR.viewFold d base | FV.viewApp d′ base
      ... | FR.foldView wf da dv {ea} {ev} ra rv eqF | FV.appView df₁ dx₁ {ef₁} rf₁ sem₁ with ty-unique da dp | ty-unique df₁ dp
      ...   | refl | refl with sem₁ | FR.viewRoll dv rv
      ...     | (ex , rx , eqA) | FR.rollView wf′ dt {e₀} rt eqR with FV.viewApp dx₁ rx
      ...       | FV.appView {Ψ₁ = ΨL} {π₁ = πL} dL dt′ {eL} rL sem₂ with MT.mapTy (layerT F) dL
      ...         | (W , eqL) with kind≡ {Δ = Δ} eqL
      ...           | refl , refl with trans (dom≡ {Δ = Δ} eqL) (layerTy F (μ F))
      ...             | refl with viewLet dL rL
      ...               | letView de db {eb} rb (ee , re , eqLet) with cataTy de
      ...                 | (W₀ , refl) with cataCod de dp
      ...                   | refl = ~trans {A} LHS (~trans {A} MID (~sym {A} RHS))
        where
          pa  = ⟦ transfer dp da ⟧ δ σ r ea
          pa₁ = ⟦ transfer dp df₁ ⟧ δ σ r ef₁
          s01 : Same (AT ⟨ σ ⟩) pa pa₁
          s01 = returnRel⁻ (runs (fl (transfer dp da) (transfer dp df₁) ra rf₁))
          cv  = CV.cataᵛ F A pa
          cv₁ = CV.cataᵛ F A pa₁

          -- The fold of a rolled layer: the algebra after the layer map of the fold.
          LHS : _~_ {A} (⟪ d ⟫ γ) (⟪ dt ⟫ e₀ >>=∞ λ l → return∞ (pa (LS.LAYER F cv l)))
          LHS = ~trans {A} eqF
            (≈-Relatedʳ (≈-sym (≈-trans (idˡ pa _) (≈-trans (assoc _ _ _) (≈-bind (≈-refl _) (λ l →
                           ≈-trans (idˡ (inv l) _) (≡→≈ (cong return∞ (cong pa (LS.foldLayer F (λ l′ → pa (fromL σ F A l′)) F l)))))))))
              (bindRel {g = λ g → (⟪ dt ⟫ e₀ >>=∞ λ l → return∞ (inv l)) >>=∞ λ v → return∞ (CV.cataᵛ F A g v)} (pureRet da dp ra)
                (λ {g} {g′} sg → bindRel {g = λ v → return∞ (CV.cataᵛ F A g′ v)} eqR
                  (λ sv → returnRel (fromSameP σ {X = μ F} {Y = A} (CV.cataResp wf sg) sv)))))

          -- `cata alg`, inside the layer map: the fold of the algebra.
          CATA₁ : _~_ {MA} (⟪ de ⟫ ee) (return∞ cv₁)
          CATA₁ = ~trans {MA} (CV.cataSem γ sγ de re df₁ rf₁)
                    (≈-Relatedˡ (≈-bind (≈-refl _) (λ _ → ≈-refl _))
                      (≈-Relatedʳ (≈-sym (idˡ pa₁ _))
                        (bindRel {g = λ g → return∞ (CV.cataᵛ F A g)} (pureRet df₁ dp rf₁) (λ sg → returnRel (CV.cataResp wf sg)))))

          dLT = subst (λ Z → Δ ⊩ Γ ⊢[ ΨL ] layerᶜ F (μ F) A (cataᶜ F pure alg) ∷ Z ! πL) eTT dL
          c   = MT.covD (layerT F) dLT
          Φ   = MT.Φcall (layerT F) {X = μ F} {Y = A} {q = Many} (λ _ → refl) (λ _ → refl)
          CL : V MA → V (layerT F ⟨ at₀ (μ F) ⟩ ⇒[ mk-kind Many pure ] layerT F ⟨ at₀ A ⟩)
          CL hv x = MapAt.mapS Δ σ (μ F) A (layerT F) c (Φ hv) x
          lv = subst V (sym eTT) (CL cv₁)

          LAYERED : _~_ {L ⇒[ mk-kind Many pure ] FA} (⟪ dL ⟫ eL) (return∞ lv)
          LAYERED = ~trans {L ⇒[ mk-kind Many pure ] FA}
            (relBack {π = πL} eTT {mv = ⟦ dL ⟧ δ σ r eL}
               (subst (λ m₀ → Related (Same ((layerT F ⟨ at₀ (μ F) ⟩ ⇒[ mk-kind Many pure ] layerT F ⟨ at₀ A ⟩) ⟨ σ ⟩)) (toT∞ πL m₀)
                                (⟪ de ⟫ ee >>=∞ λ hv → return∞ (CL hv)))
                  (meaningSubst eTT dL eL)
               (MT.mapSem γ sγ (layerT F) dLT rL de re Φ (MT.HΦcall (layerT F) {X = μ F} {Y = A} {q = Many} (λ _ → refl) (λ _ → refl)))))
            (≈-Relatedʳ (≈-sym (≈-trans (≈-bind (idˡ cv₁ _) (λ _ → ≈-refl _)) (idˡ (CL cv₁) _)))
              (bindRel {g = λ v → return∞ (subst V (sym eTT) v)}
                (bindRel {g = λ hv → return∞ (CL hv)} CATA₁ (λ {hv} {hv′} sh → returnRel
                  (toSameP σ {X = layerT F ⟨ at₀ (μ F) ⟩} {Y = layerT F ⟨ at₀ A ⟩}
                    (λ sx → MapResp.resp σ r (μ F) A (layerT F) c c
                              (MT.ΦcallResp (layerT F) {X = μ F} {Y = A} {q = Many} (λ _ → refl) (λ _ → refl) sh) sx))))
                (λ sv → returnRel (sameSubst (sym eTT) sv))))

          -- The argument: the layer map of the fold, after `t`.
          INNER : _~_ {FA} (⟪ dx₁ ⟫ ex) (⟪ dt ⟫ e₀ >>=∞ λ l → return∞ (lv l))
          INNER = FV.appMany~ dL dt′ sem₂ LAYERED (λ rx′ → runs (fl dt′ dt rx′ rt))

          RHS : _~_ {A} (⟪ d′ ⟫ γ) (⟪ dt ⟫ e₀ >>=∞ λ l → return∞ (pa₁ (lv l)))
          RHS = ~trans {A} eqA
            (≈-Relatedʳ (≈-sym (≈-trans (idˡ pa₁ _) (≈-trans (assoc _ _ _) (≈-bind (≈-refl _) (λ l → idˡ (lv l) _)))))
              (bindRel {g = λ h → (⟪ dt ⟫ e₀ >>=∞ λ l → return∞ (lv l)) >>=∞ λ a → return∞ (h a)} (pureRet df₁ dp rf₁)
                (λ {h} {h′} sh → bindRel {g = λ a → return∞ (h′ a)} INNER (λ sa → runs (appMany {pure} {FA ⟨ σ ⟩} {A ⟨ σ ⟩} sh sa)))))

          CORE : ∀ {l l′} → Same (L ⟨ σ ⟩) l l′ → Same (A ⟨ σ ⟩) (pa (LS.LAYER F cv l)) (pa₁ (lv l′))
          CORE {l} {l′} sl = fromSameP σ {X = FA} {Y = A} s01
                               (Same-sym (FA ⟨ σ ⟩) (subst₂′ {X = FA} e₂ (cong (LS.LAYER F cv) (sym (substSym (layerTy F (μ F)) l))) AGREE))
            where
              tm = subst V (sym (layerTy F (μ F))) l′
              e₂ : lv l′ ≡ LS.tr F A (CL cv₁ tm)
              e₂ = trans (funBack (sym (layerTy F (μ F))) (sym (layerTy F A)) (CL cv₁) l′) (symsym (layerTy F A) (CL cv₁ tm))
              AGREE : Same (FA ⟨ σ ⟩) (LS.tr F A (CL cv₁ tm)) (LS.LAYER F cv (LS.tr F (μ F) (subst V (sym (layerTy F (μ F))) l)))
              AGREE = LS.agree {Δ = Δ} r (μ F) A F wf c (Φ cv₁) cv
                        (λ o a a′ sa → fromSameP σ {X = μ F} {Y = A} (CV.cataResp wf (Same-sym (AT ⟨ σ ⟩) s01)) sa)
                        (sameSubst (sym (layerTy F (μ F))) (Same-sym (L ⟨ σ ⟩) sl))

          MID : _~_ {A} (⟪ dt ⟫ e₀ >>=∞ λ l → return∞ (pa (LS.LAYER F cv l))) (⟪ dt ⟫ e₀ >>=∞ λ l → return∞ (pa₁ (lv l)))
          MID = bindRel {g = λ l′ → return∞ (pa₁ (lv l′))} (runs (fl dt dt rt rt)) (λ sl → returnRel (CORE sl))
