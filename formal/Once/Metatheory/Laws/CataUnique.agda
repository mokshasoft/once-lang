{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws.CataUnique — `cata alg` is the only algebra map
-- (`Spec.Metatheory.Categorical.cata-uniqueᶜ`): a pure `h` with
-- `h ∘ in ≅ alg ∘ layer h` (at the conclusion's usage) commutes with the
-- constructor, so it agrees with the fold on every tree, by induction
-- (`Laws.LayerSem.Unique`).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature; OneName)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Laws.CataUnique (Σ : Signature) (u : OneName Σ) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

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
open import Once.Metatheory.Bisim Σ using (≈-sym; ≈-trans; ≈-bind; ≈-refl; idˡ; idʳ)
open import Once.Metatheory.Coherence.Relation Σ using (LayerEq-mono; Related; ≈-Relatedˡ; ≈-Relatedʳ; bindRel; returnRel; returnRel⁻; toObserved; fromObserved)
open import Once.Metatheory.Coherence.Layer Σ using (rel; runs; module Functor)
open import Once.Metatheory.Coherence.PER Σ using (Same-sym; Same-trans)
open import Once.Metatheory.Coherence.Uniqueness Σ S using (ty-unique)
open import Once.Metatheory.Laws.Tools Σ u fmt S
open import Once.Metatheory.Laws.Views Σ u fmt S
open import Once.Metatheory.Laws.Categorical.Tools Σ u fmt S using (toSameP; fromSameP)
open import Once.Metatheory.Laws.ComposeShape Σ u fmt S using (Shape; shape; compShape)
open import Once.Metatheory.Laws.ComposeG Σ u fmt S using (liftᵛ; module CompGV)
open import Once.Metatheory.Laws.Compose Σ u fmt S using (compᵛ)
open import Once.Metatheory.Laws.MapSem Σ using (module MapAt)
open import Once.Metatheory.Laws.MapLaws Σ using (module MapResp)
open import Once.Metatheory.Laws.Assoc Σ u fmt S using (compCong)
open import Once.Metatheory.Laws.MapTop Σ u fmt S using (module MapTopV)
open import Once.Metatheory.Laws.LayerTy using (layerT; layerTy)
open import Once.Metatheory.Laws.LayerSem Σ using (module LayerSem; module Unique; eqLayer)
open import Once.Metatheory.Laws.CataSem Σ u fmt S using (module CataV)
open import Once.Metatheory.Laws.CataLaws Σ u fmt S using (cataWF; inTy; kind≡; module Transport)

module _ {m : ℕ} {Δ : KCtx m} where

  private
    subPure : ∀ {X : Set} (p : pure ⊑π pure) (x : X) → sub p x ≡ x
    subPure ⊑-pure x = refl

  -- μ F is the initial algebra: an algebra map is the fold.
  cata-uniqueᶜ : ∀ {n} {Γ : Ctx m n} {Ψ F A π₀ π′ alg h}
               → Pure Σ fmt S Δ Γ alg (⟦ F ⟧F A ⇒[ mk-kind Many pure ] A) → Pure Σ fmt S Δ Γ h (μ F ⇒[ mk-kind Many pure ] A)
               → (e : Δ ⊩ Γ ⊢[ Ψ ] composeᶜ (⟦ F ⟧F (μ F)) pure h (inᶜ F) ∷ ⟦ F ⟧F (μ F) ⇒[ mk-kind Many pure ] A ! π′)
                 (e′ : Δ ⊩ Γ ⊢[ Ψ ] composeᶜ (⟦ F ⟧F (μ F)) pure alg (layerᶜ F (μ F) A h)
                                     ∷ ⟦ F ⟧F (μ F) ⇒[ mk-kind Many pure ] A ! π′)
               → _≅_ Σ fmt S e e′
               → (d : Δ ⊩ Γ ⊢[ Ψ ] h ∷ μ F ⇒[ mk-kind Many pure ] A ! π₀)
                 (d′ : Δ ⊩ Γ ⊢[ Ψ ] cataᶜ F pure alg ∷ μ F ⇒[ mk-kind Many pure ] A ! π₀)
               → _≅_ Σ fmt S d d′
  cata-uniqueᶜ {Γ = Γ} {Ψ} {F} {A} {π₀} {π′} {alg} {h} (Ψa , dpa) (Ψh , dph) e e′ he d d′ δ sd σ r γ sγ =
    sameM {MA ⟨ σ ⟩} {π₀} (rel (GO (compShape e) (AV.armsLL (inj₂ refl) e) (compShape e′) (AV.armsLL (inj₂ refl) e′)))
    where
      open Views δ sd σ r γ sγ
      open ProdV δ sd σ r γ sγ using (pureRet)
      module AV = ArmsV δ sd σ r γ sγ
      module G  = CompGV δ sd σ r
      module CV = CataV δ sd σ r
      module MT = MapTopV δ sd σ r (μ F) A
      module LS = LayerSem σ
      module Fn = Functor σ r
      open Transport δ σ r
      L  = ⟦ F ⟧F (μ F)
      FA = ⟦ F ⟧F A
      AT = FA ⇒[ mk-kind Many pure ] A
      TT = L ⇒[ mk-kind Many pure ] A
      MA = μ F ⇒[ mk-kind Many pure ] A
      eTT : (L ⇒[ mk-kind Many pure ] FA) ≡ (layerT F ⟨ at₀ (μ F) ⟩ ⇒[ mk-kind Many pure ] layerT F ⟨ at₀ A ⟩)
      eTT = cong₂ (λ P Q → P ⇒[ mk-kind Many pure ] Q) (sym (layerTy F (μ F))) (sym (layerTy F A))
      inv : V L → V (μ F)
      inv l = inS (toL σ F (μ F) l)

      -- `h`, the value.
      hv = ⟦ transfer dph d ⟧ δ σ r γ
      shv : Same (MA ⟨ σ ⟩) hv hv
      shv = returnRel⁻ (runs (fl (transfer dph d) (transfer dph d) base base))
      HV : _~_ {MA} (⟪ d ⟫ γ) (return∞ hv)
      HV = pureRet d dph base

      GO : Shape L pure TT h (inᶜ F) → AV.Arms e h (inᶜ F)
         → Shape L pure TT alg (layerᶜ F (μ F) A h) → AV.Arms e′ alg (layerᶜ F (μ F) A h)
         → _~_ {MA} (⟪ d ⟫ γ) (⟪ d′ ⟫ γ)
      GO (shape eT tyF tyG lf lg zp) (AV.arms dh di Ph Pi) (shape eT′ tyF′ tyG′ lf′ lg′ zp′) (AV.arms {Ψg = Ψl} {πg = πl} da dl Pa Pl)
        with eT | tyF dh | tyG di | eT′ | tyF′ da | tyG′ dl
      ... | refl | refl | refl | refl | refl | refl with ty-unique dh d | inTy di | ty-unique da dpa | MT.mapTy (layerT F) dl
      ...   | refl | refl | refl | (W , eqL) with kind≡ {Δ = Δ} eqL
      ...     | refl , refl = ~trans {MA} HV (~trans {MA} (returnRel UNIQUE) (~sym {MA} CATA))
        where
          rh = resR base Ph
          ri = resR base Pi
          ra = resR base Pa
          rl = resR base Pl
          wf = cataWF d′
          pa = ⟦ transfer dpa da ⟧ δ σ r (restrict σ Pa γ)
          spa : Same (AT ⟨ σ ⟩) pa pa
          spa = returnRel⁻ (runs (fl (transfer dpa da) (transfer dpa da) ra ra))
          cv = CV.cataᵛ F A pa

          -- `cata alg` runs `alg`, a value: the fold of it.
          CATA : _~_ {MA} (⟪ d′ ⟫ γ) (return∞ cv)
          CATA = ~trans {MA} (CV.cataSem γ sγ d′ base da ra)
                   (≈-Relatedˡ (≈-bind (≈-refl _) (λ _ → ≈-refl _))
                     (≈-Relatedʳ (≈-sym (idˡ pa _))
                       (bindRel {g = λ g → return∞ (CV.cataᵛ F A g)} (pureRet da dpa ra) (λ sg → returnRel (CV.cataResp wf sg)))))

          -- The `h` that `e` runs: the same as `d`'s.
          hvE = ⟦ transfer dph dh ⟧ δ σ r (restrict σ Ph γ)
          sEh : Same (MA ⟨ σ ⟩) hvE hv
          sEh = returnRel⁻ (runs (fl (transfer dph dh) (transfer dph d) rh base))

          LHS : _~_ {TT} (⟪ e ⟫ γ) (return∞ (compᵛ pure (liftᵛ Many lf hvE) (liftᵛ Many lg inv)))
          LHS = ~trans {TT} (G.compSemG γ sγ e base dh rh di ri lf lg zp)
            (≈-Relatedʳ (≈-sym (≈-trans (idˡ hvE _) (idˡ inv _)))
              (bindRel {g = λ c → return∞ inv >>=∞ λ i → return∞ (compᵛ pure (liftᵛ Many lf c) (liftᵛ Many lg i))} (pureRet dh dph rh)
                (λ {c} {c′} sc → bindRel {g = λ i → return∞ (compᵛ pure (liftᵛ Many lf c′) (liftᵛ Many lg i))} (CV.inSem γ sγ di ri)
                  (λ {i} {i′} si → returnRel (λ x x′ sx → toObserved (returnRel
                    (subst₂′ {X = A} (subPure lf (c (sub lg (i x)))) (subPure lf (c′ (sub lg (i′ x′))))
                      (fromSameP σ {X = μ F} {Y = A} sc
                        (subst₂′ {X = μ F} (subPure lg (i x)) (subPure lg (i′ x′)) (fromSameP σ {X = L} {Y = μ F} si sx))))))))))

          el  = restrict σ Pl γ
          dlT = subst (λ Z → Δ ⊩ Γ ⊢[ Ψl ] layerᶜ F (μ F) A h ∷ Z ! πl) eTT dl
          c   = MT.covD (layerT F) dlT
          Φ   = MT.Φcall (layerT F) {X = μ F} {Y = A} {q = Many} (λ _ → refl) (λ _ → refl)
          CL : V MA → V (layerT F ⟨ at₀ (μ F) ⟩ ⇒[ mk-kind Many pure ] layerT F ⟨ at₀ A ⟩)
          CL gv x = MapAt.mapS Δ σ (μ F) A (layerT F) c (Φ gv) x
          lv = subst V (sym eTT) (CL hv)

          LAYERED : _~_ {L ⇒[ mk-kind Many pure ] FA} (⟪ dl ⟫ _) (return∞ lv)
          LAYERED = ~trans {L ⇒[ mk-kind Many pure ] FA}
            (relBack {π = πl} eTT {mv = ⟦ dl ⟧ δ σ r el}
               (subst (λ m₀ → Related (Same ((layerT F ⟨ at₀ (μ F) ⟩ ⇒[ mk-kind Many pure ] layerT F ⟨ at₀ A ⟩) ⟨ σ ⟩)) (toT∞ πl m₀)
                                (⟪ d ⟫ γ >>=∞ λ gv → return∞ (CL gv)))
                  (meaningSubst eTT dl el)
               (MT.mapSem γ sγ (layerT F) dlT rl d base Φ (MT.HΦcall (layerT F) {X = μ F} {Y = A} {q = Many} (λ _ → refl) (λ _ → refl)))))
            (≈-Relatedʳ (≈-sym (≈-trans (≈-bind (idˡ hv _) (λ _ → ≈-refl _)) (idˡ (CL hv) _)))
              (bindRel {g = λ v → return∞ (subst V (sym eTT) v)}
                (bindRel {g = λ gv → return∞ (CL gv)} HV (λ {gv} {gv′} sg → returnRel
                  (toSameP σ {X = layerT F ⟨ at₀ (μ F) ⟩} {Y = layerT F ⟨ at₀ A ⟩}
                    (λ sx → MapResp.resp σ r (μ F) A (layerT F) c c
                              (MT.ΦcallResp (layerT F) {X = μ F} {Y = A} {q = Many} (λ _ → refl) (λ _ → refl) sg) sx))))
                (λ sv → returnRel (sameSubst (sym eTT) sv))))

          RHS : _~_ {TT} (⟪ e′ ⟫ γ) (return∞ (compᵛ pure (liftᵛ Many lf′ pa) (liftᵛ Many lg′ lv)))
          RHS = ~trans {TT} (G.compSemG γ sγ e′ base da ra dl rl lf′ lg′ zp′)
            (≈-Relatedʳ (≈-sym (≈-trans (idˡ pa _) (idˡ lv _)))
              (bindRel {g = λ a → return∞ lv >>=∞ λ l → return∞ (compᵛ pure (liftᵛ Many lf′ a) (liftᵛ Many lg′ l))} (pureRet da dpa ra)
                (λ {a} {a′} sa → bindRel {g = λ l → return∞ (compᵛ pure (liftᵛ Many lf′ a′) (liftᵛ Many lg′ l))} LAYERED
                  (λ sl → returnRel (compCong pure {Many} {Many} lf′ lf′ lg′ lg′ sa sl)))))

          -- The hypothesis, at this environment: the two composites are the same.
          SAMEe : Same (TT ⟨ σ ⟩) (compᵛ pure (liftᵛ Many lf hvE) (liftᵛ Many lg inv)) (compᵛ pure (liftᵛ Many lf′ pa) (liftᵛ Many lg′ lv))
          SAMEe = returnRel⁻ (~trans {TT} (~sym {TT} LHS) (~trans {TT} (fromObserved (he δ sd σ r γ sγ)) RHS))

          -- So `h` commutes with the constructor, a layer at a time.
          HYPx : ∀ {x x′} → Same (L ⟨ σ ⟩) x x′ → Same (A ⟨ σ ⟩) (hv (inv x)) (pa (LS.LAYER F hv x′))
          HYPx {x} {x′} sx = Same-trans (A ⟨ σ ⟩) S1 (Same-trans (A ⟨ σ ⟩) (fromSameP σ {X = L} {Y = A} SAMEe sx) S3)
            where
              S1 : Same (A ⟨ σ ⟩) (hv (inv x)) (sub lf (hvE (sub lg (inv x))))
              S1 = subst₂′ {X = A} refl (trans (cong (λ y → sub lf (hvE y)) (subPure lg (inv x))) (subPure lf (hvE (inv x))))
                     (fromSameP σ {X = μ F} {Y = A} (Same-sym (MA ⟨ σ ⟩) sEh) (Fn.reflμ wf (inv x)))
              sx′ : Same (L ⟨ σ ⟩) x′ x′
              sx′ = Same-trans (L ⟨ σ ⟩) (Same-sym (L ⟨ σ ⟩) sx) sx
              tm = subst V (sym (layerTy F (μ F))) x′
              e₂ : sub lf′ (pa (sub lg′ (lv x′))) ≡ pa (LS.tr F A (CL hv tm))
              e₂ = trans (cong (λ y → sub lf′ (pa y)) (subPure lg′ (lv x′)))
                     (trans (subPure lf′ (pa (lv x′)))
                       (cong pa (trans (funBack (sym (layerTy F (μ F))) (sym (layerTy F A)) (CL hv) x′)
                                       (symsym (layerTy F A) (CL hv tm)))))
              AGREE : Same (FA ⟨ σ ⟩) (LS.tr F A (CL hv tm)) (LS.LAYER F hv (LS.tr F (μ F) tm))
              AGREE = LS.agree {Δ = Δ} r (μ F) A F wf c (Φ hv) hv (λ o a a′ sa → fromSameP σ {X = μ F} {Y = A} shv sa)
                        (sameSubst (sym (layerTy F (μ F))) sx′)
              S3 : Same (A ⟨ σ ⟩) (sub lf′ (pa (sub lg′ (lv x′)))) (pa (LS.LAYER F hv x′))
              S3 = subst₂′ {X = A} e₂ refl
                     (fromSameP σ {X = FA} {Y = A} spa
                       (subst₂′ {X = FA} refl (cong (LS.LAYER F hv) (sym (substSym (layerTy F (μ F)) x′))) AGREE))

          alg′ = λ l → pa (fromL σ F A l)

          hyp : ∀ w → Same (A ⟨ σ ⟩) (hv (inS w)) (alg′ (sfmap (code (F ⟨ σ ⟩F)) hv w))
          hyp w = subst₂′ {X = A} (cong (λ y → hv (inS y)) (sym (LS.toLfromL F (μ F) w)))
                    (cong pa (sym (LS.layerFromL F hv w)))
                    (HYPx (Fn.fromL-same wf (μ F) (LayerEq-mono (code (F ⟨ σ ⟩F)) (Fn.≡→sameμ wf) (eqLayer (code (F ⟨ σ ⟩F)) w))))

          module U = Unique (code (F ⟨ σ ⟩F)) (Same (A ⟨ σ ⟩)) (Same-trans (A ⟨ σ ⟩)) alg′
                       (λ p → fromSameP σ {X = FA} {Y = A} spa (Fn.fromL-same wf A p)) hv hyp

          UNIQUE : Same (MA ⟨ σ ⟩) hv cv
          UNIQUE = toSameP σ {X = μ F} {Y = A} λ {v} {v′} s → subst (λ w → Same (A ⟨ σ ⟩) (hv v) (cv w)) (Fn.sameμ wf s) (U.unique v)
