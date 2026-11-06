{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws.AnaLaws — `ν F` is the final F-coalgebra
-- (`Spec.Metatheory.Categorical.ana-βᶜ`, `ana-uniqueᶜ`): `out ∘ ana c` is
-- `layer (ana c) ∘ c`, forcing an unfold being mapping it over the
-- coalgebra's layer (`Laws.AnaSem.mapPRel`) and `layerᶜ` meaning that map.
------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc)
open import Once.Spec.Signature using (Signature; OneName)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Laws.AnaLaws (Σ : Signature) (u : OneName Σ) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

open import Data.Product using (_×_; _,_; Σ-syntax; proj₁)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong; cong₂)
open import Once.Spec.Grade using (Quantity; Many; mk-kind; Purity; pure; pureᶠ; _⊑π_; ⊑-pure)
open import Once.Spec.Type using (Ty; Fun; KCtx; WFFun; TySub; Respects; ∅ₖ; _⟨_⟩; _⟨_⟩F; _⇒[_]_; ν; ⟦_⟧F; at₀; K; Id; _⊕_; _⊗_)
open import Once.Spec.Context using (Ctx)
open import Once.Spec.Core.Syntax
open import Once.Spec.Core.Derived using (composeᶜ; anaᶜ; outᶜ; layerᶜ; mapᶜ)
open import Once.Spec.Core.Typing Σ S
open import Once.Spec.Core.Meaning Σ fmt S
open import Once.Spec.Effect Σ using (M; sub; T∞; _>>=∞_; return∞; toT∞; mapP; anaP; νM; LayerEq)
open import Once.Spec.Equivalence Σ using (SameNu)
open import Once.Spec.Polynomial using (SK; SId; _S⊕_; _S⊗_)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ; code; toL; fromL; foldM)
open import Once.Spec.Polynomial using (sfmap)
open import Once.Spec.Equivalence Σ using (Same)
open import Once.Spec.Metatheory using (_≅_; Pure)
open import Once.Metatheory.Bisim Σ using (≈-sym; ≈-trans; ≈-bind; ≈-refl; idˡ; idʳ)
open import Once.Metatheory.Coherence.Relation Σ using (LayerEq-mono; Related; ≈-Relatedˡ; ≈-Relatedʳ; bindRel; returnRel; returnRel⁻; toObserved; fromObserved)
open import Once.Metatheory.Coherence.Layer Σ using (rel; runs; module Functor; LayerEq-∀)
open import Once.Metatheory.Coherence.PER Σ using (Same-sym; Same-trans; SameNu-trans)
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
open import Once.Metatheory.Laws.LayerSem Σ using (module LayerSem)
open import Once.Metatheory.Laws.AnaSem Σ u fmt S using (module AnaV)
open import Once.Metatheory.Laws.CataLaws Σ u fmt S using (kind≡; module Transport)
open import Once.Metatheory.Laws.MapCov Σ S using (lamInv; outInv; unfoldInv)
open import Once.Metatheory.Laws.Strengthen Σ S using (varTy)

module _ {m : ℕ} {Δ : KCtx m} where

  -- What any derivation of `anaᶜ`, `outᶜ` has as its type; the functor is well formed.
  anaTy : ∀ {n} {Γ : Ctx m n} {Ψ Z π F A π′ c} → Δ ⊩ Γ ⊢[ Ψ ] anaᶜ F A π′ c ∷ Z ! π
        → Σ[ W ∈ Ty m ] (Z ≡ A ⇒[ mk-kind Many π′ ] W)
  anaTy d with lamInv d
  ... | W , _ , _ , eqT , _ = W , eqT

  anaWF : ∀ {n} {Γ : Ctx m n} {Ψ π F A π′ c f} → Δ ⊩ Γ ⊢[ Ψ ] anaᶜ F A π′ c ∷ A ⇒[ mk-kind Many π′ ] ν F f ! π → WFFun Δ F
  anaWF d with lamInv d
  ... | W , _ , _ , refl , dt = proj₁ (unfoldInv dt)

  outTy : ∀ {n} {Γ : Ctx m n} {Ψ Z π F} → Δ ⊩ Γ ⊢[ Ψ ] outᶜ {S = S} F ∷ Z ! π
        → Z ≡ ν F pureᶠ ⇒[ mk-kind Many pure ] ⟦ F ⟧F (ν F pureᶠ)
  outTy d with lamInv d
  ... | W , _ , _ , eqT , dt with outInv dt
  ...   | F′ , f , _ , _ , eqX , _ , dv with varTy dv
  ...     | refl with eqX
  ...       | refl = eqT

  private
    -- Reading a layer as a code layer and back.
    fromLtoL : ∀ (σ : TySub m 0) (H : Fun m) X (y : ⟦ (⟦ H ⟧F X) ⟨ σ ⟩ ⟧ᵛ) → fromL σ H X (toL σ H X y) ≡ y
    fromLtoL σ (K C)     X y        = refl
    fromLtoL σ Id        X y        = refl
    fromLtoL σ (H₁ ⊕ H₂) X (inj₁ y) = cong inj₁ (fromLtoL σ H₁ X y)
    fromLtoL σ (H₁ ⊕ H₂) X (inj₂ y) = cong inj₂ (fromLtoL σ H₂ X y)
    fromLtoL σ (H₁ ⊗ H₂) X (y , y′) = cong₂ _,_ (fromLtoL σ H₁ X y) (fromLtoL σ H₂ X y′)

    subPure : ∀ {X : Set} (p : pure ⊑π pure) (x : X) → sub p x ≡ x
    subPure ⊑-pure x = refl

  -- ν F is the final coalgebra: `out ∘ ana c` is `layer (ana c) ∘ c`.
  ana-βᶜ : ∀ {n} {Γ : Ctx m n} {Ψ F A π₀ c}
         → Pure Σ fmt S Δ Γ c (A ⇒[ mk-kind Many pure ] ⟦ F ⟧F A)
         → (d : Δ ⊩ Γ ⊢[ Ψ ] composeᶜ A pure (outᶜ F) (anaᶜ F A pure c)
                              ∷ A ⇒[ mk-kind Many pure ] ⟦ F ⟧F (ν F pureᶠ) ! π₀)
           (d′ : Δ ⊩ Γ ⊢[ Ψ ] composeᶜ A pure (layerᶜ F A (ν F pureᶠ) (anaᶜ F A pure c)) c
                               ∷ A ⇒[ mk-kind Many pure ] ⟦ F ⟧F (ν F pureᶠ) ! π₀)
         → _≅_ Σ fmt S d d′
  ana-βᶜ {Γ = Γ} {Ψ} {F} {A} {π₀} {c} (Ψp , dp) d d′ δ sd σ r γ sγ =
    sameM {TT ⟨ σ ⟩} {π₀} (rel (GO (compShape d) (AV.armsLL (inj₂ refl) d) (compShape d′) (AV.armsLL (inj₂ refl) d′)))
    where
      open Views δ sd σ r γ sγ
      open ProdV δ sd σ r γ sγ using (pureRet)
      module AV = ArmsV δ sd σ r γ sγ
      module G  = CompGV δ sd σ r
      module NV = AnaV δ sd σ r
      module MT = MapTopV δ sd σ r A (ν F pureᶠ)
      module LS = LayerSem σ
      module Fn = Functor σ r
      open Transport δ σ r
      N  = ν F pureᶠ
      FN = ⟦ F ⟧F N
      FA = ⟦ F ⟧F A
      CT = A ⇒[ mk-kind Many pure ] FA
      NT = A ⇒[ mk-kind Many pure ] N
      TT = A ⇒[ mk-kind Many pure ] FN
      GS = code (F ⟨ σ ⟩F)
      eTT : (FA ⇒[ mk-kind Many pure ] FN) ≡ (layerT F ⟨ at₀ A ⟩ ⇒[ mk-kind Many pure ] layerT F ⟨ at₀ N ⟩)
      eTT = cong₂ (λ P Q → P ⇒[ mk-kind Many pure ] Q) (sym (layerTy F A)) (sym (layerTy F N))

      GO : Shape A pure TT (outᶜ F) (anaᶜ F A pure c) → AV.Arms d (outᶜ F) (anaᶜ F A pure c)
         → Shape A pure TT (layerᶜ F A N (anaᶜ F A pure c)) c → AV.Arms d′ (layerᶜ F A N (anaᶜ F A pure c)) c
         → _~_ {TT} (⟪ d ⟫ γ) (⟪ d′ ⟫ γ)
      GO (shape eT tyF tyG lf lg zp) (AV.arms dO dn Po Pn) (shape eT′ tyF′ tyG′ lf′ lg′ zp′) (AV.arms {Ψe = Ψl} {πe = πl} dl dc Pl Pc)
        with eT | tyF dO | tyG dn | eT′ | tyF′ dl | tyG′ dc
      ... | refl | refl | refl | refl | refl | refl with outTy dO | anaTy dn | ty-unique dc dp | MT.mapTy (layerT F) dl
      ...   | refl | (_ , refl) | refl | (W , eqL) with kind≡ {Δ = Δ} eqL
      ...     | refl , refl = ~trans {TT} LHS (~trans {TT} (returnRel SAME) (~sym {TT} RHS))
        where
          ro = resR base Po
          rn = resR base Pn
          rl = resR base Pl
          rc = resR base Pc
          wf = anaWF dn
          pc = ⟦ transfer dp dc ⟧ δ σ r (restrict σ Pc γ)
          spc : Same (CT ⟨ σ ⟩) pc pc
          spc = returnRel⁻ (runs (fl (transfer dp dc) (transfer dp dc) rc rc))
          av = NV.anaᵛ F A pc
          ANA : _~_ {NT} (⟪ dn ⟫ _) (return∞ av)
          ANA = NV.anaSem γ sγ dn rn (NV.readsPure γ sγ A A dp dc rc)

          LHS : _~_ {TT} (⟪ d ⟫ γ) (return∞ (compᵛ pure (liftᵛ Many lf (NV.outᵛ F)) (liftᵛ Many lg av)))
          LHS = ~trans {TT} (G.compSemG γ sγ d base dO ro dn rn lf lg zp)
            (≈-Relatedʳ (≈-sym (≈-trans (idˡ (NV.outᵛ F) _) (idˡ av _)))
              (bindRel {g = λ o → return∞ av >>=∞ λ i → return∞ (compᵛ pure (liftᵛ Many lf o) (liftᵛ Many lg i))} (NV.outSem γ sγ dO ro)
                (λ {o} {o′} so → bindRel {g = λ i → return∞ (compᵛ pure (liftᵛ Many lf o′) (liftᵛ Many lg i))} ANA
                  (λ {i} {i′} si → returnRel (λ x x′ sx → toObserved (returnRel
                    (subst₂′ {X = FN} (subPure lf (o (sub lg (i x)))) (subPure lf (o′ (sub lg (i′ x′))))
                      (fromSameP σ {X = N} {Y = FN} so
                        (subst₂′ {X = N} (subPure lg (i x)) (subPure lg (i′ x′)) (fromSameP σ {X = A} {Y = N} si sx))))))))))

          el  = restrict σ Pl γ
          dlT = subst (λ Z → Δ ⊩ Γ ⊢[ Ψl ] layerᶜ F A N (anaᶜ F A pure c) ∷ Z ! πl) eTT dl
          cv  = MT.covD (layerT F) dlT
          Φ   = MT.Φcall (layerT F) {X = A} {Y = N} {q = Many} (λ _ → refl) (λ _ → refl)
          CL : V NT → V (layerT F ⟨ at₀ A ⟩ ⇒[ mk-kind Many pure ] layerT F ⟨ at₀ N ⟩)
          CL gv x = MapAt.mapS Δ σ A N (layerT F) cv (Φ gv) x
          lv = subst V (sym eTT) (CL av)

          LAYERED : _~_ {FA ⇒[ mk-kind Many pure ] FN} (⟪ dl ⟫ _) (return∞ lv)
          LAYERED = ~trans {FA ⇒[ mk-kind Many pure ] FN}
            (relBack {π = πl} eTT {mv = ⟦ dl ⟧ δ σ r el}
               (subst (λ m₀ → Related (Same ((layerT F ⟨ at₀ A ⟩ ⇒[ mk-kind Many pure ] layerT F ⟨ at₀ N ⟩) ⟨ σ ⟩)) (toT∞ πl m₀)
                                (⟪ dn ⟫ (restrict σ Pn γ) >>=∞ λ gv → return∞ (CL gv)))
                  (meaningSubst eTT dl el)
               (MT.mapSem γ sγ (layerT F) dlT rl dn rn Φ (MT.HΦcall (layerT F) {X = A} {Y = N} {q = Many} (λ _ → refl) (λ _ → refl)))))
            (≈-Relatedʳ (≈-sym (≈-trans (≈-bind (idˡ av _) (λ _ → ≈-refl _)) (idˡ (CL av) _)))
              (bindRel {g = λ v → return∞ (subst V (sym eTT) v)}
                (bindRel {g = λ gv → return∞ (CL gv)} ANA (λ {gv} {gv′} sg → returnRel
                  (toSameP σ {X = layerT F ⟨ at₀ A ⟩} {Y = layerT F ⟨ at₀ N ⟩}
                    (λ sx → MapResp.resp σ r A N (layerT F) cv cv
                              (MT.ΦcallResp (layerT F) {X = A} {Y = N} {q = Many} (λ _ → refl) (λ _ → refl) sg) sx))))
                (λ sv → returnRel (sameSubst (sym eTT) sv))))

          RHS : _~_ {TT} (⟪ d′ ⟫ γ) (return∞ (compᵛ pure (liftᵛ Many lf′ lv) (liftᵛ Many lg′ pc)))
          RHS = ~trans {TT} (G.compSemG γ sγ d′ base dl rl dc rc lf′ lg′ zp′)
            (≈-Relatedʳ (≈-sym (≈-trans (idˡ lv _) (idˡ pc _)))
              (bindRel {g = λ l → return∞ pc >>=∞ λ a → return∞ (compᵛ pure (liftᵛ Many lf′ l) (liftᵛ Many lg′ a))} LAYERED
                (λ {l} {l′} sl → bindRel {g = λ a → return∞ (compᵛ pure (liftᵛ Many lf′ l′) (liftᵛ Many lg′ a))} (pureRet dc dp rc)
                  (λ sa → returnRel (compCong pure {Many} {Many} lf′ lf′ lg′ lg′ sl sa)))))

          SAME : Same (TT ⟨ σ ⟩) (compᵛ pure (liftᵛ Many lf (NV.outᵛ F)) (liftᵛ Many lg av)) (compᵛ pure (liftᵛ Many lf′ lv) (liftᵛ Many lg′ pc))
          SAME x x′ sx = toObserved (returnRel (subst₂′ {X = FN} e₁ e₂ CORE))
            where
              c′ = λ y → toL σ F A (pc y)
              y′ = pc x′
              e₁ : sub lf (NV.outᵛ F (sub lg (av x))) ≡ fromL σ F N (mapP GS GS c′ (c′ x))
              e₁ = trans (cong (λ y → sub lf (NV.outᵛ F y)) (subPure lg (av x))) (subPure lf (NV.outᵛ F (av x)))
              tm = subst V (sym (layerTy F A)) y′
              e₂ : sub lf′ (lv (sub lg′ (pc x′))) ≡ LS.tr F N (CL av tm)
              e₂ = trans (cong (λ y → sub lf′ (lv y)) (subPure lg′ (pc x′)))
                     (trans (subPure lf′ (lv y′))
                       (trans (funBack (sym (layerTy F A)) (sym (layerTy F N)) (CL av) y′)
                              (symsym (layerTy F N) (CL av tm))))
              sy : Same (FA ⟨ σ ⟩) y′ y′
              sy = sameRefl (FA ⟨ σ ⟩) (Same-sym (FA ⟨ σ ⟩) (fromSameP σ {X = A} {Y = FA} spc sx))
              AGREE : Same (FN ⟨ σ ⟩) (LS.tr F N (CL av tm)) (LS.LAYER F av (LS.tr F A tm))
              AGREE = LS.agree {Δ = Δ} r A N F wf cv (Φ av) av
                        (λ o a a′ sa → fromSameP σ {X = A} {Y = N} (NV.anaResp wf spc) sa)
                        (sameSubst (sym (layerTy F A)) sy)
              e₃ : LS.LAYER F av (LS.tr F A tm) ≡ fromL σ F N (sfmap GS av (c′ x′))
              e₃ = trans (cong (LS.LAYER F av) (substSym (layerTy F A) y′))
                     (trans (cong (LS.LAYER F av) (sym (fromLtoL σ F A y′))) (LS.layerFromL F av (c′ x′)))
              CORE : Same (FN ⟨ σ ⟩) (fromL σ F N (mapP GS GS c′ (c′ x))) (LS.tr F N (CL av tm))
              CORE = Same-trans (FN ⟨ σ ⟩)
                       (Fn.fromL-same wf N (NV.mapPRel wf spc GS (Fn.toL-same wf A (fromSameP σ {X = A} {Y = FA} spc sx))))
                       (Same-sym (FN ⟨ σ ⟩) (subst₂′ {X = FN} refl (sym e₃) AGREE))

  -- … and the only one: a coalgebra map to `out` is the unfold, layer by layer.
  ana-uniqueᶜ : ∀ {n} {Γ : Ctx m n} {Ψ F A π₀ π′ c h}
              → Pure Σ fmt S Δ Γ c (A ⇒[ mk-kind Many pure ] ⟦ F ⟧F A) → Pure Σ fmt S Δ Γ h (A ⇒[ mk-kind Many pure ] ν F pureᶠ)
              → (e : Δ ⊩ Γ ⊢[ Ψ ] composeᶜ A pure (outᶜ F) h ∷ A ⇒[ mk-kind Many pure ] ⟦ F ⟧F (ν F pureᶠ) ! π′)
                (e′ : Δ ⊩ Γ ⊢[ Ψ ] composeᶜ A pure (layerᶜ F A (ν F pureᶠ) h) c
                                    ∷ A ⇒[ mk-kind Many pure ] ⟦ F ⟧F (ν F pureᶠ) ! π′)
              → _≅_ Σ fmt S e e′
              → (d : Δ ⊩ Γ ⊢[ Ψ ] h ∷ A ⇒[ mk-kind Many pure ] ν F pureᶠ ! π₀)
                (d′ : Δ ⊩ Γ ⊢[ Ψ ] anaᶜ F A pure c ∷ A ⇒[ mk-kind Many pure ] ν F pureᶠ ! π₀)
              → _≅_ Σ fmt S d d′
  ana-uniqueᶜ {Γ = Γ} {Ψ} {F} {A} {π₀} {π′} {c} {h} (Ψp , dp) (Ψh , dph) e e′ he d d′ δ sd σ r γ sγ =
    sameM {NT ⟨ σ ⟩} {π₀} (rel (GO (compShape e) (AV.armsLL (inj₂ refl) e) (compShape e′) (AV.armsLL (inj₂ refl) e′)))
    where
      open Views δ sd σ r γ sγ
      open ProdV δ sd σ r γ sγ using (pureRet)
      module AV = ArmsV δ sd σ r γ sγ
      module G  = CompGV δ sd σ r
      module NV = AnaV δ sd σ r
      module MT = MapTopV δ sd σ r A (ν F pureᶠ)
      module LS = LayerSem σ
      module Fn = Functor σ r
      open Transport δ σ r
      N  = ν F pureᶠ
      FN = ⟦ F ⟧F N
      FA = ⟦ F ⟧F A
      CT = A ⇒[ mk-kind Many pure ] FA
      NT = A ⇒[ mk-kind Many pure ] N
      TT = A ⇒[ mk-kind Many pure ] FN
      GS = code (F ⟨ σ ⟩F)
      eTT : (FA ⇒[ mk-kind Many pure ] FN) ≡ (layerT F ⟨ at₀ A ⟩ ⇒[ mk-kind Many pure ] layerT F ⟨ at₀ N ⟩)
      eTT = cong₂ (λ P Q → P ⇒[ mk-kind Many pure ] Q) (sym (layerTy F A)) (sym (layerTy F N))
      wf = anaWF d′

      -- `h`, the value.
      hv = ⟦ transfer dph d ⟧ δ σ r γ
      shv : Same (NT ⟨ σ ⟩) hv hv
      shv = returnRel⁻ (runs (fl (transfer dph d) (transfer dph d) base base))
      HV : _~_ {NT} (⟪ d ⟫ γ) (return∞ hv)
      HV = pureRet d dph base

      -- Forcing the same streams: the same layers.
      outResp : ∀ {v v′} → Same (N ⟨ σ ⟩) v v′ → Same (FN ⟨ σ ⟩) (NV.outᵛ F v) (NV.outᵛ F v′)
      outResp s = Fn.fromL-same wf N (LayerEq-mono GS (Fn.sameν→ wf) (LayerEq-∀ GS (λ n → returnRel⁻ (fromObserved (Fn.sameν← wf s (suc n))))))

      GO : Shape A pure TT (outᶜ F) h → AV.Arms e (outᶜ F) h
         → Shape A pure TT (layerᶜ F A N h) c → AV.Arms e′ (layerᶜ F A N h) c
         → _~_ {NT} (⟪ d ⟫ γ) (⟪ d′ ⟫ γ)
      GO (shape eT tyF tyG lf lg zp) (AV.arms dO dh Po Ph) (shape eT′ tyF′ tyG′ lf′ lg′ zp′) (AV.arms {Ψe = Ψl} {πe = πl} dl dc Pl Pc)
        with eT | tyF dO | tyG dh | eT′ | tyF′ dl | tyG′ dc
      ... | refl | refl | refl | refl | refl | refl with outTy dO | ty-unique dh d | ty-unique dc dp | MT.mapTy (layerT F) dl
      ...   | refl | refl | refl | (W , eqL) with kind≡ {Δ = Δ} eqL
      ...     | refl , refl = ~trans {NT} HV (~trans {NT} (returnRel UNIQUE) (~sym {NT} ANA))
        where
          ro = resR base Po
          rh = resR base Ph
          rl = resR base Pl
          rc = resR base Pc
          pc = ⟦ transfer dp dc ⟧ δ σ r (restrict σ Pc γ)
          spc : Same (CT ⟨ σ ⟩) pc pc
          spc = returnRel⁻ (runs (fl (transfer dp dc) (transfer dp dc) rc rc))
          av = NV.anaᵛ F A pc
          ANA : _~_ {NT} (⟪ d′ ⟫ γ) (return∞ av)
          ANA = NV.anaSem γ sγ d′ base (NV.readsPure γ sγ A A dp dc rc)

          -- The `h` that `e` runs: the same as `d`'s.
          hvE = ⟦ transfer dph dh ⟧ δ σ r (restrict σ Ph γ)
          sEh : Same (NT ⟨ σ ⟩) hvE hv
          sEh = returnRel⁻ (runs (fl (transfer dph dh) (transfer dph d) rh base))

          LHS : _~_ {TT} (⟪ e ⟫ γ) (return∞ (compᵛ pure (liftᵛ Many lf (NV.outᵛ F)) (liftᵛ Many lg hvE)))
          LHS = ~trans {TT} (G.compSemG γ sγ e base dO ro dh rh lf lg zp)
            (≈-Relatedʳ (≈-sym (≈-trans (idˡ (NV.outᵛ F) _) (idˡ hvE _)))
              (bindRel {g = λ o → return∞ hvE >>=∞ λ i → return∞ (compᵛ pure (liftᵛ Many lf o) (liftᵛ Many lg i))} (NV.outSem γ sγ dO ro)
                (λ {o} {o′} so → bindRel {g = λ i → return∞ (compᵛ pure (liftᵛ Many lf o′) (liftᵛ Many lg i))} (pureRet dh dph rh)
                  (λ {i} {i′} si → returnRel (λ x x′ sx → toObserved (returnRel
                    (subst₂′ {X = FN} (subPure lf (o (sub lg (i x)))) (subPure lf (o′ (sub lg (i′ x′))))
                      (fromSameP σ {X = N} {Y = FN} so
                        (subst₂′ {X = N} (subPure lg (i x)) (subPure lg (i′ x′)) (fromSameP σ {X = A} {Y = N} si sx))))))))))

          el  = restrict σ Pl γ
          dlT = subst (λ Z → Δ ⊩ Γ ⊢[ Ψl ] layerᶜ F A N h ∷ Z ! πl) eTT dl
          cv  = MT.covD (layerT F) dlT
          Φ   = MT.Φcall (layerT F) {X = A} {Y = N} {q = Many} (λ _ → refl) (λ _ → refl)
          CL : V NT → V (layerT F ⟨ at₀ A ⟩ ⇒[ mk-kind Many pure ] layerT F ⟨ at₀ N ⟩)
          CL gv x = MapAt.mapS Δ σ A N (layerT F) cv (Φ gv) x
          lv = subst V (sym eTT) (CL hv)

          LAYERED : _~_ {FA ⇒[ mk-kind Many pure ] FN} (⟪ dl ⟫ _) (return∞ lv)
          LAYERED = ~trans {FA ⇒[ mk-kind Many pure ] FN}
            (relBack {π = πl} eTT {mv = ⟦ dl ⟧ δ σ r el}
               (subst (λ m₀ → Related (Same ((layerT F ⟨ at₀ A ⟩ ⇒[ mk-kind Many pure ] layerT F ⟨ at₀ N ⟩) ⟨ σ ⟩)) (toT∞ πl m₀)
                                (⟪ d ⟫ γ >>=∞ λ gv → return∞ (CL gv)))
                  (meaningSubst eTT dl el)
               (MT.mapSem γ sγ (layerT F) dlT rl d base Φ (MT.HΦcall (layerT F) {X = A} {Y = N} {q = Many} (λ _ → refl) (λ _ → refl)))))
            (≈-Relatedʳ (≈-sym (≈-trans (≈-bind (idˡ hv _) (λ _ → ≈-refl _)) (idˡ (CL hv) _)))
              (bindRel {g = λ v → return∞ (subst V (sym eTT) v)}
                (bindRel {g = λ gv → return∞ (CL gv)} HV (λ {gv} {gv′} sg → returnRel
                  (toSameP σ {X = layerT F ⟨ at₀ A ⟩} {Y = layerT F ⟨ at₀ N ⟩}
                    (λ sx → MapResp.resp σ r A N (layerT F) cv cv
                              (MT.ΦcallResp (layerT F) {X = A} {Y = N} {q = Many} (λ _ → refl) (λ _ → refl) sg) sx))))
                (λ sv → returnRel (sameSubst (sym eTT) sv))))

          RHS : _~_ {TT} (⟪ e′ ⟫ γ) (return∞ (compᵛ pure (liftᵛ Many lf′ lv) (liftᵛ Many lg′ pc)))
          RHS = ~trans {TT} (G.compSemG γ sγ e′ base dl rl dc rc lf′ lg′ zp′)
            (≈-Relatedʳ (≈-sym (≈-trans (idˡ lv _) (idˡ pc _)))
              (bindRel {g = λ l → return∞ pc >>=∞ λ a → return∞ (compᵛ pure (liftᵛ Many lf′ l) (liftᵛ Many lg′ a))} LAYERED
                (λ {l} {l′} sl → bindRel {g = λ a → return∞ (compᵛ pure (liftᵛ Many lf′ l′) (liftᵛ Many lg′ a))} (pureRet dc dp rc)
                  (λ sa → returnRel (compCong pure {Many} {Many} lf′ lf′ lg′ lg′ sl sa)))))

          -- The hypothesis, at this environment: the two composites are the same.
          SAMEe : Same (TT ⟨ σ ⟩) (compᵛ pure (liftᵛ Many lf (NV.outᵛ F)) (liftᵛ Many lg hvE)) (compᵛ pure (liftᵛ Many lf′ lv) (liftᵛ Many lg′ pc))
          SAMEe = returnRel⁻ (~trans {TT} (~sym {TT} LHS) (~trans {TT} (fromObserved (he δ sd σ r γ sγ)) RHS))

          c′ = λ y → toL σ F A (pc y)

          -- So forcing `h` gives `h` mapped over the coalgebra's layer.
          HYPx : ∀ {x x′} → Same (A ⟨ σ ⟩) x x′ → LayerEq GS (Same (N ⟨ σ ⟩)) (νM.outν (hv x)) (sfmap GS hv (c′ x′))
          HYPx {x} {x′} sx = subst₂ (LayerEq GS (Same (N ⟨ σ ⟩))) (LS.toLfromL F N (νM.outν (hv x))) (LS.toLfromL F N (sfmap GS hv (c′ x′)))
                               (Fn.toL-same wf N CHAIN)
            where
              y′ = pc x′
              sxx : Same (A ⟨ σ ⟩) x x
              sxx = sameRefl (A ⟨ σ ⟩) sx
              S1 : Same (FN ⟨ σ ⟩) (NV.outᵛ F (hv x)) (sub lf (NV.outᵛ F (sub lg (hvE x))))
              S1 = subst₂′ {X = FN} refl (trans (cong (λ y → sub lf (NV.outᵛ F y)) (subPure lg (hvE x))) (subPure lf (NV.outᵛ F (hvE x))))
                     (outResp (fromSameP σ {X = A} {Y = N} (Same-sym (NT ⟨ σ ⟩) sEh) sxx))
              tm = subst V (sym (layerTy F A)) y′
              e₂ : sub lf′ (lv (sub lg′ (pc x′))) ≡ LS.tr F N (CL hv tm)
              e₂ = trans (cong (λ y → sub lf′ (lv y)) (subPure lg′ (pc x′)))
                     (trans (subPure lf′ (lv y′))
                       (trans (funBack (sym (layerTy F A)) (sym (layerTy F N)) (CL hv) y′)
                              (symsym (layerTy F N) (CL hv tm))))
              sy : Same (FA ⟨ σ ⟩) y′ y′
              sy = sameRefl (FA ⟨ σ ⟩) (Same-sym (FA ⟨ σ ⟩) (fromSameP σ {X = A} {Y = FA} spc sx))
              AGREE : Same (FN ⟨ σ ⟩) (LS.tr F N (CL hv tm)) (LS.LAYER F hv (LS.tr F A tm))
              AGREE = LS.agree {Δ = Δ} r A N F wf cv (Φ hv) hv
                        (λ o a a′ sa → fromSameP σ {X = A} {Y = N} shv sa)
                        (sameSubst (sym (layerTy F A)) sy)
              e₃ : LS.LAYER F hv (LS.tr F A tm) ≡ fromL σ F N (sfmap GS hv (c′ x′))
              e₃ = trans (cong (LS.LAYER F hv) (substSym (layerTy F A) y′))
                     (trans (cong (LS.LAYER F hv) (sym (fromLtoL σ F A y′))) (LS.layerFromL F hv (c′ x′)))
              CHAIN : Same (FN ⟨ σ ⟩) (fromL σ F N (νM.outν (hv x))) (fromL σ F N (sfmap GS hv (c′ x′)))
              CHAIN = Same-trans (FN ⟨ σ ⟩) S1
                        (Same-trans (FN ⟨ σ ⟩) (subst₂′ {X = FN} refl (sym e₂) (fromSameP σ {X = A} {Y = FN} SAMEe sx))
                          (subst₂′ {X = FN} refl (sym e₃) AGREE))

          -- To every depth, `h` agrees with the unfold.
          NU   : ∀ n {x x′} → Same (A ⟨ σ ⟩) x x′ → SameNu pureᶠ GS n (hv x) (anaP GS c′ x′)
          STEP : ∀ n H {u l l′} → LayerEq H (Same (N ⟨ σ ⟩)) u (sfmap H hv l) → LayerEq H (Same (A ⟨ σ ⟩)) l l′
               → LayerEq H (SameNu pureᶠ GS n) u (mapP GS H c′ l′)
          NU zero    s = _
          NU (suc n) {x} {x′} s = toObserved (returnRel (STEP n GS (HYPx s)
                                    (Fn.toL-same wf A (fromSameP σ {X = A} {Y = FA} spc (sameRefl (A ⟨ σ ⟩) (Same-sym (A ⟨ σ ⟩) s))))))
          STEP n (SK B) p q = trans p q
          STEP n SId p q = SameNu-trans pureᶠ GS n (Fn.sameν← wf p n) (NU n q)
          STEP n (H₁ S⊕ H₂) {inj₁ u} {inj₁ l} {inj₁ l′} p q = STEP n H₁ p q
          STEP n (H₁ S⊕ H₂) {inj₂ u} {inj₂ l} {inj₂ l′} p q = STEP n H₂ p q
          STEP n (H₁ S⊕ H₂) {inj₁ u} {inj₁ l} {inj₂ l′} p ()
          STEP n (H₁ S⊕ H₂) {inj₂ u} {inj₂ l} {inj₁ l′} p ()
          STEP n (H₁ S⊕ H₂) {inj₁ u} {inj₂ l} () q
          STEP n (H₁ S⊕ H₂) {inj₂ u} {inj₁ l} () q
          STEP n (H₁ S⊗ H₂) {u₁ , u₂} {l₁ , l₂} {l₁′ , l₂′} (p₁ , p₂) (q₁ , q₂) = STEP n H₁ p₁ q₁ , STEP n H₂ p₂ q₂

          UNIQUE : Same (NT ⟨ σ ⟩) hv av
          UNIQUE = toSameP σ {X = A} {Y = N} (λ s → Fn.sameν→ wf (λ n → NU n s))
