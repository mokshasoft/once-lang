{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws.MapV.Fix — the cases of the map at μ and ν: a fold and an unfold
-- of the layer map. Each takes the layer map as a parameter (`Laws.MapV.Map` ties the knot).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature; OneName)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Laws.MapV.Fix (Σ : Signature) (u : OneName Σ) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

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

module MapVFix {m : ℕ} {Δ : KCtx m} (δ : DefSem) (sd : SameDefs Σ fmt S δ) (σ : TySub m 0) (r : Respects Δ ∅ₖ σ)
            (A B : Ty m) where
  open MapAt Δ σ A B
  open MapV δ sd σ r A B
  open Reads

  private
    cod≡ : ∀ {X Y Z Z′ : Ty m} {k k′} → (Y ⇒[ k ] Z) ≡ (X ⇒[ k′ ] Z′) → Z ≡ Z′
    cod≡ refl = refl

  private
    pur≡ : ∀ {X Y X′ Y′ : Ty m} {q q′ π π′} → (X ⇒[ mk-kind q π ] Y) ≡ (X′ ⇒[ mk-kind q′ π′ ] Y′) → π ≡ π′
    pur≡ refl = refl

    eqLayer : ∀ G {X : Set} {R : X → X → Set} → (∀ x → R x x) → ∀ l → LayerEq G R l l
    eqLayer (SK C)   rf l = refl
    eqLayer SId      rf l = rf l
    eqLayer (G S⊕ H) rf (inj₁ l) = eqLayer G rf l
    eqLayer (G S⊕ H) rf (inj₂ l) = eqLayer H rf l
    eqLayer (G S⊗ H) rf (l₁ , l₂) = eqLayer G rf l₁ , eqLayer H rf l₂

  bodyMu : ∀ {G} → LayerAt (μ (G ⟨ at₀ B ⟩F)) G → BodyAt (μ G)
  bodyMu {G} recL {Γ = Γ} γ sγ c {φ} {xv = xv} Rh Rx sx Hc db {γa} ra with FoldR.viewFold γ sγ db ra
  ... | FoldR.foldView wf da dt {ea} {et} rA rT eq with FunV.viewLam δ sd σ r γ sγ da rA
  ...   | FunV.lamView {q′ = q′} {Ψ₀} le dl {e₀} r₀ eqT eqL with cod≡ eqT | pur≡ eqT
  ...     | refl | refl with eqT
  ...       | refl =
    W.~trans {R} eq (W.~trans {R}
      (≈-Relatedʳ (≈-sym (≈-trans (idˡ alg₀ (λ g → return∞ xv >>=∞ λ v → return∞ (foldM pure (CA G) (λ l → g (fromL σ GA R l)) v)))
                                  (idˡ xv (λ v → return∞ (foldM pure (CA G) (λ l → alg₀ (fromL σ GA R l)) v)))))
        (bindRel {g = λ g → return∞ xv >>=∞ λ v → return∞ (foldM pure (CA G) (λ l → g (fromL σ GA R l)) v)} eqL (λ {g} {g′} sg →
          bindRel {g = λ v → return∞ (foldM pure (CA G) (λ l → g′ (fromL σ GA R l)) v)} (rd Rx dt rT) (λ {v} {v′} sv →
            returnRel (FOLDREL sg (Fn.sameμ wf sv))))))
      (returnRel (Fn.≡→sameμ wfGB (foldEq xv))))
    where
      module W = Views δ sd σ r γ sγ
      GA = G ⟨ at₀ A ⟩F
      GB = G ⟨ at₀ B ⟩F
      R  = μ GB
      L  = ⟦ GA ⟧F R
      φμ : FnF G
      φμ o = φ (p-μ o)
      alg₀ = ⟦ ⊢lam le dl ⟧ δ σ r e₀
      module Fn = Functor σ r
      wfGB = CovWF.wfB {Δ = Δ} σ A B G c

      -- The folds of the same algebras: the same trees.
      FOLDREL : ∀ {g g′} → Same ((L ⇒[ mk-kind Many pure ] R) ⟨ σ ⟩) g g′ → ∀ {v v′ : μS (CA G)} → v ≡ v′
              → Same (R ⟨ σ ⟩) (foldM pure (CA G) (λ l → g (fromL σ GA R l)) v) (foldM pure (CA G) (λ l → g′ (fromL σ GA R l)) v′)
      FOLDREL {g} {g′} sg {v} refl =
        returnRel⁻ (runs (Fold.foldRel pure (CA G) (R ⟨ σ ⟩) (λ l → g (fromL σ GA R l)) (λ l → g′ (fromL σ GA R l))
                            (λ p → rel (fromObserved (sg _ _ (Fn.fromL-same wf R p)))) v))

      -- The algebra, at a layer: the layer mapped, rolled.
      ALG : ∀ w w′ → Same (L ⟨ σ ⟩) w w′ → alg₀ w ≡ inS (toL σ GB R (layerS R G c φμ w′))
      ALG w w′ sw with FoldR.viewRoll (e₀ , slot q′ w) sγ₁ dl (Views.base δ sd σ r (e₀ , slot q′ w) sγ₁)
        where sγ₁ = sameEnv▸ σ {Γ = Γ} {Ψ = Ψ₀} {A = L} q′ (W.sameEnvOf r₀) (slotAgree σ {L} q′ q′ (sameRefl (L ⟨ σ ⟩) sw))
      ... | FoldR.rollView wfB dm r₁ eqR =
        trans (FunV.lamCall δ sd σ r γ sγ le dl e₀ w)
          (Fn.sameμ wfB (returnRel⁻ (Views.~trans δ sd σ r {Γ = Γ ▸ L} {Ψ = q′ ∷ Ψ₀} (e₀ , slot q′ w) sγ₁ {R} eqR
            (≈-Relatedʳ (≈-sym (idˡ (layerS R G c φμ w′) (λ l → return∞ (inS (toL σ GB R l)))))
              (bindRel {f = λ l → return∞ (inS (toL σ GB R l))} {g = λ l → return∞ (inS (toL σ GB R l))}
                (recL (e₀ , slot q′ w) sγ₁ c (readsWk γ sγ r₀ (slot q′ w) sγ₁ Rh)
                   (readsVar (e₀ , slot q′ w) sγ₁ (valAt0 σ {Γ = Γ} {A = L} q′ {γ = e₀} sw)) (sameSelf L sw)
                   (λ o → Hc (p-μ o)) dm r₁)
                (λ s → returnRel (Fn.roll-same wfB s)))))))
        where sγ₁ = sameEnv▸ σ {Γ = Γ} {Ψ = Ψ₀} {A = L} q′ (W.sameEnvOf r₀) (slotAgree σ {L} q′ q′ (sameRefl (L ⟨ σ ⟩) sw))

      alg′ : ⟦ CA G ⟧SF ⟦ R ⟨ σ ⟩ ⟧ᵛ → ⟦ R ⟨ σ ⟩ ⟧ᵛ
      alg′ l = alg₀ (fromL σ GA R l)

      -- The fold of that algebra is the map.
      foldEq : ∀ v → foldM pure (CA G) alg′ v ≡ muMap G c φμ v
      layerEq : ∀ H (cH : CovF H) (φH : FnF H) (l : ⟦ CA H ⟧SF (μS (CA G)))
              → toL σ (H ⟨ at₀ B ⟩F) R (layerS R H cH φH (fromL σ (H ⟨ at₀ A ⟩F) R (layerM pure (CA G) (CA H) alg′ l)))
                ≡ muLayer G H c φμ cH φH l
      foldEq (inS l) =
        trans (ALG _ _ (Fn.fromL-same wf R (eqLayer (CA G) (λ x → Fn.reflμ wfGB x) (layerM pure (CA G) (CA G) alg′ l))))
              (cong inS (layerEq G c φμ l))
      layerEq (K C)     cH φH l = refl
      layerEq Id        cH φH l = foldEq l
      layerEq (H₁ ⊕ H₂) (c₁ , c₂) φH (inj₁ l) = cong inj₁ (layerEq H₁ c₁ (λ o → φH (p-⊕ˡ o)) l)
      layerEq (H₁ ⊕ H₂) (c₁ , c₂) φH (inj₂ l) = cong inj₂ (layerEq H₂ c₂ (λ o → φH (p-⊕ʳ o)) l)
      layerEq (H₁ ⊗ H₂) (c₁ , c₂) φH (l₁ , l₂) =
        cong₂ _,_ (layerEq H₁ c₁ (λ o → φH (p-⊗ˡ o)) l₁) (layerEq H₂ c₂ (λ o → φH (p-⊗ʳ o)) l₂)

  bodyNu : ∀ {G f} → LayerAt (ν (G ⟨ at₀ A ⟩F) f) G → BodyAt (ν G f)
  bodyNu {G} {f} recL {Γ = Γ} γ sγ c {φ} {xv = xv} Rh Rx sx Hc db {γa} ra with FoldR.viewUnfold γ sγ db ra
  ... | FoldR.unfoldView wfB dc dt {ec} {et} rC rT eq with ty Rx dt
  ...   | refl with FunV.viewLam δ sd σ r γ sγ dc rC
  ...     | FunV.lamView {q′ = q′} {Ψ₀} le dl {e₀} r₀ eqT eqL with cod≡ eqT
  ...       | refl with eqT
  ...         | refl =
    W.~trans {RB} eq (W.~trans {RB}
      (≈-Relatedʳ (≈-sym (≈-trans (idˡ co₀ (λ g → return∞ xv >>=∞ λ v → return∞ (anaT g v))) (idˡ xv (λ v → return∞ (anaT co₀ v)))))
        (bindRel {g = λ g → return∞ xv >>=∞ λ v → return∞ (anaT g v)} eqL (λ {g} {g′} sg →
          bindRel {g = λ v → return∞ (anaT g′ v)} (rd Rx dt rT) (λ {v} {v′} sv →
            returnRel (Fn.sameν→ wfB λ n → Ana.anaRel f (CB G) (R ⟨ σ ⟩) (λ y → fmap (fin f) (toL σ GB R) (g y)) (λ y → fmap (fin f) (toL σ GB R) (g′ y))
              (λ {a} {a′} sa → ≈-Relatedˡ (toT∞-fmap (fin f) _ (g a)) (≈-Relatedʳ (toT∞-fmap (fin f) _ (g′ a′))
                 (relatedFmap (fromObserved (sg _ _ sa)) (Fn.toL-same wfB R)))) n sv)))))
      (returnRel (Fn.sameν→ wfB λ n → Ana.anaRel f (CB G) (R ⟨ σ ⟩) (λ y → fmap (fin f) (toL σ GB R) (co₀ y))
                         (λ y → fmap (fin f) (nuLayer G c φν {νM f (CA G)}) (outν y)) STEP n sx)))
    where
      module W = Views δ sd σ r γ sγ
      GA = G ⟨ at₀ A ⟩F
      GB = G ⟨ at₀ B ⟩F
      R  = ν GA f
      RB = ν GB f
      L  = ⟦ GB ⟧F R
      φν : FnF G
      φν o = φ (p-ν o)
      co₀ = ⟦ ⊢lam le dl ⟧ δ σ r e₀
      module Fn = Functor σ r
      anaT : (⟦ R ⟨ σ ⟩ ⟧ᵛ → _) → ⟦ R ⟨ σ ⟩ ⟧ᵛ → νM f (CB G)
      anaT g v = ana f (CB G) (λ y → fmap (fin f) (toL σ GB R) (g y)) v

      nuEq : ∀ H (cH : CovF H) (φH : FnF H) (l : ⟦ CA H ⟧SF (νM f (CA G)))
           → toL σ (H ⟨ at₀ B ⟩F) R (layerS R H cH φH (fromL σ (H ⟨ at₀ A ⟩F) R l)) ≡ nuLayer H cH φH l
      nuEq (K C)     cH φH l = refl
      nuEq Id        cH φH l = refl
      nuEq (H₁ ⊕ H₂) (c₁ , c₂) φH (inj₁ l) = cong inj₁ (nuEq H₁ c₁ (λ o → φH (p-⊕ˡ o)) l)
      nuEq (H₁ ⊕ H₂) (c₁ , c₂) φH (inj₂ l) = cong inj₂ (nuEq H₂ c₂ (λ o → φH (p-⊕ʳ o)) l)
      nuEq (H₁ ⊗ H₂) (c₁ , c₂) φH (l₁ , l₂) = cong₂ _,_ (nuEq H₁ c₁ (λ o → φH (p-⊗ˡ o)) l₁) (nuEq H₂ c₂ (λ o → φH (p-⊗ʳ o)) l₂)

      -- The coalgebra, at a seed: the seed forced, its layer mapped.
      COALG : ∀ y y′ → Same (R ⟨ σ ⟩) y y′
            → Related (Same (L ⟨ σ ⟩)) (toT∞ (fin f) (co₀ y)) (toT∞ (fin f) (outν y′) >>=∞ λ l → return∞ (layerS R G c φν (fromL σ GA R l)))
      COALG y y′ sy = subst (λ m′ → Related (Same (L ⟨ σ ⟩)) (toT∞ (fin f) m′) _) (sym (FunV.lamCall δ sd σ r γ sγ le dl e₀ y)) INNER
        where
          sγ₁ = sameEnv▸ σ {Γ = Γ} {Ψ = Ψ₀} {A = R} q′ (W.sameEnvOf r₀) (slotAgree σ {R} q′ q′ (sameRefl (R ⟨ σ ⟩) sy))
          γ₁ = e₀ , slot q′ y
          module W1 = Views δ sd σ r {Γ = Γ ▸ R} {Ψ = q′ ∷ Ψ₀} γ₁ sγ₁
          Ry₀ = readsVar γ₁ sγ₁ (valAt0 σ {Γ = Γ} {A = R} q′ {γ = e₀} sy)
          INNER : Related (Same (L ⟨ σ ⟩)) (W1.⟪ dl ⟫ γ₁) (toT∞ (fin f) (outν y′) >>=∞ λ l → return∞ (layerS R G c φν (fromL σ GA R l)))
          INNER with W1.viewLet dl W1.base
          ... | W1.letView {Ψ₂ = Ψ₂} de db₂ {eb} rb (ee , re , eq₂) with FoldR.viewOut γ₁ sγ₁ de re
          ...   | FoldR.outView wfA dv r₀′ eqX eqO with eqX
          ...     | refl with ty Ry₀ dv
          ...       | refl =
            W1.~trans {L} eq₂
              (≈-Relatedʳ (≈-sym (≈-trans (assoc _ _ _) (≈-bind (≈-refl _) (λ l → idˡ _ _))))
                (bindRel {g = λ w′ → return∞ (layerS R G c φν w′)}
                  (W1.~trans {⟦ GA ⟧F R} eqO (≈-Relatedʳ (≈-sym (idˡ y′ _))
                    (bindRel (rd Ry₀ dv r₀′) (λ sv →
                      relatedFmap (outRel f (CA G) (Fn.sameν← wfA sv)) (λ p → Fn.fromL-same wfA R (LayerEq-mono (CA G) (Fn.sameν→ wfA) (LayerEq-∀ (CA G) p)))))))
                  (λ {w} {w′} sw →
                    recL (eb , w) (sγ₂ sw) c (readsWk γ₁ sγ₁ rb w (sγ₂ sw) (readsWk γ sγ r₀ (slot q′ y) sγ₁ Rh))
                      (readsVar (eb , w) (sγ₂ sw) (valAt0 σ {Γ = Γ ▸ R} {A = ⟦ GA ⟧F R} One {γ = eb} sw))
                      (sameSelf (⟦ GA ⟧F R) sw) (λ o → Hc (p-ν o)) db₂ (Views.base δ sd σ r (eb , w) (sγ₂ sw)))))
            where
              sγ₂ : ∀ {w w′} → Same ((⟦ GA ⟧F R) ⟨ σ ⟩) w w′ → SameEnv Σ fmt S σ (Γ ▸ R ▸ ⟦ GA ⟧F R) (One ∷ Ψ₂) (eb , w)
              sγ₂ sw = sameEnv▸ σ {Γ = Γ ▸ R} {Ψ = Ψ₂} {A = ⟦ GA ⟧F R} One (W1.sameEnvOf rb)
                         (slotAgree σ {⟦ GA ⟧F R} One One (sameRefl ((⟦ GA ⟧F R) ⟨ σ ⟩) sw))

      STEP : ∀ {a a′} → Same (R ⟨ σ ⟩) a a′
           → Related (LayerEq (CB G) (Same (R ⟨ σ ⟩))) (toT∞ (fin f) (fmap (fin f) (toL σ GB R) (co₀ a)))
                                                    (toT∞ (fin f) (fmap (fin f) (nuLayer G c φν {νM f (CA G)}) (outν a′)))
      STEP {a} {a′} sa =
        ≈-Relatedˡ (toT∞-fmap (fin f) _ (co₀ a))
          (≈-Relatedʳ (≈-trans (toT∞-fmap (fin f) _ (outν a′))
                        (≈-sym (≈-trans (assoc _ _ _) (≈-bind (≈-refl _) (λ l → ≈-trans (idˡ _ _) (≡→≈ (cong return∞ (nuEq G c φν l))))))))
            (bindRel {g = λ w → return∞ (toL σ GB R w)} (COALG a a′ sa) (λ s → returnRel (Fn.toL-same wfB R s))))
