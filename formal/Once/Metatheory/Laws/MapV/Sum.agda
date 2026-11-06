{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws.MapV.Sum — the cases of the map at a variable, a product and a sum,
-- and of the layer map at a product and a sum. Each takes the recursive
-- calls as parameters (`Laws.MapV.Map` ties the knot).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature; OneName)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Laws.MapV.Sum (Σ : Signature) (u : OneName Σ) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

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

module MapVSum {m : ℕ} {Δ : KCtx m} (δ : DefSem) (sd : SameDefs Σ fmt S δ) (σ : TySub m 0) (r : Respects Δ ∅ₖ σ)
            (A B : Ty m) where
  open MapAt Δ σ A B
  open MapV δ sd σ r A B
  open Reads

  bodyVar0 : BodyAt (var fz)
  bodyVar0 γ sγ c {φ} {hv = hv} {xv} Rh Rx sx Hc db {γa} ra = goA (WF.viewApp db ra)
    where
      module W  = Views δ sd σ r γ sγ
      module WF = FunV δ sd σ r γ sγ
      goA : WF.AppView db γa → Related (Same (B ⟨ σ ⟩)) (W.⟪ db ⟫ γa) (return∞ (φ p-var xv))
      goA (WF.appView {q = Zero} {πl = πl} df dx rf eq) with ty Rh df | ty Rx dx
      ... | refl | refl =
        W.~trans {B} eq (W.~trans {B}
          (≈-Relatedʳ (≈-sym (idˡ hv (λ fv → toT∞ πl (fv tt))))
            (bindRel {f = λ fv → toT∞ πl (fv tt)} {g = λ fv → toT∞ πl (fv tt)} (rd Rh df rf)
              (λ sf → callRel Zero {πl} {A ⟨ σ ⟩} {B ⟨ σ ⟩} sf sx)))
          (Hc p-var refl xv xv sx))
      goA (WF.appView {q = One} {πl = πl} df dx rf (ex , rx , eq)) with ty Rh df | ty Rx dx
      ... | refl | refl =
        W.~trans {B} eq (W.~trans {B}
          (≈-Relatedʳ (≈-sym (≈-trans (idˡ hv (λ fv → return∞ xv >>=∞ λ a → toT∞ πl (fv a))) (idˡ xv (λ a → toT∞ πl (hv a)))))
            (bindRel {f = λ fv → W.⟪ dx ⟫ ex >>=∞ λ a → toT∞ πl (fv a)} {g = λ fv → return∞ xv >>=∞ λ a → toT∞ πl (fv a)}
              (rd Rh df rf) (λ {fv} {fv′} sf →
                bindRel {f = λ a → toT∞ πl (fv a)} {g = λ a → toT∞ πl (fv′ a)} (rd Rx dx rx)
                  (λ sa → callRel One {πl} {A ⟨ σ ⟩} {B ⟨ σ ⟩} sf sa))))
          (Hc p-var refl xv xv sx))
      goA (WF.appView {q = Many} {πl = πl} df dx rf (ex , rx , eq)) with ty Rh df | ty Rx dx
      ... | refl | refl =
        W.~trans {B} eq (W.~trans {B}
          (≈-Relatedʳ (≈-sym (≈-trans (idˡ hv (λ fv → return∞ xv >>=∞ λ a → toT∞ πl (fv a))) (idˡ xv (λ a → toT∞ πl (hv a)))))
            (bindRel {f = λ fv → W.⟪ dx ⟫ ex >>=∞ λ a → toT∞ πl (fv a)} {g = λ fv → return∞ xv >>=∞ λ a → toT∞ πl (fv a)}
              (rd Rh df rf) (λ {fv} {fv′} sf →
                bindRel {f = λ a → toT∞ πl (fv a)} {g = λ a → toT∞ πl (fv′ a)} (rd Rx dx rx)
                  (λ sa → callRel Many {πl} {A ⟨ σ ⟩} {B ⟨ σ ⟩} sf sa))))
          (Hc p-var refl xv xv sx))

  bodyProd : ∀ {T₁ T₂} → BodyAt T₁ → BodyAt T₂ → BodyAt (T₁ * T₂)
  bodyProd {T₁} {T₂} rec₁ rec₂ γ sγ (c₁ , c₂) {φ} {xv = xv} Rh Rx sx Hc db ra with ProdV.viewPair δ sd σ r γ sγ db ra
  ... | ProdV.pairView da db′ ra′ rb′ eq =
    Views.~trans δ sd σ r γ sγ {(T₁ * T₂) ⟨ at₀ B ⟩} eq
      (≈-Relatedʳ (≈-sym (≈-trans (idˡ _ _) (idˡ _ _)))
        (bindRel (rec₁ γ sγ c₁ Rh (readsFst γ sγ Rx) (proj₁ sx) (λ o → Hc (p-*ˡ o)) da ra′) (λ s₁ →
          bindRel (rec₂ γ sγ c₂ Rh (readsSnd γ sγ Rx) (proj₂ sx) (λ o → Hc (p-*ʳ o)) db′ rb′) (λ s₂ →
            returnRel (s₁ , s₂)))))

  bodySum : ∀ {T₁ T₂} → BodyAt T₁ → BodyAt T₂ → BodyAt (T₁ + T₂)
  bodySum {T₁} {T₂} rec₁ rec₂ {Γ = Γ} γ sγ (c₁ , c₂) {φ} {xv = xv} Rh Rx sx Hc db ra with Views.viewCase δ sd σ r γ sγ db ra
  ... | Views.caseView {Ψc = Ψc} ds dl dr {ec = ec} rs rc eq with ty Rx ds
  ...   | refl = W.~trans {T₁ ⟨ at₀ B ⟩ + T₂ ⟨ at₀ B ⟩} eq (≈-Relatedʳ (≈-sym (idˡ xv _))
                  (bindRel {f = [ (λ a → W.⟪ dl ⟫▸ ec (slot Many a)) , (λ b → W.⟪ dr ⟫▸ ec (slot Many b)) ]′}
                           {g = λ u′ → return∞ (mapS (T₁ + T₂) (c₁ , c₂) φ u′)} (rd Rx ds rs) (λ {u} {u′} su → BR {u} {u′} su)))
    where
      module W = Views δ sd σ r γ sγ
      TA₁ = T₁ ⟨ at₀ A ⟩
      TA₂ = T₂ ⟨ at₀ A ⟩
      BR : ∀ {u u′} → Same ((TA₁ + TA₂) ⟨ σ ⟩) u u′
         → Related (Same ((T₁ ⟨ at₀ B ⟩ + T₂ ⟨ at₀ B ⟩) ⟨ σ ⟩))
             ([ (λ a → W.⟪ dl ⟫▸ ec (slot Many a)) , (λ b → W.⟪ dr ⟫▸ ec (slot Many b)) ]′ u)
             (return∞ (mapS (T₁ + T₂) (c₁ , c₂) φ u′))
      BR {inj₁ a} {inj₁ a′} s with Views.viewInl δ sd σ r (ec , slot Many a) se₁ dl (Views.base δ sd σ r (ec , slot Many a) se₁)
        where se₁ = sameEnv▸ σ {Γ = Γ} {Ψ = Ψc} {A = TA₁} Many (W.sameEnvOf rc) (slotAgree σ {TA₁} Many Many (sameRefl (TA₁ ⟨ σ ⟩) s))
      ... | Views.inlView da r₀ eq₁ =
        W.~trans {T₁ ⟨ at₀ B ⟩ + T₂ ⟨ at₀ B ⟩} eq₁
          (≈-Relatedʳ (≈-sym (idˡ (mapS T₁ c₁ (λ o → φ (p-+ˡ o)) a′) (λ v → return∞ (inj₁ v))))
          (bindRel {f = λ v → return∞ (inj₁ v)} {g = λ v → return∞ (inj₁ v)} (rec₁ (ec , slot Many a) se₁ c₁ (readsWk γ sγ rc (slot Many a) se₁ Rh)
                      (readsVar (ec , slot Many a) se₁ (valAt0 σ {Γ = Γ} {A = TA₁} Many {γ = ec} s))
                      (sameSelf TA₁ s) (λ o → Hc (p-+ˡ o)) da r₀)
                   (λ sv → returnRel sv)))
        where se₁ = sameEnv▸ σ {Γ = Γ} {Ψ = Ψc} {A = TA₁} Many (W.sameEnvOf rc) (slotAgree σ {TA₁} Many Many (sameRefl (TA₁ ⟨ σ ⟩) s))
      BR {inj₂ b} {inj₂ b′} s with Views.viewInr δ sd σ r (ec , slot Many b) se₂ dr (Views.base δ sd σ r (ec , slot Many b) se₂)
        where se₂ = sameEnv▸ σ {Γ = Γ} {Ψ = Ψc} {A = TA₂} Many (W.sameEnvOf rc) (slotAgree σ {TA₂} Many Many (sameRefl (TA₂ ⟨ σ ⟩) s))
      ... | Views.inrView db₂ r₀ eq₂ =
        W.~trans {T₁ ⟨ at₀ B ⟩ + T₂ ⟨ at₀ B ⟩} eq₂
          (≈-Relatedʳ (≈-sym (idˡ (mapS T₂ c₂ (λ o → φ (p-+ʳ o)) b′) (λ v → return∞ (inj₂ v))))
          (bindRel {f = λ v → return∞ (inj₂ v)} {g = λ v → return∞ (inj₂ v)} (rec₂ (ec , slot Many b) se₂ c₂ (readsWk γ sγ rc (slot Many b) se₂ Rh)
                      (readsVar (ec , slot Many b) se₂ (valAt0 σ {Γ = Γ} {A = TA₂} Many {γ = ec} s))
                      (sameSelf TA₂ s) (λ o → Hc (p-+ʳ o)) db₂ r₀)
                   (λ sv → returnRel sv)))
        where se₂ = sameEnv▸ σ {Γ = Γ} {Ψ = Ψc} {A = TA₂} Many (W.sameEnvOf rc) (slotAgree σ {TA₂} Many Many (sameRefl (TA₂ ⟨ σ ⟩) s))
      BR {inj₁ a} {inj₂ b′} ()
      BR {inj₂ b} {inj₁ a′} ()

  layerProd : ∀ {R H₁ H₂} → LayerAt R H₁ → LayerAt R H₂ → LayerAt R (H₁ ⊗ H₂)
  layerProd {R} {H₁} {H₂} rec₁ rec₂ γ sγ (c₁ , c₂) {φ} {wv = xv} Rh Rx sx Hc db ra with ProdV.viewPair δ sd σ r γ sγ db ra
  ... | ProdV.pairView da db′ ra′ rb′ eq =
    Views.~trans δ sd σ r γ sγ {⟦ (H₁ ⊗ H₂) ⟨ at₀ B ⟩F ⟧F R} eq
      (≈-Relatedʳ (≈-sym (≈-trans (idˡ _ _) (idˡ _ _)))
        (bindRel (rec₁ γ sγ c₁ Rh (readsFst γ sγ Rx) (proj₁ sx) (λ o → Hc (p-⊗ˡ o)) da ra′) (λ s₁ →
          bindRel (rec₂ γ sγ c₂ Rh (readsSnd γ sγ Rx) (proj₂ sx) (λ o → Hc (p-⊗ʳ o)) db′ rb′) (λ s₂ →
            returnRel (s₁ , s₂)))))

  layerSum : ∀ {R H₁ H₂} → LayerAt R H₁ → LayerAt R H₂ → LayerAt R (H₁ ⊕ H₂)
  layerSum {R} {H₁} {H₂} rec₁ rec₂ {Γ = Γ} γ sγ (c₁ , c₂) {φ} {wv = xv} Rh Rx sx Hc db ra with Views.viewCase δ sd σ r γ sγ db ra
  ... | Views.caseView {Ψc = Ψc} ds dl dr {ec = ec} rs rc eq with ty Rx ds
  ...   | refl = W.~trans {⟦ H₁ ⟨ at₀ B ⟩F ⟧F R + ⟦ H₂ ⟨ at₀ B ⟩F ⟧F R} eq (≈-Relatedʳ (≈-sym (idˡ xv _))
                  (bindRel {f = [ (λ a → W.⟪ dl ⟫▸ ec (slot Many a)) , (λ b → W.⟪ dr ⟫▸ ec (slot Many b)) ]′}
                           {g = λ u′ → return∞ (layerS R (H₁ ⊕ H₂) (c₁ , c₂) φ u′)} (rd Rx ds rs) (λ {u} {u′} su → BR {u} {u′} su)))
    where
      module W = Views δ sd σ r γ sγ
      TA₁ = ⟦ H₁ ⟨ at₀ A ⟩F ⟧F R
      TA₂ = ⟦ H₂ ⟨ at₀ A ⟩F ⟧F R
      BR : ∀ {u u′} → Same ((TA₁ + TA₂) ⟨ σ ⟩) u u′
         → Related (Same ((⟦ H₁ ⟨ at₀ B ⟩F ⟧F R + ⟦ H₂ ⟨ at₀ B ⟩F ⟧F R) ⟨ σ ⟩))
             ([ (λ a → W.⟪ dl ⟫▸ ec (slot Many a)) , (λ b → W.⟪ dr ⟫▸ ec (slot Many b)) ]′ u)
             (return∞ (layerS R (H₁ ⊕ H₂) (c₁ , c₂) φ u′))
      BR {inj₁ a} {inj₁ a′} s with Views.viewInl δ sd σ r (ec , slot Many a) se₁ dl (Views.base δ sd σ r (ec , slot Many a) se₁)
        where se₁ = sameEnv▸ σ {Γ = Γ} {Ψ = Ψc} {A = TA₁} Many (W.sameEnvOf rc) (slotAgree σ {TA₁} Many Many (sameRefl (TA₁ ⟨ σ ⟩) s))
      ... | Views.inlView da r₀ eq₁ =
        W.~trans {⟦ H₁ ⟨ at₀ B ⟩F ⟧F R + ⟦ H₂ ⟨ at₀ B ⟩F ⟧F R} eq₁
          (≈-Relatedʳ (≈-sym (idˡ (layerS R H₁ c₁ (λ o → φ (p-⊕ˡ o)) a′) (λ v → return∞ (inj₁ v))))
          (bindRel {f = λ v → return∞ (inj₁ v)} {g = λ v → return∞ (inj₁ v)} (rec₁ (ec , slot Many a) se₁ c₁ (readsWk γ sγ rc (slot Many a) se₁ Rh)
                      (readsVar (ec , slot Many a) se₁ (valAt0 σ {Γ = Γ} {A = TA₁} Many {γ = ec} s))
                      (sameSelf TA₁ s) (λ o → Hc (p-⊕ˡ o)) da r₀)
                   (λ sv → returnRel sv)))
        where se₁ = sameEnv▸ σ {Γ = Γ} {Ψ = Ψc} {A = TA₁} Many (W.sameEnvOf rc) (slotAgree σ {TA₁} Many Many (sameRefl (TA₁ ⟨ σ ⟩) s))
      BR {inj₂ b} {inj₂ b′} s with Views.viewInr δ sd σ r (ec , slot Many b) se₂ dr (Views.base δ sd σ r (ec , slot Many b) se₂)
        where se₂ = sameEnv▸ σ {Γ = Γ} {Ψ = Ψc} {A = TA₂} Many (W.sameEnvOf rc) (slotAgree σ {TA₂} Many Many (sameRefl (TA₂ ⟨ σ ⟩) s))
      ... | Views.inrView db₂ r₀ eq₂ =
        W.~trans {⟦ H₁ ⟨ at₀ B ⟩F ⟧F R + ⟦ H₂ ⟨ at₀ B ⟩F ⟧F R} eq₂
          (≈-Relatedʳ (≈-sym (idˡ (layerS R H₂ c₂ (λ o → φ (p-⊕ʳ o)) b′) (λ v → return∞ (inj₂ v))))
          (bindRel {f = λ v → return∞ (inj₂ v)} {g = λ v → return∞ (inj₂ v)} (rec₂ (ec , slot Many b) se₂ c₂ (readsWk γ sγ rc (slot Many b) se₂ Rh)
                      (readsVar (ec , slot Many b) se₂ (valAt0 σ {Γ = Γ} {A = TA₂} Many {γ = ec} s))
                      (sameSelf TA₂ s) (λ o → Hc (p-⊕ʳ o)) db₂ r₀)
                   (λ sv → returnRel sv)))
        where se₂ = sameEnv▸ σ {Γ = Γ} {Ψ = Ψc} {A = TA₂} Many (W.sameEnvOf rc) (slotAgree σ {TA₂} Many Many (sameRefl (TA₂ ⟨ σ ⟩) s))
      BR {inj₁ a} {inj₂ b′} ()
      BR {inj₂ b} {inj₁ a′} ()
