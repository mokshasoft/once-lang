{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws.MapV.Lam — the cases of the map at an arrow (each quantity).
-- Each takes the recursive call as a parameter (`Laws.MapV.Map` ties the knot).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature; OneName)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Laws.MapV.Lam (Σ : Signature) (u : OneName Σ) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

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

module MapVLam {m : ℕ} {Δ : KCtx m} (δ : DefSem) (sd : SameDefs Σ fmt S δ) (σ : TySub m 0) (r : Respects Δ ∅ₖ σ)
            (A B : Ty m) where
  open MapAt Δ σ A B
  open MapV δ sd σ r A B
  open Reads

  private
    substSame : ∀ {X Y : Ty m} (e : X ≡ Y) {y y′ : ⟦ Y ⟨ σ ⟩ ⟧ᵛ} → Same (Y ⟨ σ ⟩) y y′
              → Same (X ⟨ σ ⟩) (subst (λ Z → ⟦ Z ⟨ σ ⟩ ⟧ᵛ) (sym e) y) (subst (λ Z → ⟦ Z ⟨ σ ⟩ ⟧ᵛ) (sym e) y′)
    substSame refl s = s

    cod≡ : ∀ {X Y Z Z′ : Ty m} {k k′} → (Y ⇒[ k ] Z) ≡ (X ⇒[ k′ ] Z′) → Z ≡ Z′
    cod≡ refl = refl

    -- A function value read at the arrow type it was written at.
    substFun : ∀ {X Y Z : Ty m} {q π} → Pos q → (eqT : (Y ⇒[ mk-kind q π ] Z) ≡ (X ⇒[ mk-kind q π ] Z)) (e : X ≡ Y)
               (g : ⟦ (X ⇒[ mk-kind q π ] Z) ⟨ σ ⟩ ⟧ᵛ) (y : ⟦ Y ⟨ σ ⟩ ⟧ᵛ)
             → callᵛ q (subst (λ W → ⟦ W ⟨ σ ⟩ ⟧ᵛ) (sym eqT) g) y ≡ callᵛ q g (subst (λ W → ⟦ W ⟨ σ ⟩ ⟧ᵛ) (sym e) y)
    substFun p1 refl refl g y = refl
    substFun pω refl refl g y = refl

    substFun0 : ∀ {X Y Z : Ty m} {π} (eqT : (Y ⇒[ mk-kind Zero π ] Z) ≡ (X ⇒[ mk-kind Zero π ] Z)) (e : X ≡ Y)
                (g : ⟦ (X ⇒[ mk-kind Zero π ] Z) ⟨ σ ⟩ ⟧ᵛ) → subst (λ W → ⟦ W ⟨ σ ⟩ ⟧ᵛ) (sym eqT) g tt ≡ g tt
    substFun0 refl refl g = refl

    sameM≡ : ∀ {π} {X : Ty m} {u u′ w : _} → u ≡ u′ → SameM π (X ⟨ σ ⟩) u′ w → SameM π (X ⟨ σ ⟩) u w
    sameM≡ refl s = s

  bodyLam0 : ∀ {T₁ T₂ π} → BodyAt T₂ → BodyAt (T₁ ⇒[ mk-kind Zero π ] T₂)
  bodyLam0 {T₁} {T₂} {π} rec {Γ = Γ} γ sγ (e , c) {φ} {xv = xv} Rh Rx sx Hc db {γa} ra
    with FunV.viewLam δ sd σ r γ sγ db ra
  ... | FunV.lamView {Ψ₀ = Ψ₀} 0≤q dt {e₀} r₀ eqT eq with cod≡ eqT
  ...   | refl = W.~trans {T} eq (returnRel SAME)
    where
      module W = Views δ sd σ r γ sγ
      T  = (T₁ ⇒[ mk-kind Zero π ] T₂) ⟨ at₀ B ⟩
      TA₁ = T₁ ⟨ at₀ A ⟩
      TA₂ = T₂ ⟨ at₀ A ⟩
      sγ₁ = sameEnv▸ σ {Γ = Γ} {Ψ = Ψ₀} {A = TA₁} Zero (W.sameEnvOf r₀) tt
      γ₁ = e₀ , tt
      module W1 = Views δ sd σ r {Γ = Γ ▸ TA₁} {Ψ = Zero ∷ Ψ₀} γ₁ sγ₁
      INNER : Related (Same (T₂ ⟨ at₀ B ⟩ ⟨ σ ⟩)) (W1.⟪ dt ⟫ γ₁) (toT∞ π (fmap π (mapS T₂ c (λ o → φ (p-⇒ʳ o))) (xv tt)))
      INNER with W1.viewLet dt W1.base
      ... | W1.letView {Ψ₂ = Ψ₂} de db₂ {eb} rb (ee , re , eq₂)
            with appRead0 γ₁ sγ₁ {X = TA₁} {Y = TA₂} (readsWk γ sγ r₀ tt sγ₁ Rx) de re
      ...   | retC rl =
              W1.~trans {T₂ ⟨ at₀ B ⟩} eq₂ (≈-Relatedʳ (toT∞-fmap π _ (xv tt))
                (bindRel {g = λ v′ → return∞ (mapS T₂ c (λ o → φ (p-⇒ʳ o)) v′)} rl (λ {v} {v′} sv →
                  rec (eb , v) (sγ₂ sv) c
                    (readsWk γ₁ sγ₁ rb v (sγ₂ sv) (readsWk γ sγ r₀ tt sγ₁ Rh))
                    (readsVar (eb , v) (sγ₂ sv) (valAt0 σ {Γ = Γ ▸ TA₁} {A = TA₂} Many {γ = eb} sv))
                    (sameSelf TA₂ sv) (λ o → Hc (p-⇒ʳ o)) db₂ (Views.base δ sd σ r (eb , v) (sγ₂ sv)))))
        where
          sγ₂ : ∀ {v v′} → Same (TA₂ ⟨ σ ⟩) v v′ → SameEnv Σ fmt S σ (Γ ▸ TA₁ ▸ TA₂) (Many ∷ Ψ₂) (eb , v)
          sγ₂ sv = sameEnv▸ σ {Γ = Γ ▸ TA₁} {Ψ = Ψ₂} {A = TA₂} Many (W1.sameEnvOf rb) (slotAgree σ {TA₂} Many Many (sameRefl (TA₂ ⟨ σ ⟩) sv))
      SAME : Same (T ⟨ σ ⟩) (subst (λ X → ⟦ X ⟨ σ ⟩ ⟧ᵛ) (sym eqT) (⟦ ⊢lam {q = Zero} 0≤q dt ⟧ δ σ r e₀)) (mapS (T₁ ⇒[ mk-kind Zero π ] T₂) (e , c) φ xv)
      SAME = sameM≡ {π = π} {X = T₂ ⟨ at₀ B ⟩} (substFun0 eqT e (⟦ ⊢lam {q = Zero} 0≤q dt ⟧ δ σ r e₀)) (toObserved INNER)

  bodyLam1 : ∀ {T₁ T₂ π} → BodyAt T₂ → BodyAt (T₁ ⇒[ mk-kind One π ] T₂)
  bodyLam1 {T₁} {T₂} {π} rec {Γ = Γ} γ sγ (e , c) {φ} {xv = xv} Rh Rx sx Hc db {γa} ra
    with FunV.viewLam δ sd σ r γ sγ db ra
  ... | FunV.lamView {q′ = q′} {Ψ₀} le dt {e₀} r₀ eqT eq with cod≡ eqT
  ...   | refl = W.~trans {T} eq (returnRel SAME)
    where
      module W = Views δ sd σ r γ sγ
      T  = (T₁ ⇒[ mk-kind One π ] T₂) ⟨ at₀ B ⟩
      TA₁ = T₁ ⟨ at₀ A ⟩
      TA₂ = T₂ ⟨ at₀ A ⟩
      SAME : Same (T ⟨ σ ⟩) (subst (λ X → ⟦ X ⟨ σ ⟩ ⟧ᵛ) (sym eqT) (⟦ ⊢lam le dt ⟧ δ σ r e₀)) (mapS (T₁ ⇒[ mk-kind One π ] T₂) (e , c) φ xv)
      SAME y y′ sy = sameM≡ {π = π} {X = T₂ ⟨ at₀ B ⟩} (trans (substFun p1 eqT e (⟦ ⊢lam le dt ⟧ δ σ r e₀) y) (FunV.lamCall δ sd σ r γ sγ le dt e₀ a))
                       (toObserved INNER)
        where
          a  = subst (λ Z → ⟦ Z ⟨ σ ⟩ ⟧ᵛ) (sym e) y
          a′ = subst (λ Z → ⟦ Z ⟨ σ ⟩ ⟧ᵛ) (sym e) y′
          sa : Same (TA₁ ⟨ σ ⟩) a a′
          sa = substSame e sy
          sγ₁ = sameEnv▸ σ {Γ = Γ} {Ψ = Ψ₀} {A = TA₁} q′ (W.sameEnvOf r₀) (slotAgree σ {TA₁} q′ q′ (sameRefl (TA₁ ⟨ σ ⟩) sa))
          γ₁ = e₀ , slot q′ a
          module W1 = Views δ sd σ r {Γ = Γ ▸ TA₁} {Ψ = q′ ∷ Ψ₀} γ₁ sγ₁
          INNER : Related (Same (T₂ ⟨ at₀ B ⟩ ⟨ σ ⟩)) (W1.⟪ dt ⟫ γ₁) (toT∞ π (fmap π (mapS T₂ c (λ o → φ (p-⇒ʳ o))) (xv a′)))
          INNER with W1.viewLet dt W1.base
          ... | W1.letView {Ψ₂ = Ψ₂} de db₂ {eb} rb (ee , re , eq₂)
                with appRead γ₁ sγ₁ {X = TA₁} {Y = TA₂} p1 (readsWk γ sγ r₀ (slot q′ a) sγ₁ Rx)
                       (readsVar γ₁ sγ₁ (valAt0 σ {Γ = Γ} {A = TA₁} q′ {γ = e₀} sa)) de re
          ...   | retC rl =
                  W1.~trans {T₂ ⟨ at₀ B ⟩} eq₂ (≈-Relatedʳ (toT∞-fmap π _ (xv a′))
                    (bindRel {g = λ v′ → return∞ (mapS T₂ c (λ o → φ (p-⇒ʳ o)) v′)} rl (λ {v} {v′} sv →
                      rec (eb , v) (sγ₂ sv) c
                        (readsWk γ₁ sγ₁ rb v (sγ₂ sv) (readsWk γ sγ r₀ (slot q′ a) sγ₁ Rh))
                        (readsVar (eb , v) (sγ₂ sv) (valAt0 σ {Γ = Γ ▸ TA₁} {A = TA₂} Many {γ = eb} sv))
                        (sameSelf TA₂ sv) (λ o → Hc (p-⇒ʳ o)) db₂ (Views.base δ sd σ r (eb , v) (sγ₂ sv)))))
            where
              sγ₂ : ∀ {v v′} → Same (TA₂ ⟨ σ ⟩) v v′ → SameEnv Σ fmt S σ (Γ ▸ TA₁ ▸ TA₂) (Many ∷ Ψ₂) (eb , v)
              sγ₂ sv = sameEnv▸ σ {Γ = Γ ▸ TA₁} {Ψ = Ψ₂} {A = TA₂} Many (W1.sameEnvOf rb) (slotAgree σ {TA₂} Many Many (sameRefl (TA₂ ⟨ σ ⟩) sv))

  bodyLamω : ∀ {T₁ T₂ π} → BodyAt T₂ → BodyAt (T₁ ⇒[ mk-kind Many π ] T₂)
  bodyLamω {T₁} {T₂} {π} rec {Γ = Γ} γ sγ (e , c) {φ} {xv = xv} Rh Rx sx Hc db {γa} ra
    with FunV.viewLam δ sd σ r γ sγ db ra
  ... | FunV.lamView {q′ = q′} {Ψ₀} le dt {e₀} r₀ eqT eq with cod≡ eqT
  ...   | refl = W.~trans {T} eq (returnRel SAME)
    where
      module W = Views δ sd σ r γ sγ
      T  = (T₁ ⇒[ mk-kind Many π ] T₂) ⟨ at₀ B ⟩
      TA₁ = T₁ ⟨ at₀ A ⟩
      TA₂ = T₂ ⟨ at₀ A ⟩
      SAME : Same (T ⟨ σ ⟩) (subst (λ X → ⟦ X ⟨ σ ⟩ ⟧ᵛ) (sym eqT) (⟦ ⊢lam le dt ⟧ δ σ r e₀)) (mapS (T₁ ⇒[ mk-kind Many π ] T₂) (e , c) φ xv)
      SAME y y′ sy = sameM≡ {π = π} {X = T₂ ⟨ at₀ B ⟩} (trans (substFun pω eqT e (⟦ ⊢lam le dt ⟧ δ σ r e₀) y) (FunV.lamCall δ sd σ r γ sγ le dt e₀ a))
                       (toObserved INNER)
        where
          a  = subst (λ Z → ⟦ Z ⟨ σ ⟩ ⟧ᵛ) (sym e) y
          a′ = subst (λ Z → ⟦ Z ⟨ σ ⟩ ⟧ᵛ) (sym e) y′
          sa : Same (TA₁ ⟨ σ ⟩) a a′
          sa = substSame e sy
          sγ₁ = sameEnv▸ σ {Γ = Γ} {Ψ = Ψ₀} {A = TA₁} q′ (W.sameEnvOf r₀) (slotAgree σ {TA₁} q′ q′ (sameRefl (TA₁ ⟨ σ ⟩) sa))
          γ₁ = e₀ , slot q′ a
          module W1 = Views δ sd σ r {Γ = Γ ▸ TA₁} {Ψ = q′ ∷ Ψ₀} γ₁ sγ₁
          INNER : Related (Same (T₂ ⟨ at₀ B ⟩ ⟨ σ ⟩)) (W1.⟪ dt ⟫ γ₁) (toT∞ π (fmap π (mapS T₂ c (λ o → φ (p-⇒ʳ o))) (xv a′)))
          INNER with W1.viewLet dt W1.base
          ... | W1.letView {Ψ₂ = Ψ₂} de db₂ {eb} rb (ee , re , eq₂)
                with appRead γ₁ sγ₁ {X = TA₁} {Y = TA₂} pω (readsWk γ sγ r₀ (slot q′ a) sγ₁ Rx)
                       (readsVar γ₁ sγ₁ (valAt0 σ {Γ = Γ} {A = TA₁} q′ {γ = e₀} sa)) de re
          ...   | retC rl =
                  W1.~trans {T₂ ⟨ at₀ B ⟩} eq₂ (≈-Relatedʳ (toT∞-fmap π _ (xv a′))
                    (bindRel {g = λ v′ → return∞ (mapS T₂ c (λ o → φ (p-⇒ʳ o)) v′)} rl (λ {v} {v′} sv →
                      rec (eb , v) (sγ₂ sv) c
                        (readsWk γ₁ sγ₁ rb v (sγ₂ sv) (readsWk γ sγ r₀ (slot q′ a) sγ₁ Rh))
                        (readsVar (eb , v) (sγ₂ sv) (valAt0 σ {Γ = Γ ▸ TA₁} {A = TA₂} Many {γ = eb} sv))
                        (sameSelf TA₂ sv) (λ o → Hc (p-⇒ʳ o)) db₂ (Views.base δ sd σ r (eb , v) (sγ₂ sv)))))
            where
              sγ₂ : ∀ {v v′} → Same (TA₂ ⟨ σ ⟩) v v′ → SameEnv Σ fmt S σ (Γ ▸ TA₁ ▸ TA₂) (Many ∷ Ψ₂) (eb , v)
              sγ₂ sv = sameEnv▸ σ {Γ = Γ ▸ TA₁} {Ψ = Ψ₂} {A = TA₂} Many (W1.sameEnvOf rb) (slotAgree σ {TA₂} Many Many (sameRefl (TA₂ ⟨ σ ⟩) sv))
