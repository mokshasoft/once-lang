{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws.MapTop — what `mapᶜ T A B f` means, in any
-- derivation: `f` runs, then the closure is the semantic map
-- (`Laws.MapSem.mapS`) of what `f`'s value does where the variable occurs.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature; OneName)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Laws.MapTop (Σ : Signature) (u : OneName Σ) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

open import Data.Fin using () renaming (zero to fz; suc to fs)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)
open import Data.Product using (Σ-syntax)
open import Once.Spec.Grade using (Quantity; Many; mk-kind; pure; Purity)
open import Once.Spec.Type using (Ty; KCtx; TySub; Respects; ∅ₖ; _⟨_⟩; _⇒[_]_; at₀)
open import Once.Spec.Context using (Ctx; _▸_; _∷_)
open import Once.Spec.Core.Syntax
open import Once.Spec.Core.Derived using (mapᶜ)
open import Once.Spec.Core.Typing Σ S
open import Once.Spec.Core.Meaning Σ fmt S
open import Once.Spec.Effect Σ using (T∞; _>>=∞_; return∞; toT∞)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ)
open import Once.Spec.Equivalence Σ using (Same)
open import Once.Spec.Metatheory using (SameDefs; SameEnv)
open import Once.Metatheory.Coherence.Relation Σ using (Related; ≈-Relatedˡ; bindRel; returnRel; returnRel⁻; toObserved)
open import Once.Metatheory.Coherence.Layer Σ using (runs)
open import Once.Metatheory.Coherence.Uniqueness Σ S using (ty-unique)
open import Once.Metatheory.Laws.Tools Σ u fmt S
open import Once.Metatheory.Laws.Views Σ u fmt S
open import Once.Metatheory.Laws.Compose Σ u fmt S using (valAt0; valAt▸; ≡→≈)
import Once.Metatheory.Laws.Strengthen
open import Once.Metatheory.Laws.MapSem Σ using (module MapAt; Occ; OccF; p-var; p-*ˡ; p-*ʳ; p-+ˡ; p-+ʳ; p-⇒ʳ; p-μ; p-ν; p-K; p-⊕ˡ; p-⊕ʳ; p-⊗ˡ; p-⊗ʳ)
open import Once.Metatheory.Laws.MapCov Σ S using (letInv; lamInv; cod≡; module Covs)
open import Once.Metatheory.Laws.ComposeG Σ u fmt S using (callRel)

open import Once.Metatheory.Laws.MapV Σ u fmt S using (module MapV)
open import Once.Metatheory.Laws.MapV.Map Σ u fmt S using (module MapVMap)

module MapTopV {m : ℕ} {Δ : KCtx m} (δ : DefSem) (sd : SameDefs Σ fmt S δ) (σ : TySub m 0) (r : Respects Δ ∅ₖ σ)
               (A B : Ty m) where
  open MapAt Δ σ A B
  open MapV δ sd σ r A B
  open MapVMap δ sd σ r A B using (bodyMap)
  open Covs {m} {Δ} {σ} A B using (covOf; occTy)

  -- The coverage a derivation of `mapᶜ T A B f` fixes.
  covD : ∀ {n} {Γ : Ctx m n} {Ψ π₀ f} T → Δ ⊩ Γ ⊢[ Ψ ] mapᶜ T A B f ∷ T ⟨ at₀ A ⟩ ⇒[ mk-kind Many pure ] T ⟨ at₀ B ⟩ ! π₀ → Cov T
  covD T d with letInv d
  ... | _ , _ , _ , _ , _ , de , db with lamInv db
  ...   | _ , _ , _ , eqT , dt with cod≡ {Δ = Δ} eqT
  ...     | refl = covOf T dt

  mapSem : ∀ {n} {Γ : Ctx m n} {Ψ} (γ : Env σ Γ Ψ) (sγ : SameEnv Σ fmt S σ Γ Ψ γ) T {Ψa π₀ f}
             (d : Δ ⊩ Γ ⊢[ Ψa ] mapᶜ T A B f ∷ T ⟨ at₀ A ⟩ ⇒[ mk-kind Many pure ] T ⟨ at₀ B ⟩ ! π₀) {γa}
         → Views.Res δ sd σ r γ sγ γa
         → ∀ {F Ψf πf} (df : Δ ⊩ Γ ⊢[ Ψf ] f ∷ F ! πf) {ef} → Views.Res δ sd σ r γ sγ ef
         → (Φ : ⟦ F ⟨ σ ⟩ ⟧ᵛ → Fn T) → (∀ {hv hv′} → Same (F ⟨ σ ⟩) hv hv′ → HCall T (Φ hv′) F hv)
         → Related (Same ((T ⟨ at₀ A ⟩ ⇒[ mk-kind Many pure ] T ⟨ at₀ B ⟩) ⟨ σ ⟩)) (toT∞ π₀ (⟦ d ⟧ δ σ r γa))
             (toT∞ πf (⟦ df ⟧ δ σ r ef) >>=∞ λ hv → return∞ (λ x → mapS T (covD T d) (Φ hv) x))
  mapSem {Γ = Γ} γ sγ T {f = f} d {γa} ra {F} df {ef} rf Φ HΦ with W.viewLet d ra
    where module W = Views δ sd σ r γ sγ
  ... | Views.letView {Ψ₂ = Ψb} de db {eb} rb (ee , re , eq) with ty-unique de df
  ...   | refl = W.~trans {TT} eq (bindRel (runs (W.fl de df re rf)) (λ {hv} {hv′} sh → LAM sh))
    where
      module W = Views δ sd σ r γ sγ
      TT = T ⟨ at₀ A ⟩ ⇒[ mk-kind Many pure ] T ⟨ at₀ B ⟩
      LAM : ∀ {hv hv′} → Same (F ⟨ σ ⟩) hv hv′
          → Related (Same (TT ⟨ σ ⟩)) (W.⟪ db ⟫▸ eb hv) (return∞ (λ x → mapS T (covD T d) (Φ hv′) x))
      LAM {hv} {hv′} sh with FunV.viewLam δ sd σ r {Γ = Γ ▸ F} {Ψ = Many ∷ Ψb} (eb , hv) sγ₁ db (Views.base δ sd σ r {Γ = Γ ▸ F} {Ψ = Many ∷ Ψb} (eb , hv) sγ₁)
        where sγ₁ = sameEnv▸ σ {Γ = Γ} {Ψ = Ψb} {A = F} Many (W.sameEnvOf rb) (slotAgree σ {F} Many Many (sameRefl (F ⟨ σ ⟩) sh))
      ... | FunV.lamView {q′ = q′} {Ψ₀} le dt {e₀} (Views.res P₁ refl) eqT eqL with cod≡ {Δ = Δ} eqT
      ...   | refl with eqT
      ...     | refl = Views.~trans δ sd σ r {Γ = Γ ▸ F} {Ψ = Many ∷ Ψb} (eb , hv) sγ₁ {TT} eqL (returnRel SAME)
        where
          sγ₁ = sameEnv▸ σ {Γ = Γ} {Ψ = Ψb} {A = F} Many (W.sameEnvOf rb) (slotAgree σ {F} Many Many (sameRefl (F ⟨ σ ⟩) sh))
          TA = T ⟨ at₀ A ⟩
          SAME : Same (TT ⟨ σ ⟩) (⟦ ⊢lam le dt ⟧ δ σ r e₀) (λ x → mapS T (covD T d) (Φ hv′) x)
          SAME a a′ sa = toObserved
            (≈-Relatedˡ (≡→≈ (cong (toT∞ pure) (FunV.lamCall δ sd σ r {Γ = Γ ▸ F} {Ψ = Many ∷ Ψb} (eb , hv) sγ₁ le dt e₀ a)))
              (bodyMap (e₀ , slot q′ a) sγ₂ T (covD T d)
                 (readsVar (e₀ , slot q′ a) sγ₂ (valAt▸ σ {Γ = Γ ▸ F} {A = TA} {q = q′} P₁ {γ = eb , hv} {i = fz} {v = hv} (slot q′ a)
                                                  (valAt0 σ {Γ = Γ} {A = F} Many {γ = eb} (sameRefl (F ⟨ σ ⟩) sh))))
                 (readsVar (e₀ , slot q′ a) sγ₂ (valAt0 σ {Γ = Γ ▸ F} {A = TA} q′ {γ = e₀} sa))
                 (sameSelf TA sa) (HΦ sh) dt (Views.base δ sd σ r (e₀ , slot q′ a) sγ₂)))
            where
              sγ₂ = sameEnv▸ σ {Γ = Γ ▸ F} {Ψ = Ψ₀} {A = TA} q′ (Views.sameEnvOf δ sd σ r {Γ = Γ ▸ F} {Ψ = Many ∷ Ψb} (eb , hv) sγ₁ (Views.res P₁ refl))
                      (slotAgree σ {TA} q′ q′ (sameRefl (TA ⟨ σ ⟩) sa))

  -- The type of any derivation of `mapᶜ T A B f`: an effect-free arrow from `T⟨A⟩`.
  mapTy : ∀ {n} {Γ : Ctx m n} {Ψ Z π f} T → Δ ⊩ Γ ⊢[ Ψ ] mapᶜ T A B f ∷ Z ! π
        → Σ[ W ∈ Ty m ] (Z ≡ T ⟨ at₀ A ⟩ ⇒[ mk-kind Many pure ] W)
  mapTy T d with letInv d
  ... | _ , _ , _ , _ , _ , de , db with lamInv db
  ...   | W , _ , _ , eqT , _ = W , eqT

  -- At a covariant occurrence, `f`'s type is an arrow from `A` to `B`.
  occD : ∀ {n} {Γ : Ctx m n} {Ψ π₀ Ψf πf f F} T
       → Δ ⊩ Γ ⊢[ Ψ ] mapᶜ T A B f ∷ T ⟨ at₀ A ⟩ ⇒[ mk-kind Many pure ] T ⟨ at₀ B ⟩ ! π₀ → Δ ⊩ Γ ⊢[ Ψf ] f ∷ F ! πf
       → Occ T → Σ[ q ∈ Quantity ] Σ[ π ∈ Purity ] (F ≡ A ⇒[ mk-kind q π ] B)
  occD T d df o with letInv d
  ... | X , _ , _ , _ , _ , de , db with ty-unique de df
  ...   | refl with lamInv db
  ...     | _ , _ , _ , eqT , dt with cod≡ {Δ = Δ} eqT
  ...       | refl = occTy T (λ dv → varTy′ dv) (λ dv → varTy′ dv) dt o
    where varTy′ = Once.Metatheory.Laws.Strengthen.varTy Σ S

  -- The map's function, from an effect-free arrow value: its calls, read at `A → B`
  -- where the variable occurs.
  Φcall : ∀ T {X Y : Ty m} {q} (eX : Occ T → X ≡ A) (eY : Occ T → Y ≡ B) → ⟦ (X ⇒[ mk-kind q pure ] Y) ⟨ σ ⟩ ⟧ᵛ → Fn T
  Φcall T eX eY hv o a = subst (λ Z → ⟦ Z ⟨ σ ⟩ ⟧ᵛ) (eY o) (callᵛ _ hv (subst (λ Z → ⟦ Z ⟨ σ ⟩ ⟧ᵛ) (sym (eX o)) a))

  private
    substK : ∀ {Z : Ty m} (p : Z ≡ Z) (v : ⟦ Z ⟨ σ ⟩ ⟧ᵛ) → subst (λ W → ⟦ W ⟨ σ ⟩ ⟧ᵛ) p v ≡ v
    substK refl v = refl

  HΦcall : ∀ T {X Y : Ty m} {q} (eX : Occ T → X ≡ A) (eY : Occ T → Y ≡ B) {hv hv′}
         → Same ((X ⇒[ mk-kind q pure ] Y) ⟨ σ ⟩) hv hv′ → HCall T (Φcall T eX eY hv′) (X ⇒[ mk-kind q pure ] Y) hv
  HΦcall T {q = q} eX eY {hv} {hv′} sh o refl a a′ sa
    rewrite substK (eY o) (callᵛ q hv′ (subst (λ Z → ⟦ Z ⟨ σ ⟩ ⟧ᵛ) (sym (eX o)) a′)) | substK (sym (eX o)) a′ =
    callRel q sh sa

  private
    substSame : ∀ {Y Z : Ty m} (e : Y ≡ Z) {x y : ⟦ Y ⟨ σ ⟩ ⟧ᵛ} → Same (Y ⟨ σ ⟩) x y
              → Same (Z ⟨ σ ⟩) (subst (λ W → ⟦ W ⟨ σ ⟩ ⟧ᵛ) e x) (subst (λ W → ⟦ W ⟨ σ ⟩ ⟧ᵛ) e y)
    substSame refl s = s

  -- The same arrows give the same functions.
  ΦcallResp : ∀ T {X Y : Ty m} {q} (eX : Occ T → X ≡ A) (eY : Occ T → Y ≡ B) {hv hv′}
            → Same ((X ⇒[ mk-kind q pure ] Y) ⟨ σ ⟩) hv hv′
            → ∀ o a a′ → Same (A ⟨ σ ⟩) a a′ → Same (B ⟨ σ ⟩) (Φcall T eX eY hv o a) (Φcall T eX eY hv′ o a′)
  ΦcallResp T {q = q} eX eY sh o a a′ sa = substSame (eY o) (returnRel⁻ (callRel q sh (substSame (sym (eX o)) sa)))
