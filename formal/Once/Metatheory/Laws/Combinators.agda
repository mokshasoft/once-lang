{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws.Combinators — what `pair f g`, `[ f , g ]` and
-- `curry f` mean (`Core.Derived`), as `Laws.Compose` does for `compose`: the
-- arms run, then the closure is `pairᵛ`, `caseᵛ`, `curryᵛ` up to sameness.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature; OneName)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Laws.Combinators (Σ : Signature) (u : OneName Σ) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Once.Spec.Grade using (Quantity; Zero; One; Many; mk-kind; Purity; pure)
open import Once.Spec.Type using (Ty; KCtx; TySub; Respects; ∅ₖ; _⟨_⟩; _⇒[_]_; _*_; _+_)
open import Once.Spec.Context using (Ctx; _▸_; _∷_; Usage; lookup; _⊑ᵘ_)
open import Once.Spec.Core.Syntax
open import Once.Spec.Core.Derived using (pairᶜ; caseᶜ; curryᶜ)
open import Once.Spec.Core.Typing Σ S
open import Once.Spec.Core.Meaning Σ fmt S
open import Once.Spec.Effect Σ using (M; bind; return; T∞; _>>=∞_; return∞; _≈_; toT∞)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ)
open import Once.Spec.Equivalence Σ using (Same)
open import Once.Spec.Metatheory using (SameDefs; SameEnv)
open import Once.Metatheory.Erase Σ using (toT∞-bind; toT∞-return)
open import Once.Metatheory.Bisim Σ using (≈-refl; ≈-sym; ≈-trans; ≈-bind; idˡ)
open import Once.Metatheory.Coherence.Relation Σ using (Related; ≈-Relatedˡ; ≈-Relatedʳ; bindRel; returnRel; toObserved)
open import Once.Metatheory.Coherence.Layer Σ using (rel; runs; appMany)
open import Once.Metatheory.Coherence.Uniqueness Σ S using (ty-unique)
open import Once.Metatheory.TermModel.Subst Σ S using (wk-⊢)
open import Once.Metatheory.Laws.Tools Σ u fmt S
open import Once.Metatheory.Laws.Views Σ u fmt S
open import Once.Metatheory.Laws.Strengthen Σ S using (varTy)
open import Once.Metatheory.Laws.Compose Σ u fmt S using (ValAt; valAt▸; valAt0; ≡→≈; module CompV)

-- Both arms at the same argument, left first.
pairᵛ : ∀ π {X Y Z : Set} → (X → M π Y) → (X → M π Z) → X → M π (Y × Z)
pairᵛ π fv gv c = bind π (fv c) λ x → bind π (gv c) λ y → return π (x , y)

module CombV {m : ℕ} {Δ : KCtx m} (δ : DefSem) (sd : SameDefs Σ fmt S δ) (σ : TySub m 0) (r : Respects Δ ∅ₖ σ) where
  open CompV δ sd σ r using (readAt)

  -- the body `pair (app v2 v0) (app v1 v0)`
  bodyP : ∀ {n} {Γ : Ctx m n} {Ψ A B C π πt} (γ : Env σ (Γ ▸ (C ⇒[ mk-kind Many π ] A) ▸ (C ⇒[ mk-kind Many π ] B) ▸ C) Ψ)
            (sγ : SameEnv Σ fmt S σ _ Ψ γ) {fv′ gv′ c′}
        → ValAt σ γ (suc (suc zero)) fv′ → ValAt σ γ (suc zero) gv′ → ValAt σ γ zero c′
        → (dt : Δ ⊩ _ ⊢[ Ψ ] pair (app (var (suc (suc zero))) (var zero)) (app (var (suc zero)) (var zero)) ∷ A * B ! πt)
        → Related (Same ((A * B) ⟨ σ ⟩)) (toT∞ πt (⟦ dt ⟧ δ σ r γ)) (toT∞ π (pairᵛ π fv′ gv′ c′))
  bodyP {A = A} {B} {C} {π} γ sγ {fv′} {gv′} {c′} h2 h1 h0 dt = goP (WP.viewPair dt W.base)
    where
      module W  = Views δ sd σ r γ sγ
      module WF = FunV δ sd σ r γ sγ
      module WP = ProdV δ sd σ r γ sγ
      goP : WP.PairView dt γ → _
      goP (WP.pairView da db {ea} {eb} ra rb eqP) =
        W.~trans {A * B} eqP
          (≈-Relatedʳ NORM
            (bindRel {f = λ x → W.⟪ db ⟫ eb >>=∞ λ y → return∞ (x , y)} {g = λ x → toT∞ π (gv′ c′) >>=∞ λ y → return∞ (x , y)}
              (hA (WF.viewApp da ra))
              (λ {x} {x′} sx → bindRel {f = λ y → return∞ (x , y)} {g = λ y → return∞ (x′ , y)} (hB (WF.viewApp db rb))
                 (λ sy → returnRel (sx , sy)))))
        where
          NORM : toT∞ π (pairᵛ π fv′ gv′ c′) ≈ (toT∞ π (fv′ c′) >>=∞ λ x → toT∞ π (gv′ c′) >>=∞ λ y → return∞ (x , y))
          NORM = ≈-trans (toT∞-bind π (fv′ c′) _) (≈-bind (≈-refl _) λ x →
                   ≈-trans (toT∞-bind π (gv′ c′) _) (≈-bind (≈-refl _) λ y → toT∞-return π (x , y)))
          hA : WF.AppView da ea → W._~_ {A} (W.⟪ da ⟫ ea) (toT∞ π (fv′ c′))
          hA (WF.appView df₃ dx₃ {ef₃} rf₃ sem₃) with varTy df₃
          ... | refl = ≈-Relatedʳ (≈-sym (idˡ c′ (λ a → toT∞ π (fv′ a))))
                         (WF.appMany~ df₃ dx₃ sem₃ (readAt γ sγ df₃ rf₃ h2) (λ rx → readAt γ sγ dx₃ rx h0))
          hB : WF.AppView db eb → W._~_ {B} (W.⟪ db ⟫ eb) (toT∞ π (gv′ c′))
          hB (WF.appView df₃ dx₃ {ef₃} rf₃ sem₃) with varTy df₃
          ... | refl = ≈-Relatedʳ (≈-sym (idˡ c′ (λ a → toT∞ π (gv′ a))))
                         (WF.appMany~ df₃ dx₃ sem₃ (readAt γ sγ df₃ rf₃ h1) (λ rx → readAt γ sγ dx₃ rx h0))

  lamP : ∀ {n} {Γ : Ctx m n} {Ψ A B C π πl} (γ : Env σ (Γ ▸ (C ⇒[ mk-kind Many π ] A) ▸ (C ⇒[ mk-kind Many π ] B)) Ψ)
           (sγ : SameEnv Σ fmt S σ _ Ψ γ) {fv′ gv′}
       → ValAt σ γ (suc zero) fv′ → ValAt σ γ zero gv′
       → (dl : Δ ⊩ _ ⊢[ Ψ ] lam C Many π (pair (app (var (suc (suc zero))) (var zero)) (app (var (suc zero)) (var zero)))
                 ∷ C ⇒[ mk-kind Many π ] (A * B) ! πl)
       → Related (Same ((C ⇒[ mk-kind Many π ] (A * B)) ⟨ σ ⟩)) (toT∞ πl (⟦ dl ⟧ δ σ r γ)) (return∞ (pairᵛ π fv′ gv′))
  lamP {Γ = Γ} {A = A} {B} {C} {π} γ sγ {fv′} {gv′} h1 h0 dl = goL (WF.viewLam dl W.base)
    where
      module W  = Views δ sd σ r γ sγ
      module WF = FunV δ sd σ r γ sγ
      Γ′ = Γ ▸ (C ⇒[ mk-kind Many π ] A) ▸ (C ⇒[ mk-kind Many π ] B)
      goL : WF.LamView dl γ → _
      goL (WF.lamView {q′ = q′} {Ψ₀} le dt {e₀} (W.res P₁ refl) refl eqL) =
        W.~trans {C ⇒[ mk-kind Many π ] (A * B)} eqL (returnRel SAME)
        where
          SAME : Same ((C ⇒[ mk-kind Many π ] (A * B)) ⟨ σ ⟩) (⟦ ⊢lam le dt ⟧ δ σ r e₀) (pairᵛ π fv′ gv′)
          SAME c c′ sc = toObserved
            (≈-Relatedˡ (≡→≈ (cong (toT∞ π) (WF.lamCall le dt e₀ c)))
              (bodyP (e₀ , slot q′ c) se₃ (valAt▸ σ {Γ = Γ′} {A = C} {q = q′} P₁ {γ = γ} (slot q′ c) h1)
                                         (valAt▸ σ {Γ = Γ′} {A = C} {q = q′} P₁ {γ = γ} (slot q′ c) h0)
                                         (valAt0 σ {Γ = Γ′} {A = C} q′ {γ = e₀} sc) dt))
            where
              se₃ = sameEnv▸ σ {Γ = Γ′} {Ψ = Ψ₀} {A = C} q′ (W.sameEnvOf (W.res P₁ refl))
                      (slotAgree σ {C} q′ q′ (sameRefl (C ⟨ σ ⟩) sc))

  pairSem : ∀ {n} {Γ : Ctx m n} {Ψ : Usage n} (γ : Env σ Γ Ψ) (sγ : SameEnv Σ fmt S σ Γ Ψ γ)
              {Ψa Ψf Ψg A B C π π₀ πf πg f g}
              (d : Δ ⊩ Γ ⊢[ Ψa ] pairᶜ C π f g ∷ C ⇒[ mk-kind Many π ] (A * B) ! π₀) {γa : Env σ Γ Ψa}
          → Views.Res δ sd σ r γ sγ γa
          → (df : Δ ⊩ Γ ⊢[ Ψf ] f ∷ C ⇒[ mk-kind Many π ] A ! πf) {ef : Env σ Γ Ψf} → Views.Res δ sd σ r γ sγ ef
          → (dg : Δ ⊩ Γ ⊢[ Ψg ] g ∷ C ⇒[ mk-kind Many π ] B ! πg) {eg : Env σ Γ Ψg} → Views.Res δ sd σ r γ sγ eg
          → Related (Same ((C ⇒[ mk-kind Many π ] (A * B)) ⟨ σ ⟩)) (toT∞ π₀ (⟦ d ⟧ δ σ r γa))
              (toT∞ πf (⟦ df ⟧ δ σ r ef) >>=∞ λ fv → toT∞ πg (⟦ dg ⟧ δ σ r eg) >>=∞ λ gv → return∞ (pairᵛ π fv gv))
  pairSem {Γ = Γ} γ sγ {A = A} {B} {C} {π} d {γa} ra df {ef} rf dg {eg} rg = go (W.viewLet d ra)
    where
      module W  = Views δ sd σ r γ sγ
      module WF = FunV δ sd σ r γ sγ
      T = C ⇒[ mk-kind Many π ] (A * B)
      F = C ⇒[ mk-kind Many π ] A
      G = C ⇒[ mk-kind Many π ] B

      go : W.LetView d γa → _
      go (W.letView {Ψ₂ = Ψb} de db {eb} rb (ee , re , eq1)) with ty-unique de df
      ... | refl = W.~trans {T} eq1 (bindRel (runs (W.fl de df re rf)) (λ {fv} {fv′} sf → inner sf))
        where
          inner : ∀ {fv fv′} → Same (F ⟨ σ ⟩) fv fv′
                → W._~_ {T} (W.⟪ db ⟫▸ eb fv) (W.⟪ dg ⟫ eg >>=∞ λ gv → return∞ (pairᵛ π fv′ gv))
          inner {fv} {fv′} sf = goW (W1.viewLet db W1.base)
            where
              se₁ = sameEnv▸ σ {Γ = Γ} {Ψ = Ψb} {A = F} One (W.sameEnvOf rb) (sameRefl (F ⟨ σ ⟩) sf)
              module W1 = Views δ sd σ r {Γ = Γ ▸ F} {Ψ = One ∷ Ψb} (eb , fv) se₁
              goW : W1.LetView db (eb , fv) → _
              goW (W1.letView {Ψ₁ = _ ∷ _} {Ψ₂ = Ψl} dwg dl {eb₂} (W1.res P₂ refl) (eg′ , W1.res Pg refl , eq2)) with ty-unique (wk-⊢ dg) dwg
              ... | refl = W.~trans {T} eq2 (bindRel (WF.wkRelR dwg rb fv Pg dg rg) (λ {gv} {gv′} sg →
                             lamP (e₂ , gv) (se₂ sg) (valAt▸ σ {Γ = Γ ▸ F} {A = G} {q = One} P₂ {γ = eb , fv} gv (valAt0 σ {Γ = Γ} {A = F} One {γ = eb} sf))
                               (valAt0 σ {Γ = Γ ▸ F} {A = G} One {γ = e₂} sg) dl))
                where
                  e₂ = restrict σ {Γ = Γ ▸ F} P₂ (eb , fv)
                  se₂ : ∀ {gv gv′} → Same (G ⟨ σ ⟩) gv gv′ → SameEnv Σ fmt S σ (Γ ▸ F ▸ G) (One ∷ Ψl) (e₂ , gv)
                  se₂ sg = sameEnv▸ σ {Γ = Γ ▸ F} {Ψ = Ψl} {A = G} One (W1.sameEnvOf (W1.res P₂ refl)) (sameRefl (G ⟨ σ ⟩) sg)
