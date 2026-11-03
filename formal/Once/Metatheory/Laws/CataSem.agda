{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws.CataSem — what `cataᶜ F pure alg` and `inᶜ F` mean,
-- in any derivation: the algebra runs, then the closure is the Spec's fold
-- of its value; `inᶜ` is the closure that rolls a layer.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature; OneName)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Laws.CataSem (Σ : Signature) (u : OneName Σ) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

open import Data.Fin using () renaming (zero to fz; suc to fs)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Once.Spec.Grade using (Many; mk-kind; pure)
open import Once.Spec.Type using (Ty; Fun; KCtx; TySub; Respects; ∅ₖ; _⟨_⟩; _⟨_⟩F; _⇒[_]_; μ; ⟦_⟧F)
open import Once.Spec.Context using (Ctx; _▸_; _∷_)
open import Once.Spec.Core.Syntax
open import Once.Spec.Core.Derived using (cataᶜ; inᶜ)
open import Once.Spec.Core.Typing Σ S
open import Once.Spec.Core.Meaning Σ fmt S
open import Once.Spec.Effect Σ using (T∞; _>>=∞_; return∞; toT∞)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ; code; toL; fromL; foldM)
open import Once.Spec.Polynomial using (inS)
open import Once.Spec.Equivalence Σ using (Same)
open import Once.Spec.Metatheory using (SameDefs; SameEnv)
open import Once.Metatheory.Bisim Σ using (≈-sym; ≈-trans; idˡ)
open import Once.Metatheory.Coherence.Relation Σ using (Related; ≈-Relatedˡ; ≈-Relatedʳ; bindRel; returnRel; returnRel⁻; toObserved; fromObserved)
open import Once.Metatheory.Coherence.Layer Σ using (rel; runs; module Functor; module Fold)
open import Once.Metatheory.Coherence.Uniqueness Σ S using (ty-unique)
open import Once.Metatheory.Laws.Tools Σ u fmt S
open import Once.Metatheory.Laws.Views Σ u fmt S
open import Once.Metatheory.Laws.Compose Σ u fmt S using (valAt0; valAt▸; ≡→≈)
open import Once.Metatheory.Laws.MapCov Σ S using (cod≡)
open import Once.Metatheory.Laws.MapV Σ u fmt S using (module MapV)

module CataV {m : ℕ} {Δ : KCtx m} (δ : DefSem) (sd : SameDefs Σ fmt S δ) (σ : TySub m 0) (r : Respects Δ ∅ₖ σ) where
  module Fn = Functor σ r

  -- The Spec's fold of an algebra value.
  cataᵛ : ∀ (F : Fun m) (A : Ty m) → ⟦ (⟦ F ⟧F A ⇒[ mk-kind Many pure ] A) ⟨ σ ⟩ ⟧ᵛ → ⟦ (μ F ⇒[ mk-kind Many pure ] A) ⟨ σ ⟩ ⟧ᵛ
  cataᵛ F A g v = foldM pure (code (F ⟨ σ ⟩F)) (λ l → g (fromL σ F A l)) v

  cataSem : ∀ {n} {Γ : Ctx m n} {Ψ} (γ : Env σ Γ Ψ) (sγ : SameEnv Σ fmt S σ Γ Ψ γ) {F A Ψa π₀ alg}
              (d : Δ ⊩ Γ ⊢[ Ψa ] cataᶜ F pure alg ∷ μ F ⇒[ mk-kind Many pure ] A ! π₀) {γa}
          → Views.Res δ sd σ r γ sγ γa
          → ∀ {Ψf πf} (dalg : Δ ⊩ Γ ⊢[ Ψf ] alg ∷ ⟦ F ⟧F A ⇒[ mk-kind Many pure ] A ! πf) {ef} → Views.Res δ sd σ r γ sγ ef
          → Related (Same ((μ F ⇒[ mk-kind Many pure ] A) ⟨ σ ⟩)) (toT∞ π₀ (⟦ d ⟧ δ σ r γa))
              (toT∞ πf (⟦ dalg ⟧ δ σ r ef) >>=∞ λ g → return∞ (cataᵛ F A g))
  cataSem {Γ = Γ} γ sγ {F} {A} d {γa} ra dalg {ef} rf with Views.viewLet δ sd σ r γ sγ d ra
  ... | Views.letView {Ψ₂ = Ψb} de db {eb} rb (ee , re , eq) with ty-unique de dalg
  ...   | refl = W.~trans {TT} eq (bindRel (runs (W.fl de dalg re rf)) (λ {g} {g′} sg → LAM sg))
    where
      module W = Views δ sd σ r γ sγ
      module MV = MapV δ sd σ r A A
      TT = μ F ⇒[ mk-kind Many pure ] A
      AT = ⟦ F ⟧F A ⇒[ mk-kind Many pure ] A
      LAM : ∀ {g g′} → Same (AT ⟨ σ ⟩) g g′ → Related (Same (TT ⟨ σ ⟩)) (W.⟪ db ⟫▸ eb g) (return∞ (cataᵛ F A g′))
      LAM {g} {g′} sg with FunV.viewLam δ sd σ r {Γ = Γ ▸ AT} {Ψ = Many ∷ Ψb} (eb , g) sγ₁ db (Views.base δ sd σ r {Γ = Γ ▸ AT} {Ψ = Many ∷ Ψb} (eb , g) sγ₁)
        where sγ₁ = sameEnv▸ σ {Γ = Γ} {Ψ = Ψb} {A = AT} Many (W.sameEnvOf rb) (slotAgree σ {AT} Many Many (sameRefl (AT ⟨ σ ⟩) sg))
      ... | FunV.lamView {q′ = q′} {Ψ₀} le dt {e₀} (Views.res P₁ refl) eqT eqL with cod≡ {Δ = Δ} eqT
      ...   | refl with eqT
      ...     | refl = Views.~trans δ sd σ r {Γ = Γ ▸ AT} {Ψ = Many ∷ Ψb} (eb , g) sγ₁ {TT} eqL (returnRel SAME)
        where
          sγ₁ = sameEnv▸ σ {Γ = Γ} {Ψ = Ψb} {A = AT} Many (W.sameEnvOf rb) (slotAgree σ {AT} Many Many (sameRefl (AT ⟨ σ ⟩) sg))
          SAME : Same (TT ⟨ σ ⟩) (⟦ ⊢lam le dt ⟧ δ σ r e₀) (cataᵛ F A g′)
          SAME v v′ sv = toObserved
            (≈-Relatedˡ (≡→≈ (cong (toT∞ pure) (FunV.lamCall δ sd σ r {Γ = Γ ▸ AT} {Ψ = Many ∷ Ψb} (eb , g) sγ₁ le dt e₀ v))) BODY)
            where
              γ₂ = e₀ , slot q′ v
              sγ₂ = sameEnv▸ σ {Γ = Γ ▸ AT} {Ψ = Ψ₀} {A = μ F} q′
                      (Views.sameEnvOf δ sd σ r {Γ = Γ ▸ AT} {Ψ = Many ∷ Ψb} (eb , g) sγ₁ (Views.res P₁ refl))
                      (slotAgree σ {μ F} q′ q′ (sameRefl ((μ F) ⟨ σ ⟩) sv))
              Rg = MV.readsVar {Γ = Γ ▸ AT ▸ μ F} {Ψ = q′ ∷ Ψ₀} γ₂ sγ₂ (valAt▸ σ {Γ = Γ ▸ AT} {A = μ F} {q = q′} P₁ {γ = eb , g} {i = fz} {v = g′} (slot q′ v)
                                         (valAt0 σ {Γ = Γ} {A = AT} Many {γ = eb} sg))
              Rv = MV.readsVar {Γ = Γ ▸ AT ▸ μ F} {Ψ = q′ ∷ Ψ₀} γ₂ sγ₂ (valAt0 σ {Γ = Γ ▸ AT} {A = μ F} q′ {γ = e₀} sv)
              BODY : Related (Same (A ⟨ σ ⟩)) (toT∞ pure (⟦ dt ⟧ δ σ r γ₂)) (return∞ (cataᵛ F A g′ v′))
              BODY with MV.FoldR.viewFold γ₂ sγ₂ dt (Views.base δ sd σ r γ₂ sγ₂)
              ... | MV.FoldR.foldView wf da dv {ea} {et} ra′ rt′ eqF with MV.Reads.ty Rg da
              ...   | refl =
                Views.~trans δ sd σ r {Γ = Γ ▸ AT ▸ μ F} {Ψ = q′ ∷ Ψ₀} γ₂ sγ₂ {A} eqF
                  (≈-Relatedʳ (≈-sym (≈-trans (idˡ g′ _) (idˡ v′ _)))
                    (bindRel {g = λ g₀ → return∞ v′ >>=∞ λ w → return∞ (cataᵛ F A g₀ w)} (MV.Reads.rd Rg da ra′) (λ {g₀} {g₀′} sg₀ →
                      bindRel {g = λ w → return∞ (cataᵛ F A g₀′ w)} (MV.Reads.rd Rv dv rt′) (λ {w} {w′} sw →
                        returnRel (FOLD sg₀ sw)))))
                where
                  FOLD : ∀ {g₀ g₀′} → Same (AT ⟨ σ ⟩) g₀ g₀′ → ∀ {w w′} → w ≡ w′ → Same (A ⟨ σ ⟩) (cataᵛ F A g₀ w) (cataᵛ F A g₀′ w′)
                  FOLD {g₀} {g₀′} sg₀ {w} refl =
                    returnRel⁻ (runs (Fold.foldRel pure (code (F ⟨ σ ⟩F)) (A ⟨ σ ⟩) (λ l → g₀ (fromL σ F A l)) (λ l → g₀′ (fromL σ F A l))
                                        (λ p → rel (fromObserved (sg₀ _ _ (Fn.fromL-same wf A p)))) w))

  inSem : ∀ {n} {Γ : Ctx m n} {Ψ} (γ : Env σ Γ Ψ) (sγ : SameEnv Σ fmt S σ Γ Ψ γ) {F Ψa π₀}
            (d : Δ ⊩ Γ ⊢[ Ψa ] inᶜ {S = S} F ∷ ⟦ F ⟧F (μ F) ⇒[ mk-kind Many pure ] μ F ! π₀) {γa}
        → Views.Res δ sd σ r γ sγ γa
        → Related (Same ((⟦ F ⟧F (μ F) ⇒[ mk-kind Many pure ] μ F) ⟨ σ ⟩)) (toT∞ π₀ (⟦ d ⟧ δ σ r γa))
            (return∞ (λ l → inS (toL σ F (μ F) l)))
  inSem {Γ = Γ} γ sγ {F} d {γa} ra with FunV.viewLam δ sd σ r γ sγ d ra
  ... | FunV.lamView {q′ = q′} {Ψ₀} le dt {e₀} r₀ eqT eqL with cod≡ {Δ = Δ} eqT
  ...   | refl with eqT
  ...     | refl = Views.~trans δ sd σ r γ sγ {TT} eqL (returnRel SAME)
    where
      module W = Views δ sd σ r γ sγ
      module MV = MapV δ sd σ r (μ F) (μ F)
      L  = ⟦ F ⟧F (μ F)
      TT = L ⇒[ mk-kind Many pure ] μ F
      SAME : Same (TT ⟨ σ ⟩) (⟦ ⊢lam le dt ⟧ δ σ r e₀) (λ l → inS (toL σ F (μ F) l))
      SAME l l′ sl = toObserved (≈-Relatedˡ (≡→≈ (cong (toT∞ pure) (FunV.lamCall δ sd σ r γ sγ le dt e₀ l))) BODY)
        where
          γ₁ = e₀ , slot q′ l
          sγ₁ = sameEnv▸ σ {Γ = Γ} {Ψ = Ψ₀} {A = L} q′ (W.sameEnvOf r₀) (slotAgree σ {L} q′ q′ (sameRefl (L ⟨ σ ⟩) sl))
          Rl = MV.readsVar {Γ = Γ ▸ L} {Ψ = q′ ∷ Ψ₀} γ₁ sγ₁ (valAt0 σ {Γ = Γ} {A = L} q′ {γ = e₀} sl)
          BODY : Related (Same ((μ F) ⟨ σ ⟩)) (toT∞ pure (⟦ dt ⟧ δ σ r γ₁)) (return∞ (inS (toL σ F (μ F) l′)))
          BODY with MV.FoldR.viewRoll γ₁ sγ₁ dt (Views.base δ sd σ r γ₁ sγ₁)
          ... | MV.FoldR.rollView wf dv r₁ eqR =
            Views.~trans δ sd σ r {Γ = Γ ▸ L} {Ψ = q′ ∷ Ψ₀} γ₁ sγ₁ {μ F} eqR
              (≈-Relatedʳ (≈-sym (idˡ l′ _))
                (bindRel {g = λ x → return∞ (inS (toL σ F (μ F) x))} (MV.Reads.rd Rl dv r₁) (λ s → returnRel (Fn.roll-same wf s))))
