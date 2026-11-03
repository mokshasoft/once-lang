{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws.AnaSem — what `anaᶜ F A pure c` and `outᶜ F` mean,
-- in any derivation: `anaᶜ` is the closure that unfolds by `c`'s value (an
-- effect-free `c` reads as one value, `readsPure`); `outᶜ` the closure that
-- forces a layer. Forcing an unfold is mapping the unfold over its
-- coalgebra's layer (`mapPRel`).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature; OneName)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Laws.AnaSem (Σ : Signature) (u : OneName Σ) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

open import Data.Fin using () renaming (zero to fz; suc to fs)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Once.Spec.Grade using (Many; mk-kind; pure; pureᶠ)
open import Once.Spec.Type using (Ty; Fun; KCtx; WFFun; TySub; Respects; ∅ₖ; _⟨_⟩; _⟨_⟩F; _⇒[_]_; ν; ⟦_⟧F)
open import Once.Spec.Context using (Ctx; _▸_; _∷_)
open import Once.Spec.Core.Syntax
open import Once.Spec.Core.Derived using (anaᶜ; outᶜ)
open import Once.Spec.Core.Typing Σ S
open import Once.Spec.Core.Meaning Σ fmt S
open import Once.Spec.Effect Σ using (T∞; _>>=∞_; return∞; toT∞; LayerEq; νM; ana; anaP; mapP)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ; code; toL; fromL)
open import Once.Spec.Polynomial using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF; sfmap)
open import Once.Spec.Equivalence Σ using (Same)
open import Once.Spec.Metatheory using (SameDefs; SameEnv; Pure)
open import Once.Metatheory.Bisim Σ using (≈-sym; ≈-trans; idˡ)
open import Once.Metatheory.Coherence.Relation Σ using (Related; ≈-Relatedˡ; ≈-Relatedʳ; bindRel; returnRel; returnRel⁻; toObserved; fromObserved)
open import Once.Metatheory.Coherence.Layer Σ using (rel; runs; module Functor; module Ana; relatedFmap; outRel; LayerEq-∀)
open import Once.Metatheory.Coherence.Uniqueness Σ S using (ty-unique)
open import Once.Metatheory.Laws.Tools Σ u fmt S
open import Once.Metatheory.Laws.Views Σ u fmt S
open import Once.Metatheory.Laws.Compose Σ u fmt S using (valAt0; ≡→≈)
open import Once.Metatheory.Laws.MapCov Σ S using (cod≡)
open import Once.Metatheory.Laws.MapV Σ u fmt S using (module MapV)

module AnaV {m : ℕ} {Δ : KCtx m} (δ : DefSem) (sd : SameDefs Σ fmt S δ) (σ : TySub m 0) (r : Respects Δ ∅ₖ σ) where
  module Fn = Functor σ r

  -- The Spec's unfold of a coalgebra value.
  anaᵛ : ∀ (F : Fun m) (A : Ty m) → ⟦ (A ⇒[ mk-kind Many pure ] ⟦ F ⟧F A) ⟨ σ ⟩ ⟧ᵛ → ⟦ (A ⇒[ mk-kind Many pure ] ν F pureᶠ) ⟨ σ ⟩ ⟧ᵛ
  anaᵛ F A g a = ana pureᶠ (code (F ⟨ σ ⟩F)) (λ y → toL σ F A (g y)) a

  -- Forcing a layer.
  outᵛ : ∀ (F : Fun m) → ⟦ (ν F pureᶠ ⇒[ mk-kind Many pure ] ⟦ F ⟧F (ν F pureᶠ)) ⟨ σ ⟩ ⟧ᵛ
  outᵛ F v = fromL σ F (ν F pureᶠ) (νM.outν v)

  -- The unfolds of the same coalgebras: the same streams.
  anaRelP : ∀ {F : Fun m} {A : Ty m} → WFFun Δ F → ∀ {g g′}
          → Same ((A ⇒[ mk-kind Many pure ] ⟦ F ⟧F A) ⟨ σ ⟩) g g′
          → ∀ {a a′} → Same (A ⟨ σ ⟩) a a′ → Same ((ν F pureᶠ) ⟨ σ ⟩) (anaᵛ F A g a) (anaᵛ F A g′ a′)
  anaRelP {F} {A} wf {g} {g′} sg sa n =
    Ana.anaRel pureᶠ (code (F ⟨ σ ⟩F)) (A ⟨ σ ⟩) (λ y → toL σ F A (g y)) (λ y → toL σ F A (g′ y))
      (λ s → returnRel (Fn.toL-same wf A (returnRel⁻ (fromObserved (sg _ _ s))))) n sa

  anaResp : ∀ {F : Fun m} {A : Ty m} → WFFun Δ F → ∀ {g g′}
          → Same ((A ⇒[ mk-kind Many pure ] ⟦ F ⟧F A) ⟨ σ ⟩) g g′
          → Same ((A ⇒[ mk-kind Many pure ] ν F pureᶠ) ⟨ σ ⟩) (anaᵛ F A g) (anaᵛ F A g′)
  anaResp wf sg a a′ sa = toObserved (returnRel (anaRelP wf sg sa))

  -- Forcing an unfold maps the unfold over the coalgebra's layer.
  mapPRel : ∀ {F : Fun m} {A : Ty m} → WFFun Δ F → ∀ {g g′}
          → Same ((A ⇒[ mk-kind Many pure ] ⟦ F ⟧F A) ⟨ σ ⟩) g g′
          → ∀ H {l l′} → LayerEq H (Same (A ⟨ σ ⟩)) l l′
          → LayerEq H (Same ((ν F pureᶠ) ⟨ σ ⟩)) (mapP (code (F ⟨ σ ⟩F)) H (λ y → toL σ F A (g y)) l) (sfmap H (anaᵛ F A g′) l′)
  mapPRel wf sg (SK B) p = p
  mapPRel wf sg SId p = anaRelP wf sg p
  mapPRel wf sg (H₁ S⊕ H₂) {inj₁ x} {inj₁ y} p = mapPRel wf sg H₁ p
  mapPRel wf sg (H₁ S⊕ H₂) {inj₂ x} {inj₂ y} p = mapPRel wf sg H₂ p
  mapPRel wf sg (H₁ S⊗ H₂) {x , x′} {y , y′} (p , q) = mapPRel wf sg H₁ p , mapPRel wf sg H₂ q

  module _ {n} {Γ : Ctx m n} {Ψ} (γ : Env σ Γ Ψ) (sγ : SameEnv Σ fmt S σ Γ Ψ γ) where
    private
      module W = Views δ sd σ r γ sγ
      open ProdV δ sd σ r γ sγ using (pureRet)

    -- An effect-free term reads as one value, wherever it is derived.
    readsPure : ∀ (X Y : Ty m) {A t Ψp} (dp : Δ ⊩ Γ ⊢[ Ψp ] t ∷ A ! pure) {Ψ₀ π₀} (d₀ : Δ ⊩ Γ ⊢[ Ψ₀ ] t ∷ A ! π₀) {γ₀} (r₀ : W.Res γ₀)
              → MapV.Reads δ sd σ r X Y γ sγ t A (⟦ transfer dp d₀ ⟧ δ σ r γ₀)
    readsPure X Y {A} dp d₀ {γ₀} r₀ = MapV.reads (λ d → ty-unique d dp)
      (λ dt {γa} ra → W.~trans {A} (pureRet dt dp ra) (returnRel (returnRel⁻ (runs (W.fl (transfer dp dt) (transfer dp d₀) ra r₀)))))

    anaSem : ∀ {F A Ψa π₀ c} (d : Δ ⊩ Γ ⊢[ Ψa ] anaᶜ F A pure c ∷ A ⇒[ mk-kind Many pure ] ν F pureᶠ ! π₀) {γa} → W.Res γa
           → ∀ {g} → MapV.Reads δ sd σ r A A γ sγ c (A ⇒[ mk-kind Many pure ] ⟦ F ⟧F A) g
           → Related (Same ((A ⇒[ mk-kind Many pure ] ν F pureᶠ) ⟨ σ ⟩)) (toT∞ π₀ (⟦ d ⟧ δ σ r γa)) (return∞ (anaᵛ F A g))
    anaSem {F} {A} d ra {g} Rc with FunV.viewLam δ sd σ r γ sγ d ra
    ... | FunV.lamView {q′ = q′} {Ψ₀} le dt {e₀} r₀ eqT eqL with cod≡ {Δ = Δ} eqT
    ...   | refl with eqT
    ...     | refl = W.~trans {AN} eqL (returnRel SAME)
      where
        module MV = MapV δ sd σ r A A
        AN = A ⇒[ mk-kind Many pure ] ν F pureᶠ
        SAME : Same (AN ⟨ σ ⟩) (⟦ ⊢lam le dt ⟧ δ σ r e₀) (anaᵛ F A g)
        SAME a a′ sa = toObserved (≈-Relatedˡ (≡→≈ (cong (toT∞ pure) (FunV.lamCall δ sd σ r γ sγ le dt e₀ a))) BODY)
          where
            γ₁ = e₀ , slot q′ a
            sγ₁ = sameEnv▸ σ {Γ = Γ} {Ψ = Ψ₀} {A = A} q′ (W.sameEnvOf r₀) (slotAgree σ {A} q′ q′ (sameRefl (A ⟨ σ ⟩) sa))
            Ra = MV.readsVar {Γ = Γ ▸ A} {Ψ = q′ ∷ Ψ₀} γ₁ sγ₁ (valAt0 σ {Γ = Γ} {A = A} q′ {γ = e₀} sa)
            Rc′ = MV.readsWk γ sγ r₀ (slot q′ a) sγ₁ Rc
            BODY : Related (Same ((ν F pureᶠ) ⟨ σ ⟩)) (toT∞ pure (⟦ dt ⟧ δ σ r γ₁)) (return∞ (anaᵛ F A g a′))
            BODY with MV.FoldR.viewUnfold γ₁ sγ₁ dt (Views.base δ sd σ r γ₁ sγ₁)
            ... | MV.FoldR.unfoldView wf dc dv {ec} {et} rc rt eqU with MV.Reads.ty Rc′ dc
            ...   | refl =
              Views.~trans δ sd σ r {Γ = Γ ▸ A} {Ψ = q′ ∷ Ψ₀} γ₁ sγ₁ {ν F pureᶠ} eqU
                (≈-Relatedʳ (≈-sym (≈-trans (idˡ g _) (idˡ a′ _)))
                  (bindRel {g = λ g₀ → return∞ a′ >>=∞ λ w → return∞ (anaᵛ F A g₀ w)} (MV.Reads.rd Rc′ dc rc) (λ {g₀} {g₀′} sg₀ →
                    bindRel {g = λ w → return∞ (anaᵛ F A g₀′ w)} (MV.Reads.rd Ra dv rt) (λ sw → returnRel (anaRelP wf sg₀ sw)))))

    outSem : ∀ {F Ψa π₀} (d : Δ ⊩ Γ ⊢[ Ψa ] outᶜ {S = S} F ∷ ν F pureᶠ ⇒[ mk-kind Many pure ] ⟦ F ⟧F (ν F pureᶠ) ! π₀) {γa}
           → W.Res γa
           → Related (Same ((ν F pureᶠ ⇒[ mk-kind Many pure ] ⟦ F ⟧F (ν F pureᶠ)) ⟨ σ ⟩)) (toT∞ π₀ (⟦ d ⟧ δ σ r γa)) (return∞ (outᵛ F))
    outSem {F} d ra with FunV.viewLam δ sd σ r γ sγ d ra
    ... | FunV.lamView {q′ = q′} {Ψ₀} le dt {e₀} r₀ eqT eqL with cod≡ {Δ = Δ} eqT
    ...   | refl with eqT
    ...     | refl = W.~trans {OT} eqL (returnRel SAME)
      where
        module MV = MapV δ sd σ r (ν F pureᶠ) (ν F pureᶠ)
        N  = ν F pureᶠ
        L  = ⟦ F ⟧F N
        OT = N ⇒[ mk-kind Many pure ] L
        G  = code (F ⟨ σ ⟩F)
        SAME : Same (OT ⟨ σ ⟩) (⟦ ⊢lam le dt ⟧ δ σ r e₀) (outᵛ F)
        SAME v v′ sv = toObserved (≈-Relatedˡ (≡→≈ (cong (toT∞ pure) (FunV.lamCall δ sd σ r γ sγ le dt e₀ v))) BODY)
          where
            γ₁ = e₀ , slot q′ v
            sγ₁ = sameEnv▸ σ {Γ = Γ} {Ψ = Ψ₀} {A = N} q′ (W.sameEnvOf r₀) (slotAgree σ {N} q′ q′ (sameRefl (N ⟨ σ ⟩) sv))
            Rv = MV.readsVar {Γ = Γ ▸ N} {Ψ = q′ ∷ Ψ₀} γ₁ sγ₁ (valAt0 σ {Γ = Γ} {A = N} q′ {γ = e₀} sv)
            BODY : Related (Same (L ⟨ σ ⟩)) (toT∞ pure (⟦ dt ⟧ δ σ r γ₁)) (return∞ (outᵛ F v′))
            BODY with MV.FoldR.viewOut γ₁ sγ₁ dt (Views.base δ sd σ r γ₁ sγ₁)
            ... | MV.FoldR.outView wfA dv r₁ eqX eqO with MV.Reads.ty Rv dv
            ...   | refl with eqX
            ...     | refl =
              Views.~trans δ sd σ r {Γ = Γ ▸ N} {Ψ = q′ ∷ Ψ₀} γ₁ sγ₁ {L} eqO
                (≈-Relatedʳ (≈-sym (idˡ v′ _))
                  (bindRel {g = λ w′ → return∞ (outᵛ F w′)} (MV.Reads.rd Rv dv r₁) (λ {w} {w′} sw →
                    ≈-Relatedʳ (≈-sym (idˡ (νM.outν w′) _))
                      (relatedFmap (outRel pureᶠ G sw) (λ p → Fn.fromL-same wfA N (LayerEq-∀ G p))))))
