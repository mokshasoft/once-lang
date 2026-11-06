{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws.MapFun — a type is a functor in its 0th variable, on
-- the effect-free arrows (`Spec.Metatheory.Categorical.map-idᶜ`,
-- `map-composeᶜ`): `mapᶜ` means the semantic map (`Laws.MapTop`), and the
-- semantic map preserves identities and composites (`Laws.MapLaws`).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature; OneName)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Laws.MapFun (Σ : Signature) (u : OneName Σ) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

open import Data.Fin using () renaming (zero to fz)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Data.Product using (_,_)
open import Data.Sum using (inj₂)
open import Once.Spec.Grade using (Many; mk-kind; pure; _⊑π_; ⊑-pure)
open import Once.Spec.Type using (Ty; KCtx; _⟨_⟩; _⇒[_]_; at₀)
open import Once.Spec.Context using (Ctx)
open import Once.Spec.Core.Syntax
open import Once.Spec.Core.Derived using (idᶜ; mapᶜ; composeᶜ)
open import Once.Spec.Core.Typing Σ S
open import Once.Spec.Core.Meaning Σ fmt S
open import Once.Spec.Effect Σ using (return∞; toT∞; sub; _>>=∞_)
open import Once.Spec.Equivalence Σ using (Same)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ)
open import Once.Spec.Metatheory using (_≅_)
open import Once.Metatheory.Bisim Σ using (idˡ; ≈-trans; ≈-sym; ≈-bind; ≈-refl; assoc)
open import Once.Metatheory.Coherence.Relation Σ using (≈-Relatedˡ; ≈-Relatedʳ; returnRel; returnRel⁻; bindRel)
open import Once.Metatheory.Coherence.Layer Σ using (rel; runs)
open import Once.Metatheory.Laws.Tools Σ u fmt S
open import Once.Metatheory.Laws.Views Σ u fmt S
open import Once.Metatheory.Laws.Categorical.Tools Σ u fmt S using (zero⊑; toSameP; fromSameP; idD)
open import Once.Metatheory.Laws.MapSem Σ using (module MapAt; Occ; OccF; p-var; p-*ˡ; p-*ʳ; p-+ˡ; p-+ʳ; p-⇒ʳ; p-μ; p-ν; p-K; p-⊕ˡ; p-⊕ʳ; p-⊗ˡ; p-⊗ʳ)
open import Once.Metatheory.Laws.MapLaws Σ using (module MapId; module MapComp; module MapResp)
open import Once.Metatheory.Laws.Assoc Σ u fmt S using (compCong)
open import Once.Metatheory.Laws.Compose Σ u fmt S using (compᵛ)
open import Once.Metatheory.Laws.ComposeShape Σ u fmt S using (Shape; shape; compShape; ⊑pure′)
open import Once.Metatheory.Laws.ComposeG Σ u fmt S using (liftᵛ; callRel; module CompGV)
open import Once.Metatheory.Laws.MapCov Σ S using (dom≡; cod≡)
open import Once.Metatheory.Laws.MapTop Σ u fmt S using (module MapTopV)
open import Once.Metatheory.Laws.MapV Σ u fmt S using (module MapV)

module _ {m : ℕ} {Δ : KCtx m} where

  map-idᶜ : ∀ {n} {Γ : Ctx m n} {Ψ T A π₀}
            (d : Δ ⊩ Γ ⊢[ Ψ ] mapᶜ T A A (idᶜ A pure) ∷ T ⟨ at₀ A ⟩ ⇒[ mk-kind Many pure ] T ⟨ at₀ A ⟩ ! π₀)
            (d′ : Δ ⊩ Γ ⊢[ Ψ ] idᶜ (T ⟨ at₀ A ⟩) pure ∷ T ⟨ at₀ A ⟩ ⇒[ mk-kind Many pure ] T ⟨ at₀ A ⟩ ! π₀)
          → _≅_ Σ fmt S d d′
  map-idᶜ {Γ = Γ} {Ψ} {T} {A} {π₀} d d′ δ sd σ r γ sγ =
    sameM {TT ⟨ σ ⟩} {π₀}
      (rel (~trans {TT} (MT.mapSem γ sγ T d base (idD A pure) r₀ Φ HΦ)
             (≈-Relatedˡ (idˡ idv _) (~trans {TT} (returnRel SAME) (~sym {TT} (runs (fl d′ (idD (T ⟨ at₀ A ⟩) pure) base r₀)))))))
    where
      open Views δ sd σ r γ sγ
      module MT = MapTopV δ sd σ r A A
      module MV = MapV δ sd σ r A A
      open MapAt Δ σ A A using (mapS; Fn)
      TT = T ⟨ at₀ A ⟩ ⇒[ mk-kind Many pure ] T ⟨ at₀ A ⟩
      r₀ = resR base (zero⊑ Ψ)
      idv = ⟦ idD {Γ = Γ} A pure ⟧ δ σ r (restrict σ (zero⊑ Ψ) γ)
      Φ : ⟦ (A ⇒[ mk-kind Many pure ] A) ⟨ σ ⟩ ⟧ᵛ → Fn T
      Φ g o a = g a
      HΦ : ∀ {hv hv′} → Same ((A ⇒[ mk-kind Many pure ] A) ⟨ σ ⟩) hv hv′ → MV.HCall T (Φ hv′) (A ⇒[ mk-kind Many pure ] A) hv
      HΦ sh o refl a a′ sa = returnRel (fromSameP σ {X = A} {Y = A} sh sa)
      SAME : Same (TT ⟨ σ ⟩) (λ x → mapS T (MT.covD T d) (Φ idv) x)
                             (⟦ idD {Γ = Γ} (T ⟨ at₀ A ⟩) pure ⟧ δ σ r (restrict σ (zero⊑ Ψ) γ))
      SAME = toSameP σ {X = T ⟨ at₀ A ⟩} {Y = T ⟨ at₀ A ⟩}
               (λ {x} {x′} sx → MapId.mid σ r A T (MT.covD T d) {φ = Φ idv} (λ o a a′ sa → sa) {x} {x′} sx)

  private
    -- Calls of the same arrows on the same argument, read at the types the map was written at.
    callComp : ∀ {σ} {B C B₁ C₁ : Ty m} (e₃ : C₁ ≡ C) (e₂B : B₁ ≡ B) (e₂C : C₁ ≡ C) (e₁ : B₁ ≡ B) {X : Ty m} {qf qg}
                 (lf lg : pure ⊑π pure) {fv fv′ : ⟦ (B₁ ⇒[ mk-kind qf pure ] C₁) ⟨ σ ⟩ ⟧ᵛ} {gv gv′ : ⟦ (X ⇒[ mk-kind qg pure ] B₁) ⟨ σ ⟩ ⟧ᵛ}
             → Same _ fv fv′ → Same _ gv gv′ → ∀ {a a′} → Same (X ⟨ σ ⟩) a a′
             → Same (C ⟨ σ ⟩) (subst (λ Z → ⟦ Z ⟨ σ ⟩ ⟧ᵛ) e₃ (sub lf (callᵛ qf fv (sub lg (callᵛ qg gv a)))))
                              (subst (λ Z → ⟦ Z ⟨ σ ⟩ ⟧ᵛ) e₂C (callᵛ qf fv′ (subst (λ Z → ⟦ Z ⟨ σ ⟩ ⟧ᵛ) (sym e₂B)
                                 (subst (λ Z → ⟦ Z ⟨ σ ⟩ ⟧ᵛ) e₁ (callᵛ qg gv′ a′)))))
    callComp refl refl refl refl {qf = qf} {qg} ⊑-pure ⊑-pure sf sg sa = returnRel⁻ (callRel qf sf (returnRel⁻ (callRel qg sg sa)))

    subPure : ∀ {X : Set} (p : pure ⊑π pure) (x : X) → sub p x ≡ x
    subPure ⊑-pure x = refl

  map-composeᶜ : ∀ {n} {Γ : Ctx m n} {Ψ T A B C π₀ f g}
                 (d : Δ ⊩ Γ ⊢[ Ψ ] mapᶜ T A C (composeᶜ A pure f g) ∷ T ⟨ at₀ A ⟩ ⇒[ mk-kind Many pure ] T ⟨ at₀ C ⟩ ! π₀)
                 (d′ : Δ ⊩ Γ ⊢[ Ψ ] composeᶜ (T ⟨ at₀ A ⟩) pure (mapᶜ T B C f) (mapᶜ T A B g)
                                    ∷ T ⟨ at₀ A ⟩ ⇒[ mk-kind Many pure ] T ⟨ at₀ C ⟩ ! π₀)
               → _≅_ Σ fmt S d d′
  map-composeᶜ {Γ = Γ} {Ψ} {T} {A} {B} {C} {π₀} {f} {g} d d′ δ sd σ r γ sγ =
    sameM {TT ⟨ σ ⟩} {π₀} (rel (GO (viewLet d base) (compShape d′) (AV.armsLL (inj₂ refl) d′)))
    where
      open Views δ sd σ r γ sγ
      module AV = ArmsV δ sd σ r γ sγ
      module G  = CompGV δ sd σ r
      module AC = MapTopV δ sd σ r A C
      module BC = MapTopV δ sd σ r B C
      module AB = MapTopV δ sd σ r A B
      TT = T ⟨ at₀ A ⟩ ⇒[ mk-kind Many pure ] T ⟨ at₀ C ⟩

      GO : LetView d γ → Shape (T ⟨ at₀ A ⟩) pure TT (mapᶜ T B C f) (mapᶜ T A B g) → AV.Arms d′ (mapᶜ T B C f) (mapᶜ T A B g)
         → _~_ {TT} (⟪ d ⟫ γ) (⟪ d′ ⟫ γ)
      GO (letView de db rb (ee , re , eqL)) (shape eT′ tyF′ tyG′ lf′ lg′ zp′) (AV.arms dmf dmg Pmf Pmg)
        with compShape de | AV.armsLL (inj₂ refl) de
      ... | shape {B = B₁} {C = C₁} {qf} {qg} eT tyF tyG lf lg zp | AV.arms df dg Pf Pg
        with eT | tyF df | tyG dg | eT′ | tyF′ dmf | tyG′ dmg | ⊑pure′ lf | ⊑pure′ lg
      ... | refl | refl | refl | refl | refl | refl | refl | refl with BC.mapTy T dmf | AB.mapTy T dmg
      ... | _ , refl | _ , refl = ~trans {TT} LHS (~trans {TT} MID (~sym {TT} RHS))
        where
          rf = resR re Pf
          rg = resR re Pg
          rmf = resR base Pmf
          rmg = resR base Pmg
          TA = T ⟨ at₀ A ⟩
          TC = T ⟨ at₀ C ⟩
          eC₃ : ∀ o → C₁ ≡ C
          eC₃ o with AC.occD T d de o
          ... | _ , _ , e = cod≡ {Δ = Δ} e
          eB₂ : ∀ o → B₁ ≡ B
          eB₂ o with BC.occD T dmf df o
          ... | _ , _ , e = dom≡ {Δ = Δ} e
          eC₂ : ∀ o → C₁ ≡ C
          eC₂ o with BC.occD T dmf df o
          ... | _ , _ , e = cod≡ {Δ = Δ} e
          eB₁ : ∀ o → B₁ ≡ B
          eB₁ o with AB.occD T dmg dg o
          ... | _ , _ , e = cod≡ {Δ = Δ} e
          Φ₃ = AC.Φcall T {X = A} {Y = C₁} {q = Many} (λ _ → refl) eC₃
          Φ₂ = BC.Φcall T {X = B₁} {Y = C₁} {q = qf} eB₂ eC₂
          Φ₁ = AB.Φcall T {X = A} {Y = B₁} {q = qg} (λ _ → refl) eB₁
          c₃ = AC.covD T d
          c₂ = BC.covD T dmf
          c₁ = AB.covD T dmg
          CL₃ : ⟦ (A ⇒[ mk-kind Many pure ] C₁) ⟨ σ ⟩ ⟧ᵛ → ⟦ TT ⟨ σ ⟩ ⟧ᵛ
          CL₃ hv x = MapAt.mapS Δ σ A C T c₃ (Φ₃ hv) x
          CL₂ : ⟦ (B₁ ⇒[ mk-kind qf pure ] C₁) ⟨ σ ⟩ ⟧ᵛ → ⟦ (T ⟨ at₀ B ⟩ ⇒[ mk-kind Many pure ] TC) ⟨ σ ⟩ ⟧ᵛ
          CL₂ fv y = MapAt.mapS Δ σ B C T c₂ (Φ₂ fv) y
          CL₁ : ⟦ (A ⇒[ mk-kind qg pure ] B₁) ⟨ σ ⟩ ⟧ᵛ → ⟦ (TA ⇒[ mk-kind Many pure ] T ⟨ at₀ B ⟩) ⟨ σ ⟩ ⟧ᵛ
          CL₁ gv x = MapAt.mapS Δ σ A B T c₁ (Φ₁ gv) x
          K₃ = λ fv gv → compᵛ pure (liftᵛ qf lf fv) (liftᵛ qg lg gv)
          K′ = λ u w → compᵛ pure (liftᵛ Many lf′ u) (liftᵛ Many lg′ w)

          LHS : _~_ {TT} (⟪ d ⟫ γ) (⟪ df ⟫ _ >>=∞ λ fv → ⟪ dg ⟫ _ >>=∞ λ gv → return∞ (CL₃ (K₃ fv gv)))
          LHS = ~trans {TT} (AC.mapSem γ sγ T d base de re Φ₃ (AC.HΦcall T {X = A} {Y = C₁} {q = Many} (λ _ → refl) eC₃))
            (≈-Relatedʳ (≈-sym (≈-trans (assoc _ _ _) (≈-bind (≈-refl _) (λ fv → ≈-trans (assoc _ _ _) (≈-bind (≈-refl _) (λ gv → idˡ _ _))))))
              (bindRel {g = λ hv′ → return∞ (CL₃ hv′)} (G.compSemG γ sγ de re df rf dg rg lf lg zp)
                (λ {hv} {hv′} sh → returnRel (toSameP σ {X = TA} {Y = TC}
                   (λ sx → MapResp.resp σ r A C T c₃ c₃ (AC.ΦcallResp T {X = A} {Y = C₁} {q = Many} (λ _ → refl) eC₃ sh) sx)))))

          RHS : _~_ {TT} (⟪ d′ ⟫ γ) (⟪ df ⟫ _ >>=∞ λ fv → ⟪ dg ⟫ _ >>=∞ λ gv → return∞ (K′ (CL₂ fv) (CL₁ gv)))
          RHS = ~trans {TT} (G.compSemG γ sγ d′ base dmf rmf dmg rmg lf′ lg′ zp′)
            (≈-Relatedʳ (≈-sym (≈-trans (assoc _ _ _) (≈-bind (≈-refl _) (λ fv → ≈-trans (idˡ _ _)
                          (≈-trans (assoc _ _ _) (≈-bind (≈-refl _) (λ gv → idˡ _ _)))))))
              (bindRel {g = λ u → (⟪ dg ⟫ _ >>=∞ λ gv → return∞ (CL₁ gv)) >>=∞ λ w → return∞ (K′ u w)}
                (BC.mapSem γ sγ T dmf rmf df rf Φ₂ (BC.HΦcall T {X = B₁} {Y = C₁} {q = qf} eB₂ eC₂)) (λ {u} {u′} su →
                  bindRel {g = λ w → return∞ (K′ u′ w)} (AB.mapSem γ sγ T dmg rmg dg rg Φ₁ (AB.HΦcall T {X = A} {Y = B₁} {q = qg} (λ _ → refl) eB₁))
                    (λ sw → returnRel (compCong pure {Many} {Many} lf′ lf′ lg′ lg′ su sw)))))

          MID : _~_ {TT} (⟪ df ⟫ _ >>=∞ λ fv → ⟪ dg ⟫ _ >>=∞ λ gv → return∞ (CL₃ (K₃ fv gv)))
                         (⟪ df ⟫ _ >>=∞ λ fv → ⟪ dg ⟫ _ >>=∞ λ gv → return∞ (K′ (CL₂ fv) (CL₁ gv)))
          MID = bindRel (runs (fl df df rf rf)) (λ {fv} {fv′} sf → bindRel (runs (fl dg dg rg rg)) (λ {gv} {gv′} sg →
                  returnRel (toSameP σ {X = TA} {Y = TC} (λ {x} {x′} sx →
                    subst (λ z → Same (TC ⟨ σ ⟩) (CL₃ (K₃ fv gv) x) z) (sym (K′eq fv′ gv′ x′))
                      (MapComp.comp σ r A B C T c₃ c₂ c₁ (λ o a a′ sa → callComp (eC₃ o) (eB₂ o) (eC₂ o) (eB₁ o) {X = A} {qf = qf} {qg = qg} lf lg sf sg sa) sx)))))
            where
              K′eq : ∀ fv′ gv′ x′ → K′ (CL₂ fv′) (CL₁ gv′) x′ ≡ CL₂ fv′ (CL₁ gv′ x′)
              K′eq fv′ gv′ x′ rewrite subPure lg′ (CL₁ gv′ x′) | subPure lf′ (CL₂ fv′ (CL₁ gv′ x′)) = refl
