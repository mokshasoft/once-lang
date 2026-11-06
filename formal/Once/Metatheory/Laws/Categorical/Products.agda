{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws.Categorical.Products — the product and exponential laws (`fst-pairᶜ`, `snd-pairᶜ`,
-- `pair-ηᶜ`, `curry-βᶜ`, `curry-ηᶜ`), as in `Laws.Categorical`.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature; OneName)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Laws.Categorical.Products (Σ : Signature) (u : OneName Σ) (fmt : TargetNum) {s : ℕ} (S : Defs s) where


open import Data.Fin using (zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Once.Spec.Grade using (Quantity; Zero; One; Many; mk-kind; Purity; pure; 0≤q; 1≤ω)
open import Once.Spec.Type using (Ty; KCtx; TySub; _⟨_⟩; _⇒[_]_)
open import Once.Spec.Context using (Ctx; ∅; _▸_; _∷_; []; Usage; zeroUsage; _⊑ᵘ_; _⊑∷_; _+ᵘ_; _*ᵘ_)
open import Once.Spec.Core.Syntax
open import Once.Spec.Core.Derived using (idᶜ; composeᶜ)
open import Once.Spec.Core.Typing Σ S
open import Once.Spec.Core.Meaning Σ fmt S
open import Once.Spec.Effect Σ using (M; bind; sub; T∞; _>>=∞_; return∞; _≈_; toT∞)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ)
open import Once.Spec.Equivalence Σ using (Same; SameM)
open import Once.Spec.Metatheory using (_≅_)
open import Once.Metatheory.Erase Σ using (toT∞-bind; toT∞-sub)
open import Once.Metatheory.Bisim Σ using (≈-refl; ≈-sym; ≈-trans; ≈-bind; idˡ; idʳ; assoc)
open import Once.Metatheory.Coherence.Relation Σ using (Related; ≈-Relatedˡ; ≈-Relatedʳ; bindRel; returnRel; returnRel⁻; toObserved; fromObserved)
open import Once.Metatheory.Coherence.Layer Σ using (rel; runs; appMany; relPure⁻)
open import Once.Metatheory.Coherence.Uniqueness Σ S using (ty-unique)
open import Once.Metatheory.Laws.Tools Σ u fmt S
open import Once.Metatheory.Laws.Views Σ u fmt S
open import Once.Metatheory.Laws.Strengthen Σ S using (pure⊑)
open import Once.Metatheory.Laws.Compose Σ u fmt S using (compᵛ; module CompV)
open import Once.Metatheory.Laws.Combinators Σ u fmt S using (pairᵛ; module CombV)
open import Once.Metatheory.Laws.Canon Σ S using (terminalD; initialD; inlD; inrD; fstD′; sndD′; applyD; composeD; pairD; curryD; caseD)
open import Once.Spec.Core.Derived using (terminalᶜ; initialᶜ; inlᶜ; inrᶜ; fstᶜ; sndᶜ; applyᶜ; pairᶜ; caseᶜ; curryᶜ)
open import Once.Spec.Type using (Unit; Void; _*_; _+_)
open import Once.Spec.Metatheory using (Pure)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Once.Metatheory.Laws.Categorical.Tools Σ u fmt S

module _ {m : ℕ} {Δ : KCtx m} where

  fst-pairᶜ : ∀ {n} {Γ : Ctx m n} {Ψ A B C π₀ f g}
       → Pure Σ fmt S Δ Γ g (C ⇒[ mk-kind Many pure ] B)
       → (d : Δ ⊩ Γ ⊢[ Ψ ] composeᶜ C pure (fstᶜ A B pure) (pairᶜ C pure f g) ∷ C ⇒[ mk-kind Many pure ] A ! π₀)
         (d′ : Δ ⊩ Γ ⊢[ Ψ ] f ∷ C ⇒[ mk-kind Many pure ] A ! π₀) → _≅_ Σ fmt S d d′
  fst-pairᶜ {Γ = Γ} {Ψ} {A} {B} {C} {π₀} {f} {g} (_ , pp) d d′ δ sd σ r γ sγ = goA (AV.armsLL (inj₂ refl) d)
    where
      open Views δ sd σ r γ sγ
      open ProdV δ sd σ r γ sγ using (pureRet)
      module AV = ArmsV δ sd σ r γ sγ
      T = C ⇒[ mk-kind Many pure ] A
      GOAL = SameM π₀ (T ⟨ σ ⟩) (⟦ d ⟧ δ σ r γ) (⟦ d′ ⟧ δ σ r γ)
      r₀ = resR base (zero⊑ Ψ)
      projv = ⟦ fstD′ {Γ = Γ} A B pure ⟧ δ σ r (restrict σ (zero⊑ Ψ) γ)
      goA : AV.Arms d (fstᶜ A B pure) (pairᶜ C pure f g) → GOAL
      goA (AV.arms dfst dp Pfst Pp) = goB (AV.armsLL (inj₁ refl) dp)
        where
          goB : AV.Arms dp f g → GOAL
          goB (AV.arms df dg Pf Pg) with ty-unique dg pp | ty-unique df d′
          ... | refl | refl with ty-unique dp (pairD df dg)
          ... | refl =
            sameM {T ⟨ σ ⟩} {π₀}
              (rel (~trans {T} (CompV.compSem δ sd σ r γ sγ d base (fstD′ A B pure) r₀ dp rp)
                     (≈-Relatedˡ (idˡ projv _)
                       (~trans {T} (bindRel (CombV.pairSem δ sd σ r γ sγ dp rp df rf dg rg)
                                      (λ spv → returnRel (λ c c′ sc → toObserved (returnRel (PROJ (spv c c′ sc))))))
                         (≈-Relatedˡ (≈-trans (assoc _ _ _) (≈-bind (≈-refl _) λ fv → ≈-trans (assoc _ _ _) (≈-bind (≈-refl _) λ gv → idˡ _ _)))
                           (FIN))))))
            where
              rp = resR base Pp
              rf = resR rp Pf
              rg = resR rp Pg
              PROJ : ∀ {p p′} → SameM pure ((A * B) ⟨ σ ⟩) p p′ → Same (A ⟨ σ ⟩) (proj₁ p) (proj₁ p′)
              PROJ sp = proj₁ (returnRel⁻ (fromObserved sp))
              FIN = ≈-Relatedʳ (≈-sym (idʳ (⟪ d′ ⟫ γ)))
                             (bindRel (runs (fl df d′ rf base)) (λ {fv} {fv′} sf →
                               ≈-Relatedʳ (≈-sym (idˡ (⟦ transfer pp dg ⟧ δ σ r (restrict σ Pg (restrict σ Pp γ))) (λ _ → return∞ fv′)))
                                 (bindRel (pureRet dg pp rg) (λ _ → returnRel (λ c c′ sc → sf c c′ sc)))))

  snd-pairᶜ : ∀ {n} {Γ : Ctx m n} {Ψ A B C π₀ f g}
       → Pure Σ fmt S Δ Γ f (C ⇒[ mk-kind Many pure ] A)
       → (d : Δ ⊩ Γ ⊢[ Ψ ] composeᶜ C pure (sndᶜ A B pure) (pairᶜ C pure f g) ∷ C ⇒[ mk-kind Many pure ] B ! π₀)
         (d′ : Δ ⊩ Γ ⊢[ Ψ ] g ∷ C ⇒[ mk-kind Many pure ] B ! π₀) → _≅_ Σ fmt S d d′
  snd-pairᶜ {Γ = Γ} {Ψ} {A} {B} {C} {π₀} {f} {g} (_ , pp) d d′ δ sd σ r γ sγ = goA (AV.armsLL (inj₂ refl) d)
    where
      open Views δ sd σ r γ sγ
      open ProdV δ sd σ r γ sγ using (pureRet)
      module AV = ArmsV δ sd σ r γ sγ
      T = C ⇒[ mk-kind Many pure ] B
      GOAL = SameM π₀ (T ⟨ σ ⟩) (⟦ d ⟧ δ σ r γ) (⟦ d′ ⟧ δ σ r γ)
      r₀ = resR base (zero⊑ Ψ)
      projv = ⟦ sndD′ {Γ = Γ} A B pure ⟧ δ σ r (restrict σ (zero⊑ Ψ) γ)
      goA : AV.Arms d (sndᶜ A B pure) (pairᶜ C pure f g) → GOAL
      goA (AV.arms dfst dp Pfst Pp) = goB (AV.armsLL (inj₁ refl) dp)
        where
          goB : AV.Arms dp f g → GOAL
          goB (AV.arms df dg Pf Pg) with ty-unique df pp | ty-unique dg d′
          ... | refl | refl with ty-unique dp (pairD df dg)
          ... | refl =
            sameM {T ⟨ σ ⟩} {π₀}
              (rel (~trans {T} (CompV.compSem δ sd σ r γ sγ d base (sndD′ A B pure) r₀ dp rp)
                     (≈-Relatedˡ (idˡ projv _)
                       (~trans {T} (bindRel (CombV.pairSem δ sd σ r γ sγ dp rp df rf dg rg)
                                      (λ spv → returnRel (λ c c′ sc → toObserved (returnRel (PROJ (spv c c′ sc))))))
                         (≈-Relatedˡ (≈-trans (assoc _ _ _) (≈-bind (≈-refl _) λ fv → ≈-trans (assoc _ _ _) (≈-bind (≈-refl _) λ gv → idˡ _ _)))
                           (FIN))))))
            where
              rp = resR base Pp
              rf = resR rp Pf
              rg = resR rp Pg
              PROJ : ∀ {p p′} → SameM pure ((A * B) ⟨ σ ⟩) p p′ → Same (B ⟨ σ ⟩) (proj₂ p) (proj₂ p′)
              PROJ sp = proj₂ (returnRel⁻ (fromObserved sp))
              FIN = ≈-Relatedʳ (≈-sym (idˡ (⟦ transfer pp df ⟧ δ σ r (restrict σ Pf (restrict σ Pp γ))) (λ _ → ⟪ d′ ⟫ γ)))
                             (bindRel (pureRet df pp rf) (λ {fv} {fv′} sf₀ →
                               ≈-Relatedʳ (≈-sym (idʳ (⟪ d′ ⟫ γ)))
                                 (bindRel (runs (fl dg d′ rg base)) (λ {gv} {gv′} sg → returnRel (λ c c′ sc → sg c c′ sc)))))

  pair-ηᶜ : ∀ {n} {Γ : Ctx m n} {Ψ A B C π₀ h}
          → Pure Σ fmt S Δ Γ h (C ⇒[ mk-kind Many pure ] (A * B))
          → (d : Δ ⊩ Γ ⊢[ Ψ ] pairᶜ C pure (composeᶜ C pure (fstᶜ A B pure) h) (composeᶜ C pure (sndᶜ A B pure) h)
                               ∷ C ⇒[ mk-kind Many pure ] (A * B) ! π₀)
            (d′ : Δ ⊩ Γ ⊢[ Ψ ] h ∷ C ⇒[ mk-kind Many pure ] (A * B) ! π₀) → _≅_ Σ fmt S d d′
  pair-ηᶜ {Γ = Γ} {Ψ} {A} {B} {C} {π₀} {h} (_ , ph) d d′ δ sd σ r γ sγ = goA (AV.armsLL (inj₁ refl) d)
    where
      open Views δ sd σ r γ sγ
      open ProdV δ sd σ r γ sγ using (pureRet)
      module AV = ArmsV δ sd σ r γ sγ
      T = C ⇒[ mk-kind Many pure ] (A * B)
      GOAL = SameM π₀ (T ⟨ σ ⟩) (⟦ d ⟧ δ σ r γ) (⟦ d′ ⟧ δ σ r γ)
      r₀ = resR base (zero⊑ Ψ)
      e₀ = restrict σ (zero⊑ Ψ) γ
      fstv = ⟦ fstD′ {Γ = Γ} A B pure ⟧ δ σ r e₀
      sndv = ⟦ sndD′ {Γ = Γ} A B pure ⟧ δ σ r e₀
      rr : ∀ {X : Ty m} {x x′} → SameM pure (X ⟨ σ ⟩) x x′ → Same (X ⟨ σ ⟩) x x′
      rr s = returnRel⁻ (fromObserved s)
      goA : AV.Arms d (composeᶜ C pure (fstᶜ A B pure) h) (composeᶜ C pure (sndᶜ A B pure) h) → GOAL
      goA (AV.arms dc₁ dc₂ P₁ P₂) = goB (AV.armsLL (inj₂ refl) dc₁) (AV.armsLL (inj₂ refl) dc₂)
        where
          goB : AV.Arms dc₁ (fstᶜ A B pure) h → AV.Arms dc₂ (sndᶜ A B pure) h → GOAL
          goB (AV.arms _ dh₁ _ Ph₁) (AV.arms _ dh₂ _ Ph₂) with ty-unique dh₁ ph | ty-unique dh₂ ph
          ... | refl | refl with ty-unique dc₁ (composeD (fstD′ A B pure) dh₁) | ty-unique dc₂ (composeD (sndD′ A B pure) dh₂)
          ... | refl | refl =
            sameM {T ⟨ σ ⟩} {π₀}
              (rel (~trans {T} (CombV.pairSem δ sd σ r γ sγ d base dc₁ rc₁ dc₂ rc₂)
                     (~trans {T} (bindRel R₁ (λ sx → bindRel R₂ (λ sy → returnRel (PC sx sy))))
                       (≈-Relatedˡ (≈-trans (idˡ v₁ _) (idˡ v₂ _))
                         (~trans {T} (returnRel SAME) (~sym {T} (pureRet d′ ph base)))))))
            where
              rc₁ = resR base P₁
              rc₂ = resR base P₂
              rh₁ = resR rc₁ Ph₁
              rh₂ = resR rc₂ Ph₂
              hv₁ = ⟦ transfer ph dh₁ ⟧ δ σ r (restrict σ Ph₁ (restrict σ P₁ γ))
              hv₂ = ⟦ transfer ph dh₂ ⟧ δ σ r (restrict σ Ph₂ (restrict σ P₂ γ))
              hv₀ = ⟦ transfer ph d′ ⟧ δ σ r γ
              v₁ = compᵛ pure fstv hv₁
              v₂ = compᵛ pure sndv hv₂
              R₁ : _~_ {C ⇒[ mk-kind Many pure ] A} (⟪ dc₁ ⟫ (restrict σ P₁ γ)) (return∞ v₁)
              R₁ = ~trans {C ⇒[ mk-kind Many pure ] A} (CompV.compSem δ sd σ r γ sγ dc₁ rc₁ (fstD′ A B pure) r₀ dh₁ rh₁)
                     (≈-Relatedˡ (idˡ fstv _) (≈-Relatedʳ (≈-sym (idˡ hv₁ _))
                       (bindRel (pureRet dh₁ ph rh₁) (λ sh → returnRel (λ c c′ sc → toObserved (returnRel (proj₁ (rr {A * B} (sh c c′ sc)))))))))
              R₂ : _~_ {C ⇒[ mk-kind Many pure ] B} (⟪ dc₂ ⟫ (restrict σ P₂ γ)) (return∞ v₂)
              R₂ = ~trans {C ⇒[ mk-kind Many pure ] B} (CompV.compSem δ sd σ r γ sγ dc₂ rc₂ (sndD′ A B pure) r₀ dh₂ rh₂)
                     (≈-Relatedˡ (idˡ sndv _) (≈-Relatedʳ (≈-sym (idˡ hv₂ _))
                       (bindRel (pureRet dh₂ ph rh₂) (λ sh → returnRel (λ c c′ sc → toObserved (returnRel (proj₂ (rr {A * B} (sh c c′ sc)))))))))
              PC : ∀ {x x′ y y′} → Same ((C ⇒[ mk-kind Many pure ] A) ⟨ σ ⟩) x x′ → Same ((C ⇒[ mk-kind Many pure ] B) ⟨ σ ⟩) y y′
                 → Same (T ⟨ σ ⟩) (pairᵛ pure x y) (pairᵛ pure x′ y′)
              PC sx sy c c′ sc = toObserved (returnRel (rr {A} (sx c c′ sc) , rr {B} (sy c c′ sc)))
              s₁₀ = relPure⁻ (fl (transfer ph dh₁) (transfer ph d′) rh₁ base)
              s₂₀ = relPure⁻ (fl (transfer ph dh₂) (transfer ph d′) rh₂ base)
              SAME : Same (T ⟨ σ ⟩) (pairᵛ pure v₁ v₂) hv₀
              SAME c c′ sc = toObserved (returnRel (proj₁ (rr {A * B} (s₁₀ c c′ sc)) , proj₂ (rr {A * B} (s₂₀ c c′ sc))))

  curry-βᶜ : ∀ {n} {Γ : Ctx m n} {Ψ A B C π₀ f}
           → Pure Σ fmt S Δ Γ f ((A * B) ⇒[ mk-kind Many pure ] C)
           → (d : Δ ⊩ Γ ⊢[ Ψ ] composeᶜ (A * B) pure (applyᶜ B C)
                                 (pairᶜ (A * B) pure (composeᶜ (A * B) pure (curryᶜ A B pure pure f) (fstᶜ A B pure))
                                                     (sndᶜ A B pure))
                                ∷ (A * B) ⇒[ mk-kind Many pure ] C ! π₀)
             (d′ : Δ ⊩ Γ ⊢[ Ψ ] f ∷ (A * B) ⇒[ mk-kind Many pure ] C ! π₀) → _≅_ Σ fmt S d d′
  curry-βᶜ {Γ = Γ} {Ψ} {A} {B} {C} {π₀} {f} (_ , pf) d d′ δ sd σ r γ sγ = goA (AV.armsLL (inj₂ refl) d)
    where
      open Views δ sd σ r γ sγ
      open ProdV δ sd σ r γ sγ using (pureRet)
      module AV = ArmsV δ sd σ r γ sγ
      T  = (A * B) ⇒[ mk-kind Many pure ] C
      GOAL = SameM π₀ (T ⟨ σ ⟩) (⟦ d ⟧ δ σ r γ) (⟦ d′ ⟧ δ σ r γ)
      BC = B ⇒[ mk-kind Many pure ] C
      r₀ = resR base (zero⊑ Ψ)
      e₀ = restrict σ (zero⊑ Ψ) γ
      fstv = ⟦ fstD′ {Γ = Γ} A B pure ⟧ δ σ r e₀
      sndv = ⟦ sndD′ {Γ = Γ} A B pure ⟧ δ σ r e₀
      apv  = ⟦ applyD {Γ = Γ} B C ⟧ δ σ r (restrict σ (zero⊑ω Ψ) γ)
      rA = resR base (zero⊑ω Ψ)
      goA : AV.Arms d (applyᶜ B C) (pairᶜ (A * B) pure (composeᶜ (A * B) pure (curryᶜ A B pure pure f) (fstᶜ A B pure)) (sndᶜ A B pure)) → GOAL
      goA (AV.arms _ dpr _ Ppr) = goB (AV.armsLL (inj₁ refl) dpr)
        where
          rpr = resR base Ppr
          goB : AV.Arms dpr (composeᶜ (A * B) pure (curryᶜ A B pure pure f) (fstᶜ A B pure)) (sndᶜ A B pure) → GOAL
          goB (AV.arms dcm _ Pcm _) = goC (AV.armsLL (inj₂ refl) dcm)
            where
              rcm = resR rpr Pcm
              goC : AV.Arms dcm (curryᶜ A B pure pure f) (fstᶜ A B pure) → GOAL
              goC (AV.arms dcu _ Pcu _) = goD (AV.armL1 dcu)
                where
                  rcu = resR rcm Pcu
                  goD : AV.Arm1 dcu f → GOAL
                  goD (AV.arm1 dfa Pfa) with ty-unique dfa pf
                  ... | refl with ty-unique dcu (curryD dfa)
                  ... | refl with ty-unique dcm (composeD dcu (fstD′ A B pure))
                  ... | refl with ty-unique dpr (pairD dcm (sndD′ A B pure))
                  ... | refl =
                    sameM {T ⟨ σ ⟩} {π₀}
                      (rel (~trans {T} (CompV.compSem δ sd σ r γ sγ d base (applyD B C) rA dpr rpr)
                             (≈-Relatedˡ (idˡ apv _)
                               (~trans {T} (bindRel RPR (λ spv → returnRel (AP spv)))
                                 (≈-Relatedˡ (idˡ prv _)
                                   (~trans {T} (returnRel FINAL) (~sym {T} (pureRet d′ pf base))))))))
                    where
                      rfa = resR rcu Pfa
                      fv₁ = ⟦ transfer pf dfa ⟧ δ σ r (restrict σ Pfa (restrict σ Pcu (restrict σ Pcm (restrict σ Ppr γ))))
                      cuv = λ a b → fv₁ (a , b)
                      cmv = compᵛ pure cuv fstv
                      prv = pairᵛ pure cmv sndv
                      RCU : _~_ {A ⇒[ mk-kind Many pure ] BC} (⟪ dcu ⟫ _) (return∞ cuv)
                      RCU = ~trans {A ⇒[ mk-kind Many pure ] BC} (CombV.currySem δ sd σ r γ sγ dcu rcu dfa rfa)
                              (≈-Relatedʳ (≈-sym (idˡ fv₁ _)) (bindRel (pureRet dfa pf rfa) (λ sf →
                                 returnRel (toSameP σ {A} {BC} (λ sa → toSameP σ {B} {C} (λ sb → fromSameP σ {A * B} {C} sf (sa , sb)))))))
                      RCM : _~_ {(A * B) ⇒[ mk-kind Many pure ] BC} (⟪ dcm ⟫ _) (return∞ cmv)
                      RCM = ~trans {(A * B) ⇒[ mk-kind Many pure ] BC} (CompV.compSem δ sd σ r γ sγ dcm rcm dcu rcu (fstD′ A B pure) r₀)
                              (≈-Relatedˡ (≈-bind (≈-refl _) (λ x → idˡ fstv _))
                                (≈-Relatedʳ (≈-sym (idˡ cuv _)) (bindRel RCU (λ sx →
                                   returnRel (toSameP σ {A * B} {BC} (λ sp → fromSameP σ {A} {BC} sx (proj₁ sp)))))))
                      RPR : _~_ {(A * B) ⇒[ mk-kind Many pure ] (BC * B)} (⟪ dpr ⟫ _) (return∞ prv)
                      RPR = ~trans {(A * B) ⇒[ mk-kind Many pure ] (BC * B)} (CombV.pairSem δ sd σ r γ sγ dpr rpr dcm rcm (sndD′ A B pure) r₀)
                              (≈-Relatedˡ (≈-bind (≈-refl _) (λ x → idˡ sndv _))
                                (≈-Relatedʳ (≈-sym (idˡ cmv _)) (bindRel RCM (λ sx →
                                   returnRel (toSameP σ {A * B} {BC * B} (λ sp → fromSameP σ {A * B} {BC} sx sp , proj₂ sp))))))
                      AP : ∀ {pv pv′} → Same (((A * B) ⇒[ mk-kind Many pure ] (BC * B)) ⟨ σ ⟩) pv pv′
                         → Same (T ⟨ σ ⟩) (compᵛ pure apv pv) (compᵛ pure apv pv′)
                      AP spv = toSameP σ {A * B} {C} (λ sp → let s = fromSameP σ {A * B} {BC * B} spv sp in fromSameP σ {B} {C} (proj₁ s) (proj₂ s))
                      s₁₀ = relPure⁻ (fl (transfer pf dfa) (transfer pf d′) rfa base)
                      FINAL : Same (T ⟨ σ ⟩) (compᵛ pure apv prv) (⟦ transfer pf d′ ⟧ δ σ r γ)
                      FINAL = toSameP σ {A * B} {C} (λ sp → fromSameP σ {A * B} {C} s₁₀ sp)

  curry-ηᶜ : ∀ {n} {Γ : Ctx m n} {Ψ A B C π₀ h}
           → Pure Σ fmt S Δ Γ h (A ⇒[ mk-kind Many pure ] (B ⇒[ mk-kind Many pure ] C))
           → (d : Δ ⊩ Γ ⊢[ Ψ ] curryᶜ A B pure pure
                                 (composeᶜ (A * B) pure (applyᶜ B C)
                                   (pairᶜ (A * B) pure (composeᶜ (A * B) pure h (fstᶜ A B pure)) (sndᶜ A B pure)))
                                ∷ A ⇒[ mk-kind Many pure ] (B ⇒[ mk-kind Many pure ] C) ! π₀)
             (d′ : Δ ⊩ Γ ⊢[ Ψ ] h ∷ A ⇒[ mk-kind Many pure ] (B ⇒[ mk-kind Many pure ] C) ! π₀) → _≅_ Σ fmt S d d′
  curry-ηᶜ {Γ = Γ} {Ψ} {A} {B} {C} {π₀} {h} (_ , ph) d d′ δ sd σ r γ sγ = goA (AV.armL1 d)
    where
      open Views δ sd σ r γ sγ
      open ProdV δ sd σ r γ sγ using (pureRet)
      module AV = ArmsV δ sd σ r γ sγ
      BC = B ⇒[ mk-kind Many pure ] C
      T  = A ⇒[ mk-kind Many pure ] BC
      GOAL = SameM π₀ (T ⟨ σ ⟩) (⟦ d ⟧ δ σ r γ) (⟦ d′ ⟧ δ σ r γ)
      r₀ = resR base (zero⊑ Ψ)
      e₀ = restrict σ (zero⊑ Ψ) γ
      fstv = ⟦ fstD′ {Γ = Γ} A B pure ⟧ δ σ r e₀
      sndv = ⟦ sndD′ {Γ = Γ} A B pure ⟧ δ σ r e₀
      apv  = ⟦ applyD {Γ = Γ} B C ⟧ δ σ r (restrict σ (zero⊑ω Ψ) γ)
      rA = resR base (zero⊑ω Ψ)
      goA : AV.Arm1 d (composeᶜ (A * B) pure (applyᶜ B C) (pairᶜ (A * B) pure (composeᶜ (A * B) pure h (fstᶜ A B pure)) (sndᶜ A B pure))) → GOAL
      goA (AV.arm1 dce Pce) = goB (AV.armsLL (inj₂ refl) dce)
        where
          rce = resR base Pce
          goB : AV.Arms dce (applyᶜ B C) (pairᶜ (A * B) pure (composeᶜ (A * B) pure h (fstᶜ A B pure)) (sndᶜ A B pure)) → GOAL
          goB (AV.arms _ dpr _ Ppr) = goC (AV.armsLL (inj₁ refl) dpr)
            where
              rpr = resR rce Ppr
              goC : AV.Arms dpr (composeᶜ (A * B) pure h (fstᶜ A B pure)) (sndᶜ A B pure) → GOAL
              goC (AV.arms dcm _ Pcm _) = goD (AV.armsLL (inj₂ refl) dcm)
                where
                  rcm = resR rpr Pcm
                  goD : AV.Arms dcm h (fstᶜ A B pure) → GOAL
                  goD (AV.arms dh _ Ph _) with ty-unique dh ph
                  ... | refl with ty-unique dcm (composeD dh (fstD′ A B pure))
                  ... | refl with ty-unique dpr (pairD dcm (sndD′ A B pure))
                  ... | refl with ty-unique dce (composeD (applyD B C) dpr)
                  ... | refl =
                    sameM {T ⟨ σ ⟩} {π₀}
                      (rel (~trans {T} (CombV.currySem δ sd σ r γ sγ d base dce rce)
                             (~trans {T} (bindRel RCE (λ sf → returnRel (CU sf)))
                               (≈-Relatedˡ (idˡ cev _)
                                 (~trans {T} (returnRel FINAL) (~sym {T} (pureRet d′ ph base)))))))
                    where
                      rh = resR rcm Ph
                      hv₁ = ⟦ transfer ph dh ⟧ δ σ r (restrict σ Ph (restrict σ Pcm (restrict σ Ppr (restrict σ Pce γ))))
                      cmv = compᵛ pure hv₁ fstv
                      prv = pairᵛ pure cmv sndv
                      cev = compᵛ pure apv prv
                      RCM : _~_ {(A * B) ⇒[ mk-kind Many pure ] BC} (⟪ dcm ⟫ _) (return∞ cmv)
                      RCM = ~trans {(A * B) ⇒[ mk-kind Many pure ] BC} (CompV.compSem δ sd σ r γ sγ dcm rcm dh rh (fstD′ A B pure) r₀)
                              (≈-Relatedˡ (≈-bind (≈-refl _) (λ x → idˡ fstv _))
                                (≈-Relatedʳ (≈-sym (idˡ hv₁ _)) (bindRel (pureRet dh ph rh) (λ sx →
                                   returnRel (toSameP σ {A * B} {BC} (λ sp → fromSameP σ {A} {BC} sx (proj₁ sp)))))))
                      RPR : _~_ {(A * B) ⇒[ mk-kind Many pure ] (BC * B)} (⟪ dpr ⟫ _) (return∞ prv)
                      RPR = ~trans {(A * B) ⇒[ mk-kind Many pure ] (BC * B)} (CombV.pairSem δ sd σ r γ sγ dpr rpr dcm rcm (sndD′ A B pure) r₀)
                              (≈-Relatedˡ (≈-bind (≈-refl _) (λ x → idˡ sndv _))
                                (≈-Relatedʳ (≈-sym (idˡ cmv _)) (bindRel RCM (λ sx →
                                   returnRel (toSameP σ {A * B} {BC * B} (λ sp → fromSameP σ {A * B} {BC} sx sp , proj₂ sp))))))
                      RCE : _~_ {(A * B) ⇒[ mk-kind Many pure ] C} (⟪ dce ⟫ _) (return∞ cev)
                      RCE = ~trans {(A * B) ⇒[ mk-kind Many pure ] C} (CompV.compSem δ sd σ r γ sγ dce rce (applyD B C) rA dpr rpr)
                              (≈-Relatedˡ (idˡ apv _)
                                (≈-Relatedʳ (≈-sym (idˡ prv _)) (bindRel RPR (λ spv →
                                   returnRel (toSameP σ {A * B} {C} (λ sp → let s = fromSameP σ {A * B} {BC * B} spv sp
                                                                           in fromSameP σ {B} {C} (proj₁ s) (proj₂ s)))))))
                      CU : ∀ {fv fv′} → Same (((A * B) ⇒[ mk-kind Many pure ] C) ⟨ σ ⟩) fv fv′
                         → Same (T ⟨ σ ⟩) (λ a b → fv (a , b)) (λ a b → fv′ (a , b))
                      CU sf = toSameP σ {A} {BC} (λ sa → toSameP σ {B} {C} (λ sb → fromSameP σ {A * B} {C} sf (sa , sb)))
                      s₁₀ = relPure⁻ (fl (transfer ph dh) (transfer ph d′) rh base)
                      FINAL : Same (T ⟨ σ ⟩) (λ a b → cev (a , b)) (⟦ transfer ph d′ ⟧ δ σ r γ)
                      FINAL = toSameP σ {A} {BC} (λ sa → toSameP σ {B} {C} (λ sb → fromSameP σ {B} {C} (fromSameP σ {A} {BC} s₁₀ sa) sb))
