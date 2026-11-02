{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws.Categorical — the combinator laws
-- (`Spec.Metatheory.Categorical`): each side, read through what its
-- combinators mean (`Laws.Compose`, …), is the same computation; the closures
-- are the same functions (extensionally, by the monad laws up to
-- bisimilarity).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature; OneName)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Laws.Categorical (Σ : Signature) (u : OneName Σ) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

open import Data.Fin using (zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Once.Spec.Grade using (Quantity; Zero; One; Many; mk-kind; Purity; pure; 0≤q; 1≤ω)
open import Once.Spec.Type using (Ty; KCtx; TySub; _⟨_⟩; _⇒[_]_)
open import Once.Spec.Context using (Ctx; ∅; _▸_; _∷_; []; Usage; zeroUsage; _⊑ᵘ_; _⊑∷_)
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

-- Nothing is used below every usage.
zero⊑ : ∀ {n} (Ψ : Usage n) → zeroUsage ⊑ᵘ Ψ
zero⊑ []      = []
zero⊑ (q ∷ Ψ) = 0≤q ⊑∷ zero⊑ Ψ

module _ {m : ℕ} {Δ : KCtx m} where

  -- `idᶜ`, typed once and for all.
  idD : ∀ {n} {Γ : Ctx m n} (B : Ty m) (π : Purity) → Δ ⊩ Γ ⊢[ zeroUsage ] idᶜ B π ∷ B ⇒[ mk-kind Many π ] B ! pure
  idD B π = ⊢lam 1≤ω (⊢sub-eff (pure⊑ π) (⊢var zero))

  compose-idˡ : ∀ {n} {Γ : Ctx m n} {Ψ A B π π₀ f}
                (d : Δ ⊩ Γ ⊢[ Ψ ] composeᶜ A π (idᶜ B π) f ∷ A ⇒[ mk-kind Many π ] B ! π₀)
                (d′ : Δ ⊩ Γ ⊢[ Ψ ] f ∷ A ⇒[ mk-kind Many π ] B ! π₀) → _≅_ Σ fmt S d d′
  compose-idˡ {Γ = Γ} {Ψ} {A} {B} {π} {π₀} d d′ δ sd σ r γ sγ =
    sameM {T ⟨ σ ⟩} {π₀}
      (rel (~trans {T} (CompV.compSem δ sd σ r γ sγ d base (idD B π) r₀ d′ base)
             (≈-Relatedˡ (idˡ _ _)
               (≈-Relatedʳ (≈-sym (idʳ (⟪ d′ ⟫ γ)))
                 (bindRel (runs (fl d′ d′ base base)) (λ sg → returnRel (SAME sg)))))))
    where
      open Views δ sd σ r γ sγ
      T = A ⇒[ mk-kind Many π ] B
      r₀ = resR base (zero⊑ Ψ)
      idv = ⟦ idD {Γ = Γ} B π ⟧ δ σ r (restrict σ (zero⊑ Ψ) γ)
      SAME : ∀ {gv gv′} → Same (T ⟨ σ ⟩) gv gv′ → Same (T ⟨ σ ⟩) (compᵛ π idv gv) gv′
      SAME {gv} {gv′} sg a a′ sa = toObserved
        (≈-Relatedˡ (≈-trans (toT∞-bind π (gv a) idv) (≈-trans (≈-bind (≈-refl _) (λ b → toT∞-sub (pure⊑ π) b)) (idʳ _)))
          (runs (appMany {π} {A ⟨ σ ⟩} {B ⟨ σ ⟩} sg sa)))

  compose-idʳ : ∀ {n} {Γ : Ctx m n} {Ψ A B π π₀ f}
                (d : Δ ⊩ Γ ⊢[ Ψ ] composeᶜ A π f (idᶜ A π) ∷ A ⇒[ mk-kind Many π ] B ! π₀)
                (d′ : Δ ⊩ Γ ⊢[ Ψ ] f ∷ A ⇒[ mk-kind Many π ] B ! π₀) → _≅_ Σ fmt S d d′
  compose-idʳ {Γ = Γ} {Ψ} {A} {B} {π} {π₀} d d′ δ sd σ r γ sγ =
    sameM {T ⟨ σ ⟩} {π₀}
      (rel (~trans {T} (CompV.compSem δ sd σ r γ sγ d base d′ base (idD A π) r₀)
             (≈-Relatedʳ (≈-sym (idʳ (⟪ d′ ⟫ γ)))
               (bindRel (runs (fl d′ d′ base base))
                 (λ {fv} {fv′} sf → ≈-Relatedˡ (idˡ idv (λ gv → return∞ (compᵛ π fv gv))) (returnRel (SAME sf)))))))
    where
      open Views δ sd σ r γ sγ
      T = A ⇒[ mk-kind Many π ] B
      r₀ = resR base (zero⊑ Ψ)
      idv = ⟦ idD {Γ = Γ} A π ⟧ δ σ r (restrict σ (zero⊑ Ψ) γ)
      SAME : ∀ {fv fv′} → Same (T ⟨ σ ⟩) fv fv′ → Same (T ⟨ σ ⟩) (compᵛ π fv idv) fv′
      SAME {fv} {fv′} sf a a′ sa = toObserved
        (≈-Relatedˡ (≈-trans (toT∞-bind π (idv a) fv) (≈-trans (≈-bind (toT∞-sub (pure⊑ π) a) (λ _ → ≈-refl _)) (idˡ a _)))
          (runs (appMany {π} {A ⟨ σ ⟩} {B ⟨ σ ⟩} sf sa)))

  terminal-uniqueᶜ : ∀ {n} {Γ : Ctx m n} {Ψ A π₀ h}
                   → Pure Σ fmt S Δ Γ h (A ⇒[ mk-kind Many pure ] Unit)
                   → (d : Δ ⊩ Γ ⊢[ Ψ ] h ∷ A ⇒[ mk-kind Many pure ] Unit ! π₀)
                     (d′ : Δ ⊩ Γ ⊢[ Ψ ] terminalᶜ A pure ∷ A ⇒[ mk-kind Many pure ] Unit ! π₀) → _≅_ Σ fmt S d d′
  terminal-uniqueᶜ {Ψ = Ψ} {A} {π₀} (_ , ph) d d′ δ sd σ r γ sγ =
    sameM {T ⟨ σ ⟩} {π₀}
      (rel (~trans {T} (pureRet d ph base) (~trans {T} (returnRel SAME) (~sym {T} (runs (fl d′ (terminalD A pure) base r₀))))))
    where
      open Views δ sd σ r γ sγ
      open ProdV δ sd σ r γ sγ using (pureRet)
      T = A ⇒[ mk-kind Many pure ] Unit
      r₀ = resR base (zero⊑ Ψ)
      SAME : ∀ {hv tv} → Same (T ⟨ σ ⟩) hv tv
      SAME a a′ sa = toObserved (returnRel tt)

  initial-uniqueᶜ : ∀ {n} {Γ : Ctx m n} {Ψ A π π₀ h}
                  → Pure Σ fmt S Δ Γ h (Void ⇒[ mk-kind Many π ] A)
                  → (d : Δ ⊩ Γ ⊢[ Ψ ] h ∷ Void ⇒[ mk-kind Many π ] A ! π₀)
                    (d′ : Δ ⊩ Γ ⊢[ Ψ ] initialᶜ A π ∷ Void ⇒[ mk-kind Many π ] A ! π₀) → _≅_ Σ fmt S d d′
  initial-uniqueᶜ {Ψ = Ψ} {A} {π} {π₀} (_ , ph) d d′ δ sd σ r γ sγ =
    sameM {T ⟨ σ ⟩} {π₀}
      (rel (~trans {T} (pureRet d ph base) (~trans {T} (returnRel SAME) (~sym {T} (runs (fl d′ (initialD A π) base r₀))))))
    where
      open Views δ sd σ r γ sγ
      open ProdV δ sd σ r γ sγ using (pureRet)
      T = Void ⇒[ mk-kind Many π ] A
      r₀ = resR base (zero⊑ Ψ)
      SAME : ∀ {hv iv} → Same (T ⟨ σ ⟩) hv iv
      SAME () a′ sa

  case-ηᶜ : ∀ {n} {Γ : Ctx m n} {Ψ A B π π₀}
            (d : Δ ⊩ Γ ⊢[ Ψ ] caseᶜ A B π (inlᶜ A B π) (inrᶜ A B π) ∷ (A + B) ⇒[ mk-kind Many π ] (A + B) ! π₀)
            (d′ : Δ ⊩ Γ ⊢[ Ψ ] idᶜ (A + B) π ∷ (A + B) ⇒[ mk-kind Many π ] (A + B) ! π₀) → _≅_ Σ fmt S d d′
  case-ηᶜ {Γ = Γ} {Ψ} {A} {B} {π} {π₀} d d′ δ sd σ r γ sγ =
    sameM {T ⟨ σ ⟩} {π₀}
      (rel (~trans {T} (CombV.caseSem δ sd σ r γ sγ d base (inlD A B π) r₀ (inrD A B π) r₀)
             (≈-Relatedˡ (≈-trans (idˡ _ _) (idˡ _ _))
               (~trans {T} (returnRel SAME) (~sym {T} (runs (fl d′ (idD (A + B) π) base r₀)))))))
    where
      open Views δ sd σ r γ sγ
      T = (A + B) ⇒[ mk-kind Many π ] (A + B)
      r₀ = resR base (zero⊑ Ψ)
      e₀ = restrict σ (zero⊑ Ψ) γ
      inlv = ⟦ inlD {Γ = Γ} A B π ⟧ δ σ r e₀
      inrv = ⟦ inrD {Γ = Γ} A B π ⟧ δ σ r e₀
      idv  = ⟦ idD {Γ = Γ} (A + B) π ⟧ δ σ r e₀
      SAME : Same (T ⟨ σ ⟩) [ inlv , inrv ]′ idv
      SAME (inj₁ a) (inj₁ a′) s = toObserved
        (≈-Relatedˡ (toT∞-sub (pure⊑ π) (inj₁ a)) (≈-Relatedʳ (toT∞-sub (pure⊑ π) (inj₁ a′)) (returnRel s)))
      SAME (inj₂ b) (inj₂ b′) s = toObserved
        (≈-Relatedˡ (toT∞-sub (pure⊑ π) (inj₂ b)) (≈-Relatedʳ (toT∞-sub (pure⊑ π) (inj₂ b′)) (returnRel s)))
      SAME (inj₁ _) (inj₂ _) ()
      SAME (inj₂ _) (inj₁ _) ()

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
      r₀ = resR base (zero⊑ Ψ)
      projv = ⟦ fstD′ {Γ = Γ} A B pure ⟧ δ σ r (restrict σ (zero⊑ Ψ) γ)
      goA : AV.Arms d (fstᶜ A B pure) (pairᶜ C pure f g) → _
      goA (AV.arms dfst dp Pfst Pp) = goB (AV.armsLL (inj₁ refl) dp)
        where
          goB : AV.Arms dp f g → _
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
      r₀ = resR base (zero⊑ Ψ)
      projv = ⟦ sndD′ {Γ = Γ} A B pure ⟧ δ σ r (restrict σ (zero⊑ Ψ) γ)
      goA : AV.Arms d (sndᶜ A B pure) (pairᶜ C pure f g) → _
      goA (AV.arms dfst dp Pfst Pp) = goB (AV.armsLL (inj₁ refl) dp)
        where
          goB : AV.Arms dp f g → _
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

  case-inlᶜ : ∀ {n} {Γ : Ctx m n} {Ψ A B C π π₀ f g}
       → Pure Σ fmt S Δ Γ g (B ⇒[ mk-kind Many π ] C)
       → (d : Δ ⊩ Γ ⊢[ Ψ ] composeᶜ A π (caseᶜ A B π f g) (inlᶜ A B π) ∷ A ⇒[ mk-kind Many π ] C ! π₀)
         (d′ : Δ ⊩ Γ ⊢[ Ψ ] f ∷ A ⇒[ mk-kind Many π ] C ! π₀) → _≅_ Σ fmt S d d′
  case-inlᶜ {Γ = Γ} {Ψ} {A} {B} {C} {π} {π₀} {f} {g} (_ , pp) d d′ δ sd σ r γ sγ = goA (AV.armsLL (inj₂ refl) d)
    where
      open Views δ sd σ r γ sγ
      open ProdV δ sd σ r γ sγ using (pureRet)
      module AV = ArmsV δ sd σ r γ sγ
      T = A ⇒[ mk-kind Many π ] C
      r₀ = resR base (zero⊑ Ψ)
      injv = ⟦ inlD {Γ = Γ} A B π ⟧ δ σ r (restrict σ (zero⊑ Ψ) γ)
      -- calling a function on the injected value is calling it at the injection
      E : ∀ (h : ⟦ ((A + B) ⇒[ mk-kind Many π ] C) ⟨ σ ⟩ ⟧ᵛ) a → toT∞ π (bind π (injv a) h) ≈ toT∞ π (h (inj₁ a))
      E h a = ≈-trans (toT∞-bind π (injv a) h) (≈-trans (≈-bind (toT∞-sub (pure⊑ π) (inj₁ a)) (λ _ → ≈-refl _)) (idˡ (inj₁ a) _))
      CC : ∀ {cv cv′} → Same (((A + B) ⇒[ mk-kind Many π ] C) ⟨ σ ⟩) cv cv′ → Same (T ⟨ σ ⟩) (compᵛ π cv injv) (compᵛ π cv′ injv)
      CC {cv} {cv′} scv a a′ sa = toObserved (≈-Relatedˡ (E cv a) (≈-Relatedʳ (E cv′ a′) (runs (appMany {π} {(A + B) ⟨ σ ⟩} {C ⟨ σ ⟩} scv {inj₁ a} {inj₁ a′} sa))))
      goA : AV.Arms d (caseᶜ A B π f g) (inlᶜ A B π) → _
      goA (AV.arms dc di Pc Pi) = goB (AV.armsLL (inj₁ refl) dc)
        where
          goB : AV.Arms dc f g → _
          goB (AV.arms df dg Pf Pg) with ty-unique dg pp | ty-unique df d′
          ... | refl | refl with ty-unique dc (caseD df dg)
          ... | refl =
            sameM {T ⟨ σ ⟩} {π₀}
              (rel (~trans {T} (CompV.compSem δ sd σ r γ sγ d base dc rc (inlD A B π) r₀)
                     (≈-Relatedˡ (≈-bind (≈-refl _) (λ cv → idˡ injv _))
                       (~trans {T} (bindRel (CombV.caseSem δ sd σ r γ sγ dc rc df rf dg rg) (λ scv → returnRel (CC scv)))
                         (≈-Relatedˡ (≈-trans (assoc _ _ _) (≈-bind (≈-refl _) λ fv → ≈-trans (assoc _ _ _) (≈-bind (≈-refl _) λ gv → idˡ _ _)))
                           FIN)))))
            where
              rc = resR base Pc
              rf = resR rc Pf
              rg = resR rc Pg
              FIN = ≈-Relatedʳ (≈-sym (idʳ (⟪ d′ ⟫ γ)))
                      (bindRel (runs (fl df d′ rf base)) (λ {fv} {fv′} sf →
                        ≈-Relatedʳ (≈-sym (idˡ (⟦ transfer pp dg ⟧ δ σ r (restrict σ Pg (restrict σ Pc γ))) (λ _ → return∞ fv′)))
                          (bindRel (pureRet dg pp rg) (λ {gv} {gv′} _ → returnRel
                             (λ a a′ sa → toObserved (≈-Relatedˡ (E [ fv , gv ]′ a) (runs (appMany {π} {A ⟨ σ ⟩} {C ⟨ σ ⟩} sf sa))))))))

  case-inrᶜ : ∀ {n} {Γ : Ctx m n} {Ψ A B C π π₀ f g}
       → Pure Σ fmt S Δ Γ f (A ⇒[ mk-kind Many π ] C)
       → (d : Δ ⊩ Γ ⊢[ Ψ ] composeᶜ B π (caseᶜ A B π f g) (inrᶜ A B π) ∷ B ⇒[ mk-kind Many π ] C ! π₀)
         (d′ : Δ ⊩ Γ ⊢[ Ψ ] g ∷ B ⇒[ mk-kind Many π ] C ! π₀) → _≅_ Σ fmt S d d′
  case-inrᶜ {Γ = Γ} {Ψ} {A} {B} {C} {π} {π₀} {f} {g} (_ , pp) d d′ δ sd σ r γ sγ = goA (AV.armsLL (inj₂ refl) d)
    where
      open Views δ sd σ r γ sγ
      open ProdV δ sd σ r γ sγ using (pureRet)
      module AV = ArmsV δ sd σ r γ sγ
      T = B ⇒[ mk-kind Many π ] C
      r₀ = resR base (zero⊑ Ψ)
      injv = ⟦ inrD {Γ = Γ} A B π ⟧ δ σ r (restrict σ (zero⊑ Ψ) γ)
      -- calling a function on the injected value is calling it at the injection
      E : ∀ (h : ⟦ ((A + B) ⇒[ mk-kind Many π ] C) ⟨ σ ⟩ ⟧ᵛ) a → toT∞ π (bind π (injv a) h) ≈ toT∞ π (h (inj₂ a))
      E h a = ≈-trans (toT∞-bind π (injv a) h) (≈-trans (≈-bind (toT∞-sub (pure⊑ π) (inj₂ a)) (λ _ → ≈-refl _)) (idˡ (inj₂ a) _))
      CC : ∀ {cv cv′} → Same (((A + B) ⇒[ mk-kind Many π ] C) ⟨ σ ⟩) cv cv′ → Same (T ⟨ σ ⟩) (compᵛ π cv injv) (compᵛ π cv′ injv)
      CC {cv} {cv′} scv a a′ sa = toObserved (≈-Relatedˡ (E cv a) (≈-Relatedʳ (E cv′ a′) (runs (appMany {π} {(A + B) ⟨ σ ⟩} {C ⟨ σ ⟩} scv {inj₂ a} {inj₂ a′} sa))))
      goA : AV.Arms d (caseᶜ A B π f g) (inrᶜ A B π) → _
      goA (AV.arms dc di Pc Pi) = goB (AV.armsLL (inj₁ refl) dc)
        where
          goB : AV.Arms dc f g → _
          goB (AV.arms df dg Pf Pg) with ty-unique df pp | ty-unique dg d′
          ... | refl | refl with ty-unique dc (caseD df dg)
          ... | refl =
            sameM {T ⟨ σ ⟩} {π₀}
              (rel (~trans {T} (CompV.compSem δ sd σ r γ sγ d base dc rc (inrD A B π) r₀)
                     (≈-Relatedˡ (≈-bind (≈-refl _) (λ cv → idˡ injv _))
                       (~trans {T} (bindRel (CombV.caseSem δ sd σ r γ sγ dc rc df rf dg rg) (λ scv → returnRel (CC scv)))
                         (≈-Relatedˡ (≈-trans (assoc _ _ _) (≈-bind (≈-refl _) λ fv → ≈-trans (assoc _ _ _) (≈-bind (≈-refl _) λ gv → idˡ _ _)))
                           FIN)))))
            where
              rc = resR base Pc
              rf = resR rc Pf
              rg = resR rc Pg
              FIN = ≈-Relatedʳ (≈-sym (idˡ (⟦ transfer pp df ⟧ δ σ r (restrict σ Pf (restrict σ Pc γ))) (λ _ → ⟪ d′ ⟫ γ)))
                      (bindRel (pureRet df pp rf) (λ {fv} {fv′} _ →
                        ≈-Relatedʳ (≈-sym (idʳ (⟪ d′ ⟫ γ)))
                          (bindRel (runs (fl dg d′ rg base)) (λ {gv} {gv′} sg → returnRel
                             (λ b b′ sb → toObserved (≈-Relatedˡ (E [ fv , gv ]′ b) (runs (appMany {π} {B ⟨ σ ⟩} {C ⟨ σ ⟩} sg sb))))))))

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
      r₀ = resR base (zero⊑ Ψ)
      e₀ = restrict σ (zero⊑ Ψ) γ
      fstv = ⟦ fstD′ {Γ = Γ} A B pure ⟧ δ σ r e₀
      sndv = ⟦ sndD′ {Γ = Γ} A B pure ⟧ δ σ r e₀
      rr : ∀ {X : Ty m} {x x′} → SameM pure (X ⟨ σ ⟩) x x′ → Same (X ⟨ σ ⟩) x x′
      rr s = returnRel⁻ (fromObserved s)
      goA : AV.Arms d (composeᶜ C pure (fstᶜ A B pure) h) (composeᶜ C pure (sndᶜ A B pure) h) → _
      goA (AV.arms dc₁ dc₂ P₁ P₂) = goB (AV.armsLL (inj₂ refl) dc₁) (AV.armsLL (inj₂ refl) dc₂)
        where
          goB : AV.Arms dc₁ (fstᶜ A B pure) h → AV.Arms dc₂ (sndᶜ A B pure) h → _
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
