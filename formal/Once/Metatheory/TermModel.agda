{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.TermModel — the term model (`Spec.Metatheory.TermModel`):
-- substitution is typed (`TermModel.Subst`), typing survives type
-- substitution (`TermModel.TySubst`), and a pure `let` means its
-- substitution (`let-β`): the substituted term means what the body means
-- with the bound value in its environment (`TermModel.SubSem`), which is
-- what a canonical `let` means, which by the fundamental lemma is what any
-- derivation of the `let` means.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)
open import Once.Spec.Signature using (OneName)

module Once.Metatheory.TermModel (Σ : Signature) (u : OneName Σ) where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)
open import Once.Spec.Grade using (Zero; One; Many; pure)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Type using (KCtx; TySub; Respects; ∅ₖ; _⟨_⟩)
open import Once.Spec.Context using (Ctx; _▸_; lookup; singleUse; _∷_; _+ᵘ_; _*ᵘ_; _⊑ᵘ_; ⊑ᵘ-+ˡ; ⊑ᵘ-+ʳ; ⊑ᵘ-trans; ⊑ᵘ-*One; ⊑ᵘ-*Many)
open import Once.Spec.Core.Syntax using (Defs; let′; _[_])
open import Once.Spec.Equivalence Σ using (Same)
import Once.Spec.Equivalence
open import Once.Spec.Metatheory using (TermModel; SameDefs; SameEnv)
open import Once.Metatheory.Coherence.Relation Σ using (Related-trans; toObserved)
open import Once.Metatheory.Coherence.Layer Σ using (Rel; rel; runs; relPure⁻)
open import Once.Metatheory.Coherence.PER Σ using (Same-trans)
open import Once.Metatheory.TermModel.Usage using (⊑ᵘ-≡)

module _ (fmt : TargetNum) {s : ℕ} (S : Defs s) where
  open import Once.Spec.Core.Typing Σ S
  open import Once.Spec.Core.Meaning Σ fmt S
  open import Once.Metatheory.TermModel.Subst Σ S using (subst-⊢; sub-⊢; single; cast; single-usage; single-term; module TSub)
  open import Once.Metatheory.TermModel.TySubst Σ S using (ty-subst-⊢)
  open import Once.Metatheory.TermModel.Val Σ fmt S
  open import Once.Metatheory.TermModel.SubSem Σ u fmt S using (module SubSem)
  open import Once.Metatheory.Coherence.Env Σ fmt S using (selfAgree; restrictˡ; restrictʳ)
  open import Once.Metatheory.Coherence.Fundamental Σ u fmt S using (module FL)

  -- A derivation's meaning does not see which proof put its term in place.
  termSubst-sem : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ t t′ B π} (e : t ≡ t′) (D : Δ ⊩ Γ ⊢[ Ψ ] t ∷ B ! π)
                  (δ : DefSem) (σ : TySub m 0) (r : Respects Δ ∅ₖ σ) γ
                → ⟦ subst (λ x → Δ ⊩ Γ ⊢[ Ψ ] x ∷ B ! π) e D ⟧ δ σ r γ ≡ ⟦ D ⟧ δ σ r γ
  termSubst-sem refl D δ σ r γ = refl

  module _ {m n} {Δ : KCtx m} (Γ : Ctx m n) (δ : DefSem) (sd : SameDefs Σ fmt S δ) (σ : TySub m 0) (r : Respects Δ ∅ₖ σ) where
    open SubSem δ sd σ r

    -- A variable other than the substituted one reads the same value.
    varAg : ∀ {U Ψ₀ Ψ₂} {γ : Env σ Γ U} → SelfSame σ γ → ∀ j (nz : NZ (At Ψ₂ j)) (p : singleUse j One ⊑ᵘ Ψ₀) (P : Ψ₀ ⊑ᵘ U) (R : Ψ₂ ⊑ᵘ U)
          → Same (lookup Γ j ⟨ σ ⟩) (lookupᵛ σ Γ j (restrict σ p (restrict σ P γ))) (val σ (restrict σ R γ) j nz)
    varAg {γ = γ} ss j nz p P R =
      subst₂ (Same _)
        (sym (trans (lookup-val σ Γ j (restrict σ p (restrict σ P γ)))
             (trans (restrict-val σ p (restrict σ P γ) j _) (restrict-val σ P γ j _))))
        (sym (restrict-val σ R γ j nz))
        (subst (λ w → Same _ (val σ γ j w) (val σ γ j _)) (nz-irr _ _) (ss j _))

    letCore : ∀ {Ψₜ Ψᵤ q π A B t u}
                (dt : Δ ⊩ (Γ ▸ A) ⊢[ q ∷ Ψₜ ] t ∷ B ! π) (du : Δ ⊩ Γ ⊢[ Ψᵤ ] u ∷ A ! pure)
                (dl : Δ ⊩ Γ ⊢[ Ψₜ +ᵘ q *ᵘ Ψᵤ ] let′ q u t ∷ B ! π)
                (γ : Env σ Γ (Ψₜ +ᵘ q *ᵘ Ψᵤ)) → SameEnv Σ fmt S σ Γ _ γ
            → (canon : Δ ⊩ Γ ⊢[ Ψₜ +ᵘ q *ᵘ Ψᵤ ] let′ q u t ∷ B ! π) (γdt : Env σ (Γ ▸ A) (q ∷ Ψₜ))
            → ⟦ canon ⟧ δ σ r γ ≡ ⟦ dt ⟧ δ σ r γdt
            → SubAgree (single du) (q ∷ Ψₜ) (restrict σ (⊑ᵘ-≡ (single-usage du q Ψₜ)) γ) γdt
            → Once.Spec.Equivalence.SameM Σ π (B ⟨ σ ⟩) (⟦ subst-⊢ dt du ⟧ δ σ r γ) (⟦ dl ⟧ δ σ r γ)
    letCore {Ψₜ} {Ψᵤ} {q} {π} {A} {B} {t} dt du dl γ sγ canon γdt ceq ag =
      toObserved
        (Related-trans (Same-trans (B ⟨ σ ⟩))
          (runs (subst₂ (Rel π π (B ⟨ σ ⟩))
                        (sym (termSubst-sem (single-term du t) (cast (single-usage du q Ψₜ) (sub-⊢ (single du) dt)) δ σ r γ))
                        (sym ceq)
                        (subSem (single du) dt (selfSame-restrict σ _ {γ = γ} (selfSame σ Γ _ γ sγ)) ag)))
          (runs (FL.FL δ sd σ r r canon dl refl (selfAgree σ Γ _ γ sγ))))

  let-β : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψₜ Ψᵤ q π A B t u}
            (dt : Δ ⊩ (Γ ▸ A) ⊢[ q ∷ Ψₜ ] t ∷ B ! π) (du : Δ ⊩ Γ ⊢[ Ψᵤ ] u ∷ A ! pure)
            (dl : Δ ⊩ Γ ⊢[ Ψₜ +ᵘ q *ᵘ Ψᵤ ] let′ q u t ∷ B ! π)
            (δ : DefSem) → SameDefs Σ fmt S δ → (σ : TySub m 0) (r : Respects Δ ∅ₖ σ)
            (γ : Env σ Γ (Ψₜ +ᵘ q *ᵘ Ψᵤ)) → SameEnv Σ fmt S σ Γ _ γ
          → Once.Spec.Equivalence.SameM Σ π (B ⟨ σ ⟩) (⟦ subst-⊢ dt du ⟧ δ σ r γ) (⟦ dl ⟧ δ σ r γ)
  let-β {Γ = Γ} {Ψₜ} {Ψᵤ} {Zero} dt du dl δ sd σ r γ sγ =
    letCore Γ δ sd σ r dt du dl γ sγ (⊢let {q = Zero} {π₁ = pure} du dt) (restrict σ (⊑ᵘ-+ˡ Ψₜ (Zero *ᵘ Ψᵤ)) γ , tt) refl ag
    where
      ag : _
      ag zero () p
      ag (suc j) nz p = varAg Γ δ sd σ r (selfSame σ Γ _ γ sγ) j nz p (⊑ᵘ-≡ (single-usage du _ Ψₜ)) (⊑ᵘ-+ˡ Ψₜ (_ *ᵘ Ψᵤ))
  let-β {Γ = Γ} {Ψₜ} {Ψᵤ} {One} dt du dl δ sd σ r γ sγ =
    letCore Γ δ sd σ r dt du dl γ sγ (⊢let {q = One} {π₁ = pure} du dt)
      (restrict σ (⊑ᵘ-+ˡ Ψₜ (One *ᵘ Ψᵤ)) γ , ⟦ du ⟧ δ σ r (restrict σ R₁ γ)) refl ag
    where
      R₁ = ⊑ᵘ-trans (⊑ᵘ-*One Ψᵤ) (⊑ᵘ-+ʳ Ψₜ (One *ᵘ Ψᵤ))
      ag : _
      ag zero nz p = relPure⁻ (FL.FL δ sd σ r r du du refl
                       (restrictˡ σ p (restrictˡ σ _ (restrictʳ σ R₁ (selfAgree σ Γ _ γ sγ)))))
      ag (suc j) nz p = varAg Γ δ sd σ r (selfSame σ Γ _ γ sγ) j nz p (⊑ᵘ-≡ (single-usage du _ Ψₜ)) (⊑ᵘ-+ˡ Ψₜ (_ *ᵘ Ψᵤ))
  let-β {Γ = Γ} {Ψₜ} {Ψᵤ} {Many} dt du dl δ sd σ r γ sγ =
    letCore Γ δ sd σ r dt du dl γ sγ (⊢let {q = Many} {π₁ = pure} du dt)
      (restrict σ (⊑ᵘ-+ˡ Ψₜ (Many *ᵘ Ψᵤ)) γ , ⟦ du ⟧ δ σ r (restrict σ R₁ γ)) refl ag
    where
      R₁ = ⊑ᵘ-trans (⊑ᵘ-*Many Ψᵤ) (⊑ᵘ-+ʳ Ψₜ (Many *ᵘ Ψᵤ))
      ag : _
      ag zero nz p = relPure⁻ (FL.FL δ sd σ r r du du refl
                       (restrictˡ σ p (restrictˡ σ _ (restrictʳ σ R₁ (selfAgree σ Γ _ γ sγ)))))
      ag (suc j) nz p = varAg Γ δ sd σ r (selfSame σ Γ _ γ sγ) j nz p (⊑ᵘ-≡ (single-usage du _ Ψₜ)) (⊑ᵘ-+ˡ Ψₜ (_ *ᵘ Ψᵤ))

  termModel : TermModel Σ fmt S
  termModel = record
    { subst-⊢    = subst-⊢
    ; let-β      = let-β
    ; ty-subst-⊢ = λ σ rσ d → ty-subst-⊢ σ rσ d
    }
