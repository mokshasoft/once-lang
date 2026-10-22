-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Internal.Core.DerivedSubst — substituting types into a derived
-- combinator's typing (`Core.DerivedTyping`) is the typing at the
-- substituted types: `ty-subst-⊢ σ (⊢Xᶜ …) ≅ ⊢Xᶜ (ty-subst-⊢ σ …)`.
-- The step `Adequacy.ElabCommute` takes at each combinator.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)
open import Once.Spec.Type using (TySub; KCtx; Respects)

module Once.Internal.Core.DerivedSubst (Σ : Signature) {s : ℕ} (S : Defs s)
  {m k : ℕ} (σ : TySub m k) {Δ : KCtx m} {Δ′ : KCtx k} (rσ : Respects Δ Δ′ σ) where

open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)
open import Once.Spec.Grade using (1≤ω; Quantity; Zero; One; Many; Purity; pure; act; eff; Finite; fin; pureᶠ; actᶠ; mk-kind; _⊑π_; _·p_)
open import Once.Spec.Type using (Ty; Fun; Unit; Void; _*_; _+_; _⇒[_]_; μ; ν; ⟦_⟧F; WFFun; _⟨_⟩; _⟨_⟩F)
open import Once.Spec.Context using (Ctx; _▸_; _⟨_⟩ᶜ; Usage; _∷_; _*ᵘ_)
open import Once.Surface.Properties using (+ᵘ-identityʳ)
open import Once.Spec.Core.Syntax
open import Once.Spec.Core.Derived
open import Once.Spec.Core.Typing Σ S
import Once.Metatheory.TermModel.TySubst Σ S as TS
open import Once.Internal.Core.TySubstRen Σ S using (⟪⟫-wk; module Deriv)
import Once.Metatheory.TermModel.Subst Σ S as TM
open Deriv σ rσ
import Once.Internal.Core.DerivedTyping Σ S as DT

W : ∀ {F} → WFFun Δ F → WFFun Δ′ (F ⟨ σ ⟩F)
W = TS.wf-⟨⟩ σ rσ

subst-≅ : ∀ {X : Set} (P : X → Set) {x y : X} (e : x ≡ y) (z : P x) → subst P e z ≅ z
subst-≅ P refl z = H.refl

tyU : ∀ {n} {Γ : Ctx m n} {Ψ Ψ′ t A π} (e : Ψ ≡ Ψ′) (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π)
    → ty (subst (λ U → Δ ⊩ Γ ⊢[ U ] t ∷ A ! π) e d) ≅ ty d
tyU refl d = H.refl

-- …and under a fixed context of the usage (a binder's `One ∷ _`).
tyUf : ∀ {n n₀} {Γ : Ctx m n} (f : Usage n₀ → Usage n) {Ψ Ψ′ t A π} (e : Ψ ≡ Ψ′) (d : Δ ⊩ Γ ⊢[ f Ψ ] t ∷ A ! π)
     → ty (subst (λ U → Δ ⊩ Γ ⊢[ f U ] t ∷ A ! π) e d) ≅ ty d
tyUf f refl d = H.refl

substUf-≅ : ∀ {n n₀} {Γ : Ctx k n} (f : Usage n₀ → Usage n) {Ψ Ψ′ t A π} (e : Ψ ≡ Ψ′) (d : Δ′ ⊩ Γ ⊢[ f Ψ ] t ∷ A ! π)
          → subst (λ U → Δ′ ⊩ Γ ⊢[ f U ] t ∷ A ! π) e d ≅ d
substUf-≅ f refl d = H.refl

substU-≅ : ∀ {n} {Γ : Ctx k n} {Ψ Ψ′ t A π} (e : Ψ ≡ Ψ′) (d : Δ′ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π)
         → subst (λ U → Δ′ ⊩ Γ ⊢[ U ] t ∷ A ! π) e d ≅ d
substU-≅ refl d = H.refl

module _ {n} {Γ : Ctx m n} where

  -- The closed combinators: substitution passes through, and each variable is
  -- one of the combinator's own binders, so its transport is the identity.
  dc-id : ∀ {A π} (u : pure ⊑π π) → ty (DT.⊢idᶜ {Γ = Γ} {A = A} u) ≅ DT.⊢idᶜ {Δ = Δ′} {Γ = Γ ⟨ σ ⟩ᶜ} {A = A ⟨ σ ⟩} u
  dc-id u = H.refl

  dc-fst : ∀ {A B π} (u : pure ⊑π π) → ty (DT.⊢fstᶜ {Γ = Γ} {A = A} {B = B} u) ≅ DT.⊢fstᶜ {Δ = Δ′} {Γ = Γ ⟨ σ ⟩ᶜ} {A = A ⟨ σ ⟩} {B = B ⟨ σ ⟩} u
  dc-fst u = H.refl

  dc-snd : ∀ {A B π} (u : pure ⊑π π) → ty (DT.⊢sndᶜ {Γ = Γ} {A = A} {B = B} u) ≅ DT.⊢sndᶜ {Δ = Δ′} {Γ = Γ ⟨ σ ⟩ᶜ} {A = A ⟨ σ ⟩} {B = B ⟨ σ ⟩} u
  dc-snd u = H.refl

  dc-inl : ∀ {A B π} (u : pure ⊑π π) → ty (DT.⊢inlᶜ {Γ = Γ} {A = A} {B = B} u) ≅ DT.⊢inlᶜ {Δ = Δ′} {Γ = Γ ⟨ σ ⟩ᶜ} {A = A ⟨ σ ⟩} {B = B ⟨ σ ⟩} u
  dc-inl u = H.refl

  dc-inr : ∀ {A B π} (u : pure ⊑π π) → ty (DT.⊢inrᶜ {Γ = Γ} {A = A} {B = B} u) ≅ DT.⊢inrᶜ {Δ = Δ′} {Γ = Γ ⟨ σ ⟩ᶜ} {A = A ⟨ σ ⟩} {B = B ⟨ σ ⟩} u
  dc-inr u = H.refl

  dc-terminal : ∀ {A π} (u : pure ⊑π π) → ty (DT.⊢terminalᶜ {Γ = Γ} {A = A} u) ≅ DT.⊢terminalᶜ {Δ = Δ′} {Γ = Γ ⟨ σ ⟩ᶜ} {A = A ⟨ σ ⟩} u
  dc-terminal u = H.refl

  dc-initial : ∀ {A π} (u : pure ⊑π π) → ty (DT.⊢initialᶜ {Γ = Γ} {A = A} u) ≅ DT.⊢initialᶜ {Δ = Δ′} {Γ = Γ ⟨ σ ⟩ᶜ} {A = A ⟨ σ ⟩} u
  dc-initial u = H.refl

  dc-apply : ∀ {A B} → ty (DT.⊢applyᶜ {Γ = Γ} {A = A} {B = B}) ≅ DT.⊢applyᶜ {Δ = Δ′} {Γ = Γ ⟨ σ ⟩ᶜ} {A = A ⟨ σ ⟩} {B = B ⟨ σ ⟩}
  dc-apply {A} {B} =
    H.trans (tyU (DT.z+qz {m = m} {Δ = Δ} Many) _)
            (H.sym (subst-≅ (λ U → Δ′ ⊩ Γ ⟨ σ ⟩ᶜ ⊢[ U ] applyᶜ (A ⟨ σ ⟩) (B ⟨ σ ⟩) ∷ _ ! pure) (DT.z+qz {m = k} {Δ = Δ′} Many) _))

  dc-applyEff : ∀ {π A B} → ty (DT.⊢applyEffᶜ {Γ = Γ} {π = π} {A = A} {B = B}) ≅ DT.⊢applyEffᶜ {Δ = Δ′} {Γ = Γ ⟨ σ ⟩ᶜ} {π = π} {A = A ⟨ σ ⟩} {B = B ⟨ σ ⟩}
  dc-applyEff {π} {A} {B} =
    H.trans (tyU (DT.z+qz {m = m} {Δ = Δ} Many) _)
            (H.sym (subst-≅ (λ U → Δ′ ⊩ Γ ⟨ σ ⟩ᶜ ⊢[ U ] applyEffᶜ π (A ⟨ σ ⟩) (B ⟨ σ ⟩) ∷ _ ! pure) (DT.z+qz {m = k} {Δ = Δ′} Many) _))

  -- A functor's layer: the binder's type is the substituted layer.
  dc-in : ∀ {F} (wf : WFFun Δ F) → ty (DT.⊢inᶜ {Γ = Γ} wf) ≅ DT.⊢inᶜ {Δ = Δ′} {Γ = Γ ⟨ σ ⟩ᶜ} (W wf)
  dc-in {F} wf = go (TS.⟦⟧F-⟨⟩ σ F (μ F))
    where
      go : ∀ {X} (e : X ≡ ⟦ F ⟨ σ ⟩F ⟧F (μ (F ⟨ σ ⟩F)))
         → ⊢lam {Γ = Γ ⟨ σ ⟩ᶜ} {A = X} _ (⊢roll (W wf) (TS.retypeᵗ σ rσ e (⊢var zero)))
           ≅ DT.⊢inᶜ {Δ = Δ′} {Γ = Γ ⟨ σ ⟩ᶜ} (W wf)
      go refl = H.refl

  dc-out : ∀ {F} (wf : WFFun Δ F) → ty (DT.⊢outᶜ {Γ = Γ} wf) ≅ DT.⊢outᶜ {Δ = Δ′} {Γ = Γ ⟨ σ ⟩ᶜ} (W wf)
  dc-out {F} wf = go (sym (TS.⟦⟧F-⟨⟩ σ F (ν F pureᶠ)))
    where
      go : ∀ {Y} (e : ⟦ F ⟨ σ ⟩F ⟧F (ν (F ⟨ σ ⟩F) pureᶠ) ≡ Y)
         → ⊢lam {Γ = Γ ⟨ σ ⟩ᶜ} _ (TS.retypeᵗ σ rσ e (⊢out (W wf) (⊢var zero)))
           ≅ DT.⊢outᶜ {Δ = Δ′} {Γ = Γ ⟨ σ ⟩ᶜ} (W wf)
      go refl = H.refl

  dc-outAct : ∀ {F} (wf : WFFun Δ F) → ty (DT.⊢outActᶜ {Γ = Γ} wf) ≅ DT.⊢outActᶜ {Δ = Δ′} {Γ = Γ ⟨ σ ⟩ᶜ} (W wf)
  dc-outAct {F} wf = go (sym (TS.⟦⟧F-⟨⟩ σ F (ν F actᶠ)))
    where
      go : ∀ {Y} (e : ⟦ F ⟨ σ ⟩F ⟧F (ν (F ⟨ σ ⟩F) actᶠ) ≡ Y)
         → ⊢lam {Γ = Γ ⟨ σ ⟩ᶜ} _ (⊢lam _ (TS.retypeᵗ σ rσ e (⊢out (W wf) (⊢var (suc zero)))))
           ≅ DT.⊢outActᶜ {Δ = Δ′} {Γ = Γ ⟨ σ ⟩ᶜ} (W wf)
      go refl = H.refl

  -- The combinators with arms: the arms are weakened (`ty-wk`), the rest is
  -- the combinator's own structure.
  dc-compose : ∀ {Ψ₁ Ψ₂ A B C π₁ π₂ π f g} (le : π₂ ·p π₁ ⊑π π)
                 (df : Δ ⊩ Γ ⊢[ Ψ₁ ] f ∷ B ⇒[ mk-kind Many π₁ ] C ! pure) (dg : Δ ⊩ Γ ⊢[ Ψ₂ ] g ∷ A ⇒[ mk-kind Many π₂ ] B ! pure)
             → ty (DT.⊢composeᶜ le df dg) ≅ DT.⊢composeᶜ {Δ = Δ′} le (ty df) (ty dg)
  dc-compose {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {g = g} le df dg =
    H.trans (tyU (DT.compose-use {m = m} {Δ = Δ} Ψ₁ Ψ₂) _)
      (H.trans (c-let refl (cong (λ x → let′ Many x _) (⟪⟫-wk σ g)) H.refl (c-let (⟪⟫-wk σ g) refl (ty-wk dg) H.refl))
               (H.sym (substU-≅ (DT.compose-use {m = k} {Δ = Δ′} Ψ₁ Ψ₂) _)))

  dc-pair : ∀ {Ψ₁ Ψ₂ A B C π₁ π₂ π f g} (le : π₁ ·p π₂ ⊑π π)
              (df : Δ ⊩ Γ ⊢[ Ψ₁ ] f ∷ A ⇒[ mk-kind Many π₁ ] B ! pure) (dg : Δ ⊩ Γ ⊢[ Ψ₂ ] g ∷ A ⇒[ mk-kind Many π₂ ] C ! pure)
          → ty (DT.⊢pairᶜ le df dg) ≅ DT.⊢pairᶜ {Δ = Δ′} le (ty df) (ty dg)
  dc-pair {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {g = g} le df dg =
    H.trans (tyU (DT.pair-use {m = m} {Δ = Δ} Ψ₁ Ψ₂) _)
      (H.trans (c-let refl (cong (λ x → let′ One x _) (⟪⟫-wk σ g)) H.refl (c-let (⟪⟫-wk σ g) refl (ty-wk dg) H.refl))
               (H.sym (substU-≅ (DT.pair-use {m = k} {Δ = Δ′} Ψ₁ Ψ₂) _)))

  dc-case : ∀ {Ψ₁ Ψ₂ A B C π f g}
              (df : Δ ⊩ Γ ⊢[ Ψ₁ ] f ∷ A ⇒[ mk-kind Many π ] C ! pure) (dg : Δ ⊩ Γ ⊢[ Ψ₂ ] g ∷ B ⇒[ mk-kind Many π ] C ! pure)
          → ty (DT.⊢caseᶜ df dg) ≅ DT.⊢caseᶜ {Δ = Δ′} (ty df) (ty dg)
  dc-case {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {g = g} df dg =
    H.trans (tyU (DT.case-use {m = m} {Δ = Δ} Ψ₁ Ψ₂) _)
      (H.trans (c-let refl (cong (λ x → let′ One x _) (⟪⟫-wk σ g)) H.refl (c-let (⟪⟫-wk σ g) refl (ty-wk dg) H.refl))
               (H.sym (substU-≅ (DT.case-use {m = k} {Δ = Δ′} Ψ₁ Ψ₂) _)))

  dc-curry : ∀ {Ψ A B C π₀ π f} (u₀ : pure ⊑π π₀) (df : Δ ⊩ Γ ⊢[ Ψ ] f ∷ (A * B) ⇒[ mk-kind Many π ] C ! pure)
           → ty (DT.⊢curryᶜ u₀ df) ≅ DT.⊢curryᶜ {Δ = Δ′} u₀ (ty df)
  dc-curry {Ψ = Ψ} u₀ df = H.trans (tyU (DT.curry-use {m = m} {Δ = Δ} Ψ) _) (H.sym (substU-≅ (DT.curry-use {m = k} {Δ = Δ′} Ψ) _))

  dc-loop : ∀ {Ψ A B c} (dc : Δ ⊩ Γ ⊢[ Ψ ] c ∷ A ⇒[ mk-kind Many act ] (B + A) ! pure)
          → ty (DT.⊢loopᶜ dc) ≅ DT.⊢loopᶜ {Δ = Δ′} (ty dc)
  dc-loop {Ψ = Ψ} dc = H.trans (tyU (DT.loop-use {m = m} {Δ = Δ} Ψ) _) (H.sym (substU-≅ (DT.loop-use {m = k} {Δ = Δ′} Ψ) _))

  dc-effApp : ∀ {Ψ₁ Ψ₂ π A B f x} (df : Δ ⊩ Γ ⊢[ Ψ₁ ] f ∷ A ⇒[ mk-kind Many π ] B ! pure) (dx : Δ ⊩ Γ ⊢[ Ψ₂ ] x ∷ A ! pure)
            → ty (DT.⊢effAppᶜ df dx) ≅ DT.⊢effAppᶜ {Δ = Δ′} (ty df) (ty dx)
  dc-effApp {f = f} {x = x} df dx =
    c-lam (cong₂ app (⟪⟫-wk σ f) (⟪⟫-wk σ x)) (c-app (⟪⟫-wk σ f) (⟪⟫-wk σ x) (ty-wk df) (ty-wk dx))

  -- The fold: the algebra is at the substituted layer type; an algebra `X`
  -- related to the substituted one gives the substituted fold.
  dc-cata : ∀ {Ψ F A π alg alg′} (wf : WFFun Δ F) (da : Δ ⊩ Γ ⊢[ Ψ ] alg ∷ ⟦ F ⟧F A ⇒[ mk-kind Many π ] A ! pure)
              {X : Δ′ ⊩ Γ ⟨ σ ⟩ᶜ ⊢[ Ψ ] alg′ ∷ ⟦ F ⟨ σ ⟩F ⟧F (A ⟨ σ ⟩) ⇒[ mk-kind Many π ] A ⟨ σ ⟩ ! pure}
          → alg′ ≡ alg ⟪ σ ⟫ₜ → X ≅ ty da → ty (DT.⊢cataᶜ wf da) ≅ DT.⊢cataᶜ {Δ = Δ′} (W wf) X
  dc-cata {Ψ = Ψ} {F = F} {A = A} {π = π} wf da e X≅ =
    H.trans (tyU (DT.cata-use {m = m} {Δ = Δ} Ψ) _)
            (H.trans (go (TS.⟦⟧F-⟨⟩ σ F A) (sym e) (H.sym X≅)) (H.sym (substU-≅ (DT.cata-use {m = k} {Δ = Δ′} Ψ) _)))
    where
      go : ∀ {Ψ X₀} (eX : X₀ ≡ ⟦ F ⟨ σ ⟩F ⟧F (A ⟨ σ ⟩)) {a₁ a₂}
             {d₁ : Δ′ ⊩ Γ ⟨ σ ⟩ᶜ ⊢[ Ψ ] a₁ ∷ X₀ ⇒[ mk-kind Many π ] A ⟨ σ ⟩ ! pure}
             {d₂ : Δ′ ⊩ Γ ⟨ σ ⟩ᶜ ⊢[ Ψ ] a₂ ∷ ⟦ F ⟨ σ ⟩F ⟧F (A ⟨ σ ⟩) ⇒[ mk-kind Many π ] A ⟨ σ ⟩ ! pure}
         → a₁ ≡ a₂ → d₁ ≅ d₂
         → ⊢let d₁ (⊢lam 1≤ω (⊢fold (W wf) (TS.retypeᵗ σ rσ (cong (λ Y → Y ⇒[ mk-kind Many π ] A ⟨ σ ⟩) eX) (⊢var (suc zero))) (⊢var zero)))
           ≅ ⊢let d₂ (⊢lam 1≤ω (⊢fold (W wf) (⊢var (suc zero)) (⊢var zero)))
      go refl refl H.refl = H.refl

  -- Weakening respects `≅`.
  wk-≅ : ∀ {Ψ B t t′ T T′ π} {d : Δ′ ⊩ Γ ⟨ σ ⟩ᶜ ⊢[ Ψ ] t ∷ T ! π} {d′ : Δ′ ⊩ Γ ⟨ σ ⟩ᶜ ⊢[ Ψ ] t′ ∷ T′ ! π}
       → t ≡ t′ → T ≡ T′ → d ≅ d′ → TM.wk-⊢ {B = B} d ≅ TM.wk-⊢ {B = B} d′
  wk-≅ refl refl H.refl = H.refl

  -- The unfold: likewise for the coalgebra.
  dc-ana : ∀ {Ψ F A π₀ φ c c′} (u₀ : pure ⊑π π₀) (wf : WFFun Δ F) (dc : Δ ⊩ Γ ⊢[ Ψ ] c ∷ A ⇒[ mk-kind Many (fin φ) ] ⟦ F ⟧F A ! pure)
             {X : Δ′ ⊩ Γ ⟨ σ ⟩ᶜ ⊢[ Ψ ] c′ ∷ A ⟨ σ ⟩ ⇒[ mk-kind Many (fin φ) ] ⟦ F ⟨ σ ⟩F ⟧F (A ⟨ σ ⟩) ! pure}
         → c′ ≡ c ⟪ σ ⟫ₜ → X ≅ ty dc → ty (DT.⊢anaᶜ u₀ wf dc) ≅ DT.⊢anaᶜ {Δ = Δ′} u₀ (W wf) X
  dc-ana {Ψ = Ψ} {F = F} {A = A} {φ = φ} {c = c} u₀ wf dc e X≅ =
    c-lam tm
      (H.trans (tyUf (One ∷_) (+ᵘ-identityʳ (Many *ᵘ Ψ)) (⊢sub-eff u₀ (⊢unfold wf (DT.wk-⊢′ A dc) (⊢var {Γ = Γ ▸ A} zero))))
        (H.trans (c-sub-eff tm′
                   (c-unfold t₁ refl
                     (H.trans (rtᵗ-≅ _ _) (H.trans (ty-wk dc) (wk-≅ (sym e) (cong (λ Y → A ⟨ σ ⟩ ⇒[ mk-kind Many (fin φ) ] Y) (TS.⟦⟧F-⟨⟩ σ F A)) (H.sym X≅))))
                     H.refl))
                 (H.sym (substUf-≅ (One ∷_) _ _))))
    where
      t₁ = trans (⟪⟫-wk σ c) (cong wk (sym e))
      tm′ = cong (λ u → unfold (F ⟨ σ ⟩F) u (var zero)) t₁
      tm = tm′
