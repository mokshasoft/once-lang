{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecCore.Env — related environments (plan 0.121 §3.5).
--
-- Both meanings run over one slot per variable, empty where unused: the
-- instance's over the instantiated context at no variable, the Spec's over
-- the context at the instance. `EnvR`: the used variables' values related,
-- at the instance's types. Forgetting values (`restrict`), reading one
-- (`lookup`) and binding one keep environments related.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)
open import Once.Spec.Numerics using (TargetNum)

module Once.Adequacy.SpecCore.Env (Σ : Signature) {s : ℕ} (S : Defs s) (fmt : TargetNum) where

open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Spec.Grade using (Zero; One; Many; 0≤q; 1≤1; 1≤ω; ω≤ω)
import Once.Spec.Grade as SG
import Once.Spec.Context as SCx
open SCx using (Ctx; ∅; _▸_; Usage; []; _∷_; _⊑ᵘ_; _⊑∷_; _+ᵘ_; _*ᵘ_)
import Once.Spec.Type as ST
open import Once.Spec.Core.Program Σ using (noVars)
import Once.Spec.Core.Meaning Σ fmt S as SM
import Once.Metatheory.Coherence.Env Σ fmt S as CE
open import Once.Metatheory.TermModel.Usage using (⊑ᵘ-+ˡ; ⊑ᵘ-+ʳ; ⊑ᵘ-trans; ⊑ᵘ-*One; ⊑ᵘ-*Many)
open import Once.Adequacy.SpecCore.Index
open import Once.Adequacy.SpecCore.Value Σ

------------------------------------------------------------------------
-- Environments
------------------------------------------------------------------------

module _ {m} (σ : ST.TySub m 0) where

  -- the instance's environment: the instantiated context, at no variable
  LEnv : ∀ {n} → Ctx m n → Usage n → Set
  LEnv Γ Ψ = SM.Env noVars (Γ SCx.⟨ σ ⟩ᶜ) Ψ

  EnvR : ∀ {n} (Γ : Ctx m n) (Ψ : Usage n) → LEnv Γ Ψ → SM.Env σ Γ Ψ → Set
  EnvR ∅       []         _       _         = ⊤
  EnvR (Γ ▸ A) (Zero ∷ Ψ) (γ , _) (γ′ , _)  = EnvR Γ Ψ γ γ′
  EnvR (Γ ▸ A) (One  ∷ Ψ) (γ , x) (γ′ , x′) = EnvR Γ Ψ γ γ′ × ValR (g⟨⟩ noVars (A ST.⟨ σ ⟩)) x x′
  EnvR (Γ ▸ A) (Many ∷ Ψ) (γ , x) (γ′ , x′) = EnvR Γ Ψ γ γ′ × ValR (g⟨⟩ noVars (A ST.⟨ σ ⟩)) x x′

  -- The type of a variable, looked up on both sides.
  GR-lookup : ∀ {n} (Γ : Ctx m n) (i : Fin n)
            → GR (SCx.lookup (Γ SCx.⟨ σ ⟩ᶜ) i ST.⟨ noVars ⟩) (SCx.lookup Γ i ST.⟨ σ ⟩)
  GR-lookup (Γ ▸ A) zero    = g⟨⟩ noVars (A ST.⟨ σ ⟩)
  GR-lookup (Γ ▸ A) (suc i) = GR-lookup Γ i

  lookup-R : ∀ {n} (Γ : Ctx m n) (i : Fin n) {γ γ′}
           → EnvR Γ (SCx.singleUse i One) γ γ′
           → ValR (GR-lookup Γ i) (SM.lookupᵛ noVars (Γ SCx.⟨ σ ⟩ᶜ) i γ) (SM.lookupᵛ σ Γ i γ′)
  lookup-R (Γ ▸ A) zero    (_ , r) = r
  lookup-R (Γ ▸ A) (suc i) r       = lookup-R Γ i r

  -- Forgetting the values a part does not use.
  restrict-R : ∀ {n} {Γ : Ctx m n} {Ψ Ψ′ : Usage n} (p : Ψ′ ⊑ᵘ Ψ) {γ γ′}
             → EnvR Γ Ψ γ γ′ → EnvR Γ Ψ′ (SM.restrict noVars p γ) (SM.restrict σ p γ′)
  restrict-R {Γ = ∅} [] r = tt
  restrict-R {Γ = Γ ▸ A} {Zero ∷ Ψ} (0≤q ⊑∷ p) r       = restrict-R {Γ = Γ} p r
  restrict-R {Γ = Γ ▸ A} {One  ∷ Ψ} (0≤q ⊑∷ p) (r , _) = restrict-R {Γ = Γ} p r
  restrict-R {Γ = Γ ▸ A} {Many ∷ Ψ} (0≤q ⊑∷ p) (r , _) = restrict-R {Γ = Γ} p r
  restrict-R {Γ = Γ ▸ A} (1≤1 ⊑∷ p) (r , v) = restrict-R {Γ = Γ} p r , v
  restrict-R {Γ = Γ ▸ A} (1≤ω ⊑∷ p) (r , v) = restrict-R {Γ = Γ} p r , v
  restrict-R {Γ = Γ ▸ A} (ω≤ω ⊑∷ p) (r , v) = restrict-R {Γ = Γ} p r , v

  -- The Spec meaning forgets by its own `envˡ`/`envʳ`/`env*One`/`env*Many`
  -- (D335); each is `restrict` along the usage order (`Coherence.Env`).
  restrict-R≡ : ∀ {n} {Γ : Ctx m n} {Ψ Ψ′ : Usage n} (p : Ψ′ ⊑ᵘ Ψ) {γ γ′ δ δ′}
              → δ ≡ SM.restrict noVars p γ → δ′ ≡ SM.restrict σ p γ′ → EnvR Γ Ψ γ γ′ → EnvR Γ Ψ′ δ δ′
  restrict-R≡ {Γ = Γ} p refl refl e = restrict-R {Γ = Γ} p e

  envˡ-R : ∀ {n} {Γ : Ctx m n} (Φ₁ Φ₂ : Usage n) {γ γ′}
         → EnvR Γ (Φ₁ +ᵘ Φ₂) γ γ′ → EnvR Γ Φ₁ (SM.envˡ noVars Φ₁ Φ₂ γ) (SM.envˡ σ Φ₁ Φ₂ γ′)
  envˡ-R {Γ = Γ} Φ₁ Φ₂ {γ} {γ′} =
    restrict-R≡ {Γ = Γ} (⊑ᵘ-+ˡ Φ₁ Φ₂) (CE.envˡ-restrict noVars Φ₁ Φ₂ γ) (CE.envˡ-restrict σ Φ₁ Φ₂ γ′)

  envʳ-R : ∀ {n} {Γ : Ctx m n} (Φ₁ Φ₂ : Usage n) {γ γ′}
         → EnvR Γ (Φ₁ +ᵘ Φ₂) γ γ′ → EnvR Γ Φ₂ (SM.envʳ noVars Φ₁ Φ₂ γ) (SM.envʳ σ Φ₁ Φ₂ γ′)
  envʳ-R {Γ = Γ} Φ₁ Φ₂ {γ} {γ′} =
    restrict-R≡ {Γ = Γ} (⊑ᵘ-+ʳ Φ₁ Φ₂) (CE.envʳ-restrict noVars Φ₁ Φ₂ γ) (CE.envʳ-restrict σ Φ₁ Φ₂ γ′)

  env*One-envʳ-R : ∀ {n} {Γ : Ctx m n} (Φ₁ Φ₂ : Usage n) {γ γ′}
                 → EnvR Γ (Φ₁ +ᵘ One *ᵘ Φ₂) γ γ′
                 → EnvR Γ Φ₂ (SM.env*One noVars Φ₂ (SM.envʳ noVars Φ₁ (One *ᵘ Φ₂) γ))
                              (SM.env*One σ Φ₂ (SM.envʳ σ Φ₁ (One *ᵘ Φ₂) γ′))
  env*One-envʳ-R {Γ = Γ} Φ₁ Φ₂ {γ} {γ′} =
    restrict-R≡ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*One Φ₂) (⊑ᵘ-+ʳ Φ₁ (One *ᵘ Φ₂)))
      (CE.env*One-envʳ-restrict noVars Φ₁ Φ₂ γ) (CE.env*One-envʳ-restrict σ Φ₁ Φ₂ γ′)

  env*Many-envʳ-R : ∀ {n} {Γ : Ctx m n} (Φ₁ Φ₂ : Usage n) {γ γ′}
                  → EnvR Γ (Φ₁ +ᵘ Many *ᵘ Φ₂) γ γ′
                  → EnvR Γ Φ₂ (SM.env*Many noVars Φ₂ (SM.envʳ noVars Φ₁ (Many *ᵘ Φ₂) γ))
                               (SM.env*Many σ Φ₂ (SM.envʳ σ Φ₁ (Many *ᵘ Φ₂) γ′))
  env*Many-envʳ-R {Γ = Γ} Φ₁ Φ₂ {γ} {γ′} =
    restrict-R≡ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Φ₂) (⊑ᵘ-+ʳ Φ₁ (Many *ᵘ Φ₂)))
      (CE.env*Many-envʳ-restrict noVars Φ₁ Φ₂ γ) (CE.env*Many-envʳ-restrict σ Φ₁ Φ₂ γ′)

  env*Many-envˡ-R : ∀ {n} {Γ : Ctx m n} (Φ₁ Φ₂ : Usage n) {γ γ′}
                  → EnvR Γ (Many *ᵘ Φ₁ +ᵘ Φ₂) γ γ′
                  → EnvR Γ Φ₁ (SM.env*Many noVars Φ₁ (SM.envˡ noVars (Many *ᵘ Φ₁) Φ₂ γ))
                               (SM.env*Many σ Φ₁ (SM.envˡ σ (Many *ᵘ Φ₁) Φ₂ γ′))
  env*Many-envˡ-R {Γ = Γ} Φ₁ Φ₂ {γ} {γ′} =
    restrict-R≡ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Φ₁) (⊑ᵘ-+ˡ (Many *ᵘ Φ₁) Φ₂))
      (CE.env*Many-envˡ-restrict noVars Φ₁ Φ₂ γ) (CE.env*Many-envˡ-restrict σ Φ₁ Φ₂ γ′)

  -- Binding a variable at a usage.
  bind-env-R : ∀ {n} {Γ : Ctx m n} {Ψ} (A : ST.Ty m) q {γ γ′ x x′}
             → EnvR Γ Ψ γ γ′ → ValR (g⟨⟩ noVars (A ST.⟨ σ ⟩)) x x′
             → EnvR (Γ ▸ A) (q ∷ Ψ) (γ , SM.slot q x) (γ′ , SM.slot q x′)
  bind-env-R A Zero r v = r
  bind-env-R A One  r v = r , v
  bind-env-R A Many r v = r , v
