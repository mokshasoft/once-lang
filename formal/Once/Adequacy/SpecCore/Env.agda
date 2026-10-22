{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecCore.Env — related environments (plan 0.121 §3.5).
--
-- Both meanings run over the values of the variables a term USES: the
-- compiler's as the context restricted to the usage (`Γ ↾ Ψ`), the Spec's as
-- one slot per variable, empty where unused. `EnvR`: the used variables'
-- values related, at the instance's types. Forgetting values (`restrict`),
-- reading one (`lookup`) and binding one keep environments related.
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

import Once.Spec.Grade as LG
import Once.Spec.Grade as SG
import Once.Internal.Context as LC
import Once.Spec.Context as SCx
import Once.Spec.Type as ST
import Once.Internal.Environment as LEnv
import Once.Internal.Core.Meaning Σ S as GM
import Once.Spec.Core.Meaning Σ fmt S as SM
import Once.Metatheory.Coherence.Env Σ fmt S as CE
open import Once.Metatheory.TermModel.Usage using (⊑ᵘ-+ˡ; ⊑ᵘ-+ʳ; ⊑ᵘ-trans; ⊑ᵘ-*One; ⊑ᵘ-*Many)
open import Once.Adequacy.SpecCore.Index
open import Once.Adequacy.SpecCore.Value Σ

------------------------------------------------------------------------
-- Usages
------------------------------------------------------------------------

ur-zero : ∀ {n} → UR (LC.zeroUsage {n}) SCx.zeroUsage
ur-zero {ℕ.zero}  = ur-[]
ur-zero {ℕ.suc n} = ur-∷ qr-zero ur-zero

ur-single : ∀ {n} (i : Fin n) → UR (LC.singleUse i LG.One) (SCx.singleUse i SG.One)
ur-single {ℕ.suc n} zero    = ur-∷ qr-one ur-zero
ur-single {ℕ.suc n} (suc i) = ur-∷ qr-zero (ur-single i)

------------------------------------------------------------------------
-- Environments
------------------------------------------------------------------------

module _ {m} (σ : ST.TySub m 0) where

  EnvR : ∀ {n} (Γ : SCx.Ctx m n) {Ψ Φ} → UR Ψ Φ → GM.Env (Γ SCx.⟨ σ ⟩ᶜ) Ψ → SM.Env σ Γ Φ → Set
  EnvR SCx.∅       ur-[] _ _ = ⊤
  EnvR (Γ SCx.▸ A) (ur-∷ qr-zero u) γ        (γ′ , _)  = EnvR Γ u γ γ′
  EnvR (Γ SCx.▸ A) (ur-∷ qr-one  u) (γ , x)  (γ′ , x′) = EnvR Γ u γ γ′ × ValR (gr (A ST.⟨ σ ⟩)) x x′
  EnvR (Γ SCx.▸ A) (ur-∷ qr-many u) (γ , x)  (γ′ , x′) = EnvR Γ u γ γ′ × ValR (gr (A ST.⟨ σ ⟩)) x x′

  -- The type of a variable, looked up on both sides.
  GR-lookup : ∀ {n} (Γ : SCx.Ctx m n) (i : Fin n)
            → GR (SCx.lookup (Γ SCx.⟨ σ ⟩ᶜ) i) (SCx.lookup Γ i ST.⟨ σ ⟩)
  GR-lookup (Γ SCx.▸ A) zero    = gr (A ST.⟨ σ ⟩)
  GR-lookup (Γ SCx.▸ A) (suc i) = GR-lookup Γ i

  lookup-R : ∀ {n} (Γ : SCx.Ctx m n) (i : Fin n) {γ γ′}
           → EnvR Γ (ur-single i) γ γ′
           → ValR (GR-lookup Γ i) (LEnv.lookupᵛUsed (Γ SCx.⟨ σ ⟩ᶜ) i γ) (SM.lookupᵛ σ Γ i γ′)
  lookup-R (Γ SCx.▸ A) zero    (_ , r) = r
  lookup-R (Γ SCx.▸ A) (suc i) r       = lookup-R Γ i r

  -- Forgetting the values a part does not use.
  restrict-R : ∀ {n} {Γ : SCx.Ctx m n} {Ψ Ψ′ Φ Φ′} 
             (p : Ψ′ LC.⊑ᵘ Ψ) (p′ : Φ′ SCx.⊑ᵘ Φ) (u : UR Ψ Φ) (u′ : UR Ψ′ Φ′) {γ γ′}
             → EnvR Γ u γ γ′
             → EnvR Γ u′ (LEnv.restrictᵛ {Γ = Γ SCx.⟨ σ ⟩ᶜ} p γ) (SM.restrict σ p′ γ′)
  restrict-R {Γ = SCx.∅} SCx.[] SCx.[] ur-[] ur-[] r = tt
  restrict-R {Γ = Γ SCx.▸ A} (LC.z≤z SCx.⊑∷ p) (SG.0≤q SCx.⊑∷ p′) (ur-∷ qr-zero u) (ur-∷ qr-zero u′) r =
    restrict-R {Γ = Γ} p p′ u u′ r
  restrict-R {Γ = Γ SCx.▸ A} (LC.z≤o SCx.⊑∷ p) (SG.0≤q SCx.⊑∷ p′) (ur-∷ qr-one u) (ur-∷ qr-zero u′) (r , _) =
    restrict-R {Γ = Γ} p p′ u u′ r
  restrict-R {Γ = Γ SCx.▸ A} (LC.z≤m SCx.⊑∷ p) (SG.0≤q SCx.⊑∷ p′) (ur-∷ qr-many u) (ur-∷ qr-zero u′) (r , _) =
    restrict-R {Γ = Γ} p p′ u u′ r
  restrict-R {Γ = Γ SCx.▸ A} (LC.o≤o SCx.⊑∷ p) (SG.1≤1 SCx.⊑∷ p′) (ur-∷ qr-one u) (ur-∷ qr-one u′) (r , v) =
    restrict-R {Γ = Γ} p p′ u u′ r , v
  restrict-R {Γ = Γ SCx.▸ A} (LC.o≤m SCx.⊑∷ p) (SG.1≤ω SCx.⊑∷ p′) (ur-∷ qr-many u) (ur-∷ qr-one u′) (r , v) =
    restrict-R {Γ = Γ} p p′ u u′ r , v
  restrict-R {Γ = Γ SCx.▸ A} (LC.m≤m SCx.⊑∷ p) (SG.ω≤ω SCx.⊑∷ p′) (ur-∷ qr-many u) (ur-∷ qr-many u′) (r , v) =
    restrict-R {Γ = Γ} p p′ u u′ r , v

  -- The Spec meaning forgets by its own `envˡ`/`envʳ`/`env*One`/`env*Many`
  -- (D335); each is `restrict` along the usage order (`Coherence.Env`).
  restrict-R≡ : ∀ {n} {Γ : SCx.Ctx m n} {Ψ Ψ′ Φ Φ′} 
              (p : Ψ′ LC.⊑ᵘ Ψ) (p′ : Φ′ SCx.⊑ᵘ Φ) (u : UR Ψ Φ) (u′ : UR Ψ′ Φ′) {γ γ′ γ″}
              → γ″ ≡ SM.restrict σ p′ γ′ → EnvR Γ u γ γ′
              → EnvR Γ u′ (LEnv.restrictᵛ {Γ = Γ SCx.⟨ σ ⟩ᶜ} p γ) γ″
  restrict-R≡ {Γ = Γ} p p′ u u′ refl e = restrict-R {Γ = Γ} p p′ u u′ e

  envˡ-R : ∀ {n} {Γ : SCx.Ctx m n} {Ψ Ψ′ Φ₁ Φ₂}  (p : Ψ′ LC.⊑ᵘ Ψ) (u : UR Ψ (Φ₁ SCx.+ᵘ Φ₂)) (u′ : UR Ψ′ Φ₁) {γ γ′}
         → EnvR Γ u γ γ′ → EnvR Γ u′ (LEnv.restrictᵛ {Γ = Γ SCx.⟨ σ ⟩ᶜ} p γ) (SM.envˡ σ Φ₁ Φ₂ γ′)
  envˡ-R {Γ = Γ} {Φ₁ = Φ₁} {Φ₂} p u u′ {γ′ = γ′} = restrict-R≡ {Γ = Γ} p (⊑ᵘ-+ˡ Φ₁ Φ₂) u u′ (CE.envˡ-restrict σ Φ₁ Φ₂ γ′)

  envʳ-R : ∀ {n} {Γ : SCx.Ctx m n} {Ψ Ψ′ Φ₁ Φ₂}  (p : Ψ′ LC.⊑ᵘ Ψ) (u : UR Ψ (Φ₁ SCx.+ᵘ Φ₂)) (u′ : UR Ψ′ Φ₂) {γ γ′}
         → EnvR Γ u γ γ′ → EnvR Γ u′ (LEnv.restrictᵛ {Γ = Γ SCx.⟨ σ ⟩ᶜ} p γ) (SM.envʳ σ Φ₁ Φ₂ γ′)
  envʳ-R {Γ = Γ} {Φ₁ = Φ₁} {Φ₂} p u u′ {γ′ = γ′} = restrict-R≡ {Γ = Γ} p (⊑ᵘ-+ʳ Φ₁ Φ₂) u u′ (CE.envʳ-restrict σ Φ₁ Φ₂ γ′)

  env*One-envʳ-R : ∀ {n} {Γ : SCx.Ctx m n} {Ψ Ψ′ Φ₁ Φ₂}  (p : Ψ′ LC.⊑ᵘ Ψ)
                   (u : UR Ψ (Φ₁ SCx.+ᵘ SG.One SCx.*ᵘ Φ₂)) (u′ : UR Ψ′ Φ₂) {γ γ′}
                 → EnvR Γ u γ γ′
                 → EnvR Γ u′ (LEnv.restrictᵛ {Γ = Γ SCx.⟨ σ ⟩ᶜ} p γ) (SM.env*One σ Φ₂ (SM.envʳ σ Φ₁ (SG.One SCx.*ᵘ Φ₂) γ′))
  env*One-envʳ-R {Γ = Γ} {Φ₁ = Φ₁} {Φ₂} p u u′ {γ′ = γ′} =
    restrict-R≡ {Γ = Γ} p (⊑ᵘ-trans (⊑ᵘ-*One Φ₂) (⊑ᵘ-+ʳ Φ₁ (SG.One SCx.*ᵘ Φ₂))) u u′ (CE.env*One-envʳ-restrict σ Φ₁ Φ₂ γ′)

  env*Many-envʳ-R : ∀ {n} {Γ : SCx.Ctx m n} {Ψ Ψ′ Φ₁ Φ₂}  (p : Ψ′ LC.⊑ᵘ Ψ)
                    (u : UR Ψ (Φ₁ SCx.+ᵘ SG.Many SCx.*ᵘ Φ₂)) (u′ : UR Ψ′ Φ₂) {γ γ′}
                  → EnvR Γ u γ γ′
                  → EnvR Γ u′ (LEnv.restrictᵛ {Γ = Γ SCx.⟨ σ ⟩ᶜ} p γ) (SM.env*Many σ Φ₂ (SM.envʳ σ Φ₁ (SG.Many SCx.*ᵘ Φ₂) γ′))
  env*Many-envʳ-R {Γ = Γ} {Φ₁ = Φ₁} {Φ₂} p u u′ {γ′ = γ′} =
    restrict-R≡ {Γ = Γ} p (⊑ᵘ-trans (⊑ᵘ-*Many Φ₂) (⊑ᵘ-+ʳ Φ₁ (SG.Many SCx.*ᵘ Φ₂))) u u′ (CE.env*Many-envʳ-restrict σ Φ₁ Φ₂ γ′)

  env*Many-envˡ-R : ∀ {n} {Γ : SCx.Ctx m n} {Ψ Ψ′ Φ₁ Φ₂}  (p : Ψ′ LC.⊑ᵘ Ψ)
                    (u : UR Ψ (SG.Many SCx.*ᵘ Φ₁ SCx.+ᵘ Φ₂)) (u′ : UR Ψ′ Φ₁) {γ γ′}
                  → EnvR Γ u γ γ′
                  → EnvR Γ u′ (LEnv.restrictᵛ {Γ = Γ SCx.⟨ σ ⟩ᶜ} p γ) (SM.env*Many σ Φ₁ (SM.envˡ σ (SG.Many SCx.*ᵘ Φ₁) Φ₂ γ′))
  env*Many-envˡ-R {Γ = Γ} {Φ₁ = Φ₁} {Φ₂} p u u′ {γ′ = γ′} =
    restrict-R≡ {Γ = Γ} p (⊑ᵘ-trans (⊑ᵘ-*Many Φ₁) (⊑ᵘ-+ˡ (SG.Many SCx.*ᵘ Φ₁) Φ₂)) u u′ (CE.env*Many-envˡ-restrict σ Φ₁ Φ₂ γ′)

  -- Binding a variable at a usage.
  bind-env-R : ∀ {n} {Γ : SCx.Ctx m n} {Ψ Φ q q′} (A : ST.Ty m) (u : UR Ψ Φ) (qq : QR q q′)
               {γ γ′ x x′}
             → EnvR Γ u γ γ′ → ValR (gr (A ST.⟨ σ ⟩)) x x′
             → EnvR (Γ SCx.▸ A) (ur-∷ qq u)
                    (LEnv.bindᵛ {Γ = Γ SCx.⟨ σ ⟩ᶜ} {A = A ST.⟨ σ ⟩} q γ x) (γ′ , SM.slot q′ x′)
  bind-env-R A u qr-zero r v = r
  bind-env-R A u qr-one  r v = r , v
  bind-env-R A u qr-many r v = r , v
