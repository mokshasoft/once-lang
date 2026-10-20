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
open import Once.Lang.Contract using (ISig)
import Once.Lang.Core.PolyTy as LP
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Numerics using (TargetNum)

module Once.Adequacy.SpecCore.Env {Fs : ISig} {s : ℕ} (S : LP.Sig Fs s) (Σ : Signature) (fmt : TargetNum) where

open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Fin using (Fin; zero; suc)

import Once.Lang.Type.Grade as LG
import Once.Spec.Grade as SG
import Once.Lang.Context as LC
import Once.Spec.Context as SCx
import Once.Spec.Type as ST
import Once.Lang.Environment as LEnv
import Once.Lang.Core.PolyTyping S as PT
import Once.Lang.Core.Meaning S as GM
open import Once.Adequacy.SpecCore.Schema using (defsS)
import Once.Spec.Core.Meaning Σ fmt (defsS S) as SM
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

module _ {m} {σ : LP.GSub m} {σ′ : ST.TySub m 0} (g : InstG σ σ′) where

  EnvR : ∀ {n} {Γ : PT.PCtx m n} {Γ′ Ψ Φ} → CR S Γ Γ′ → UR Ψ Φ → GM.Env (Γ PT.⟪ σ ⟫ᶜ) Ψ → SM.Env σ′ Γ′ Φ → Set
  EnvR cr-∅ ur-[] _ _ = ⊤
  EnvR (cr-▸ c a) (ur-∷ qr-zero u) γ        (γ′ , _)  = EnvR c u γ γ′
  EnvR (cr-▸ c a) (ur-∷ qr-one  u) (γ , x)  (γ′ , x′) = EnvR c u γ γ′ × ValR (GR-inst a g) x x′
  EnvR (cr-▸ c a) (ur-∷ qr-many u) (γ , x)  (γ′ , x′) = EnvR c u γ γ′ × ValR (GR-inst a g) x x′

  -- The type of a variable, looked up on both sides.
  GR-lookup : ∀ {n} {Γ : PT.PCtx m n} {Γ′} → CR S Γ Γ′ → (i : Fin n)
            → GR (LC.lookup (Γ PT.⟪ σ ⟫ᶜ) i) (SCx.lookup Γ′ i ST.⟨ σ′ ⟩)
  GR-lookup (cr-▸ c a) zero    = GR-inst a g
  GR-lookup (cr-▸ c a) (suc i) = GR-lookup c i

  lookup-R : ∀ {n} {Γ : PT.PCtx m n} {Γ′} (c : CR S Γ Γ′) (i : Fin n) {γ γ′}
           → EnvR c (ur-single i) γ γ′
           → ValR (GR-lookup c i) (LEnv.lookupᵛUsed (Γ PT.⟪ σ ⟫ᶜ) i γ) (SM.lookupᵛ σ′ Γ′ i γ′)
  lookup-R (cr-▸ c a) zero    (_ , r) = r
  lookup-R (cr-▸ c a) (suc i) r       = lookup-R c i r

  -- Forgetting the values a part does not use.
  restrict-R : ∀ {n} {Γ : PT.PCtx m n} {Γ′ Ψ Ψ′ Φ Φ′} (c : CR S Γ Γ′)
             (p : Ψ′ LC.⊑ᵘ Ψ) (p′ : Φ′ SCx.⊑ᵘ Φ) (u : UR Ψ Φ) (u′ : UR Ψ′ Φ′) {γ γ′}
             → EnvR c u γ γ′
             → EnvR c u′ (LEnv.restrictᵛ {Γ = Γ PT.⟪ σ ⟫ᶜ} p γ) (SM.restrict σ′ p′ γ′)
  restrict-R cr-∅ LC.⊑[] SCx.[] ur-[] ur-[] r = tt
  restrict-R (cr-▸ c a) (LC.z≤z LC.⊑∷ p) (SG.0≤q SCx.⊑∷ p′) (ur-∷ qr-zero u) (ur-∷ qr-zero u′) r =
    restrict-R c p p′ u u′ r
  restrict-R (cr-▸ c a) (LC.z≤o LC.⊑∷ p) (SG.0≤q SCx.⊑∷ p′) (ur-∷ qr-one u) (ur-∷ qr-zero u′) (r , _) =
    restrict-R c p p′ u u′ r
  restrict-R (cr-▸ c a) (LC.z≤m LC.⊑∷ p) (SG.0≤q SCx.⊑∷ p′) (ur-∷ qr-many u) (ur-∷ qr-zero u′) (r , _) =
    restrict-R c p p′ u u′ r
  restrict-R (cr-▸ c a) (LC.o≤o LC.⊑∷ p) (SG.1≤1 SCx.⊑∷ p′) (ur-∷ qr-one u) (ur-∷ qr-one u′) (r , v) =
    restrict-R c p p′ u u′ r , v
  restrict-R (cr-▸ c a) (LC.o≤m LC.⊑∷ p) (SG.1≤ω SCx.⊑∷ p′) (ur-∷ qr-many u) (ur-∷ qr-one u′) (r , v) =
    restrict-R c p p′ u u′ r , v
  restrict-R (cr-▸ c a) (LC.m≤m LC.⊑∷ p) (SG.ω≤ω SCx.⊑∷ p′) (ur-∷ qr-many u) (ur-∷ qr-many u′) (r , v) =
    restrict-R c p p′ u u′ r , v

  -- Binding a variable at a usage.
  bind-env-R : ∀ {n} {Γ : PT.PCtx m n} {Γ′ Ψ Φ A A′ q q′} (c : CR S Γ Γ′) (a : PTR A A′) (u : UR Ψ Φ) (qq : QR q q′)
               {γ γ′ x x′}
             → EnvR c u γ γ′ → ValR (GR-inst a g) x x′
             → EnvR (cr-▸ {q = LG.Many} c a) (ur-∷ qq u)
                    (LEnv.bindᵛ {Γ = Γ PT.⟪ σ ⟫ᶜ} {A = A LP.⟪ σ ⟫} q γ x) (γ′ , SM.slot q′ x′)
  bind-env-R c a u qr-zero r v = r
  bind-env-R c a u qr-one  r v = r , v
  bind-env-R c a u qr-many r v = r , v
