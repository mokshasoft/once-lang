-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecCore.Context — the compiler's contexts and usages as the
-- Spec's (plan 0.121, the core bridge).
--
-- A usage is the same vector of quantities on both sides (`uS`), and every
-- operation the core rules build usages with commutes with it. A context is
-- related entrywise by `TyR`; the compiler's entries also carry the quantity
-- a binder was introduced at, which the Spec's do not.
------------------------------------------------------------------------

import Once.Type.Grade
module Once.Adequacy.SpecCore.Context where


open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym)

import Once.Spec.Grade as LG
import Once.Spec.Grade as SG
import Once.Internal.Context as LC
import Once.Spec.Context as SCx
import Once.Spec.Context as SC
import Once.Spec.Type as ST
open import Once.Adequacy.SpecGrammar.Conv using (qS)
open import Once.Adequacy.SpecCore.Type using (TyR; qS-injective)

------------------------------------------------------------------------
-- Quantities and usages
------------------------------------------------------------------------

+q-S : ∀ p q → qS (p LG.+q q) ≡ qS p SG.+q qS q
+q-S LG.Zero q       = refl
+q-S LG.One  LG.Zero = refl
+q-S LG.One  LG.One  = refl
+q-S LG.One  LG.Many = refl
+q-S LG.Many q       = refl

*q-S : ∀ p q → qS (p LG.*q q) ≡ qS p SG.*q qS q
*q-S LG.Zero q       = refl
*q-S LG.One  LG.Zero = refl
*q-S LG.One  LG.One  = refl
*q-S LG.One  LG.Many = refl
*q-S LG.Many LG.Zero = refl
*q-S LG.Many LG.One  = refl
*q-S LG.Many LG.Many = refl

≤q-S : ∀ p q → (p Once.Type.Grade.≤qᵇ q) ≡ true → qS p SG.≤q qS q
≤q-S LG.Zero q       _ = SG.0≤q
≤q-S LG.One  LG.One  _ = SG.1≤1
≤q-S LG.One  LG.Many _ = SG.1≤ω
≤q-S LG.Many LG.Many _ = SG.ω≤ω
≤q-S LG.One  LG.Zero ()
≤q-S LG.Many LG.Zero ()
≤q-S LG.Many LG.One  ()

≤q-L : ∀ p q → qS p SG.≤q qS q → (p Once.Type.Grade.≤qᵇ q) ≡ true
≤q-L LG.Zero q       _ = refl
≤q-L LG.One  LG.One  _ = refl
≤q-L LG.One  LG.Many _ = refl
≤q-L LG.Many LG.Many _ = refl
≤q-L LG.One  LG.Zero ()
≤q-L LG.Many LG.Zero ()
≤q-L LG.Many LG.One  ()

≤q′-S : ∀ {p q} → p LC.≤q' q → qS p SG.≤q qS q
≤q′-S LC.z≤z = SG.0≤q
≤q′-S LC.z≤o = SG.0≤q
≤q′-S LC.z≤m = SG.0≤q
≤q′-S LC.o≤o = SG.1≤1
≤q′-S LC.o≤m = SG.1≤ω
≤q′-S LC.m≤m = SG.ω≤ω

≤q′-L : ∀ p q → qS p SG.≤q qS q → p LC.≤q' q
≤q′-L LG.Zero LG.Zero _ = LC.z≤z
≤q′-L LG.Zero LG.One  _ = LC.z≤o
≤q′-L LG.Zero LG.Many _ = LC.z≤m
≤q′-L LG.One  LG.One  _ = LC.o≤o
≤q′-L LG.One  LG.Many _ = LC.o≤m
≤q′-L LG.Many LG.Many _ = LC.m≤m
≤q′-L LG.One  LG.Zero ()
≤q′-L LG.Many LG.Zero ()
≤q′-L LG.Many LG.One  ()

-- Plan 0.122: the usages are one (`uS` the identity), the lemmas kept as the
-- front-end bridge reads them.
qS-id : ∀ q → qS q ≡ q
qS-id LG.Zero = refl
qS-id LG.One  = refl
qS-id LG.Many = refl

uS : ∀ {n} → LC.Usage n → SC.Usage n
uS Ψ = Ψ

uS-zero : ∀ {n} → uS (LC.zeroUsage {n}) ≡ SC.zeroUsage
uS-zero = refl

uS-single : ∀ {n} (i : Fin n) q → uS (LC.singleUse i q) ≡ SC.singleUse i (qS q)
uS-single i q = cong (SC.singleUse i) (sym (qS-id q))

uS-+ : ∀ {n} (Ψ Φ : LC.Usage n) → uS (Ψ LC.+ᵘ Φ) ≡ uS Ψ SC.+ᵘ uS Φ
uS-+ Ψ Φ = refl

uS-* : ∀ {n} q (Ψ : LC.Usage n) → uS (q LC.*ᵘ Ψ) ≡ qS q SC.*ᵘ uS Ψ
uS-* q Ψ = cong (SC._*ᵘ Ψ) (sym (qS-id q))

⊑ᵘ-S : ∀ {n} {Ψ Φ : LC.Usage n} → Ψ LC.⊑ᵘ Φ → uS Ψ SC.⊑ᵘ uS Φ
⊑ᵘ-S s = s

⊑ᵘ-L : ∀ {n} (Ψ Φ : LC.Usage n) → uS Ψ SC.⊑ᵘ uS Φ → Ψ LC.⊑ᵘ Φ
⊑ᵘ-L Ψ Φ s = s

uS-injective : ∀ {n} {Ψ Φ : LC.Usage n} → uS Ψ ≡ uS Φ → Ψ ≡ Φ
uS-injective e = e

------------------------------------------------------------------------
-- Contexts
------------------------------------------------------------------------

data CtxR {m} (Δ : ST.KCtx m) : ∀ {n} → SC.Ctx m n → SC.Ctx m n → Set where
  r-∅ : CtxR Δ SC.∅ SC.∅
  r-▸ : ∀ {n} {Γ Γ′ : SC.Ctx m n} {A A′} → CtxR Δ Γ Γ′ → TyR Δ A A′ → CtxR Δ (Γ SC.▸ A) (Γ′ SC.▸ A′)

lookup-R : ∀ {m} {Δ : ST.KCtx m} {n} {Γ Γ′ : SC.Ctx m n} → CtxR Δ Γ Γ′ → ∀ i → TyR Δ (SC.lookup Γ i) (SC.lookup Γ′ i)
lookup-R (r-▸ g a) zero    = a
lookup-R (r-▸ g a) (suc i) = lookup-R g i
