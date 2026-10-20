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

module Once.Adequacy.SpecCore.Context where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

import Once.Lang.Type.Grade as LG
import Once.Spec.Grade as SG
import Once.Lang.Context as LC
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

≤q-S : ∀ p q → (p LG.≤q q) ≡ true → qS p SG.≤q qS q
≤q-S LG.Zero q       _ = SG.0≤q
≤q-S LG.One  LG.One  _ = SG.1≤1
≤q-S LG.One  LG.Many _ = SG.1≤ω
≤q-S LG.Many LG.Many _ = SG.ω≤ω
≤q-S LG.One  LG.Zero ()
≤q-S LG.Many LG.Zero ()
≤q-S LG.Many LG.One  ()

≤q-L : ∀ p q → qS p SG.≤q qS q → (p LG.≤q q) ≡ true
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

uS : ∀ {n} → LC.Usage n → SC.Usage n
uS LC.[]      = SC.[]
uS (q LC.∷ Ψ) = qS q SC.∷ uS Ψ

uS-zero : ∀ {n} → uS (LC.zeroUsage {n}) ≡ SC.zeroUsage
uS-zero {ℕ.zero}  = refl
uS-zero {ℕ.suc n} = cong (SG.Zero SC.∷_) uS-zero

uS-single : ∀ {n} (i : Fin n) q → uS (LC.singleUse i q) ≡ SC.singleUse i (qS q)
uS-single {ℕ.suc n} zero    q = cong (qS q SC.∷_) uS-zero
uS-single {ℕ.suc n} (suc i) q = cong (SG.Zero SC.∷_) (uS-single i q)

uS-+ : ∀ {n} (Ψ Φ : LC.Usage n) → uS (Ψ LC.+ᵘ Φ) ≡ uS Ψ SC.+ᵘ uS Φ
uS-+ LC.[]      LC.[]      = refl
uS-+ (p LC.∷ Ψ) (q LC.∷ Φ) = cong₂ SC._∷_ (+q-S p q) (uS-+ Ψ Φ)

uS-* : ∀ {n} q (Ψ : LC.Usage n) → uS (q LC.*ᵘ Ψ) ≡ qS q SC.*ᵘ uS Ψ
uS-* q LC.[]      = refl
uS-* q (p LC.∷ Ψ) = cong₂ SC._∷_ (*q-S q p) (uS-* q Ψ)

⊑ᵘ-S : ∀ {n} {Ψ Φ : LC.Usage n} → Ψ LC.⊑ᵘ Φ → uS Ψ SC.⊑ᵘ uS Φ
⊑ᵘ-S LC.⊑[]      = SC.[]
⊑ᵘ-S (p LC.⊑∷ s) = ≤q′-S p SC.⊑∷ ⊑ᵘ-S s

⊑ᵘ-L : ∀ {n} (Ψ Φ : LC.Usage n) → uS Ψ SC.⊑ᵘ uS Φ → Ψ LC.⊑ᵘ Φ
⊑ᵘ-L LC.[]      LC.[]      SC.[]       = LC.⊑[]
⊑ᵘ-L (p LC.∷ Ψ) (q LC.∷ Φ) (r SC.⊑∷ s) = ≤q′-L p q r LC.⊑∷ ⊑ᵘ-L Ψ Φ s

uS-injective : ∀ {n} {Ψ Φ : LC.Usage n} → uS Ψ ≡ uS Φ → Ψ ≡ Φ
uS-injective {Ψ = LC.[]}      {LC.[]}      _ = refl
uS-injective {Ψ = p LC.∷ Ψ} {q LC.∷ Φ} e = cons (qS-injective (cong head e)) (uS-injective (cong tail e))
  where
    head : ∀ {n} → SC.Usage (ℕ.suc n) → SG.Quantity
    head (x SC.∷ _) = x
    tail : ∀ {n} → SC.Usage (ℕ.suc n) → SC.Usage n
    tail (_ SC.∷ xs) = xs
    cons : p ≡ q → Ψ ≡ Φ → (p LC.∷ Ψ) ≡ (q LC.∷ Φ)
    cons refl refl = refl

------------------------------------------------------------------------
-- Contexts
------------------------------------------------------------------------

data CtxR {m} (Δ : ST.KCtx m) : ∀ {n} → LC.Ctx n → SC.Ctx m n → Set where
  r-∅ : CtxR Δ LC.∅ SC.∅
  r-▸ : ∀ {n} {Γ : LC.Ctx n} {Γ′ A A′ q} → CtxR Δ Γ Γ′ → TyR Δ A A′ → CtxR Δ (Γ LC., A ^ q) (Γ′ SC.▸ A′)

lookup-R : ∀ {m} {Δ : ST.KCtx m} {n} {Γ : LC.Ctx n} {Γ′} → CtxR Δ Γ Γ′ → ∀ i → TyR Δ (LC.lookup Γ i) (SC.lookup Γ′ i)
lookup-R (r-▸ g a) zero    = a
lookup-R (r-▸ g a) (suc i) = lookup-R g i
