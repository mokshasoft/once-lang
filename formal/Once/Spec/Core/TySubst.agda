-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Core.TySubst — plan 0.103 phase 5: SUBSTITUTION OF OPEN TYPES,
-- the vocabulary of the type-substitution lemma (D303).
--
--     Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π   ⟹   Δ′ ⊩ Γ⟨σ⟩ ⊢[ Ψ ] t⟨σ⟩ₜ ∷ A⟨σ⟩ ! π
--
-- for every substitution `σ` that respects the kinds (`KSub`). The lemma is
-- STATED in `Once.Spec.Core.TermModel` (`ty-subst-⊢`, part of the
-- Spec's metatheory, `Once.Spec.Metatheory`) and PROVED in `Once.Metatheory.TySubst`;
-- this module holds the definitions the statement needs, plus one small fact
-- `Spec.Core.Abstract` reads (`<:ₚ-refl`).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
import Once.Spec.Type
import Once.Type
open import Once.Spec.Core.PolyTy using (Sig)

open import Once.Spec.Contract using (ISig)
module Once.Spec.Core.TySubst {Fs : ISig} {s : ℕ} (S : Sig Fs s) where

open import Data.Nat using (suc)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong; cong₂)

import Once.Type as T
open import Once.Spec.Type.Grade using (Purity; pure; mk-kind; Many; One)
open import Once.Metatheory.SubLaws using (⊑π-refl)
open import Once.Spec.Context using (Usage; zeroUsage; singleUse)
open import Once.Spec.Core.PolyTy
open Schema using (type)
open import Once.Spec.Core.PolyTyping S
import Once.Spec.Core.Syntax S as G
open G using (primDom; primCod)

------------------------------------------------------------------------
-- Substitution respecting kinds
------------------------------------------------------------------------

-- A substitution RESPECTS the kinds when it sends every base variable of `Δ`
-- to a type that is base under `Δ′`.
KSub : ∀ {m k} → KCtx m → KCtx k → Sub m k → Set
KSub Δ Δ′ σ = ∀ i → Δ i ≡ Once.Spec.Type.k-base → Base Δ′ (σ i)

-- Subtyping over open types is reflexive, hence stable under substitution.
<:ₚ-refl : ∀ {m} (A : Ty m) → A <:ₚ A
<:ₚ-refl (var i) = sub-var
<:ₚ-refl Unit = sub-unit
<:ₚ-refl Void = sub-void
<:ₚ-refl Int = sub-int
<:ₚ-refl Float = sub-float
<:ₚ-refl (rigid k i) = sub-rigid
<:ₚ-refl (A * B) = sub-prod (<:ₚ-refl A) (<:ₚ-refl B)
<:ₚ-refl (A + B) = sub-sum (<:ₚ-refl A) (<:ₚ-refl B)
<:ₚ-refl (A ⇒[ mk-kind q π ] B) = sub-arr (<:ₚ-refl A) (<:ₚ-refl B) (⊑π-refl π)
<:ₚ-refl (μ-type F) = sub-μ
<:ₚ-refl (ν-type F π) = sub-ν (⊑π-refl π)

------------------------------------------------------------------------
-- Substitution on contexts and terms
------------------------------------------------------------------------

_⟨_⟩ᶜ : ∀ {m k n} → PCtx m n → Sub m k → PCtx k n
∅           ⟨ σ ⟩ᶜ = ∅
(Γ , A ^ q) ⟨ σ ⟩ᶜ = (Γ ⟨ σ ⟩ᶜ) , (A ⟨ σ ⟩) ^ q

_⟨_⟩ₜ : ∀ {m k n} → PTm m n → Sub m k → PTm k n
var i        ⟨ σ ⟩ₜ = var i
lam t        ⟨ σ ⟩ₜ = lam (t ⟨ σ ⟩ₜ)
app A q t u  ⟨ σ ⟩ₜ = app (A ⟨ σ ⟩) q (t ⟨ σ ⟩ₜ) (u ⟨ σ ⟩ₜ)
let′ A q t u ⟨ σ ⟩ₜ = let′ (A ⟨ σ ⟩) q (t ⟨ σ ⟩ₜ) (u ⟨ σ ⟩ₜ)
unit         ⟨ σ ⟩ₜ = unit
pair t u     ⟨ σ ⟩ₜ = pair (t ⟨ σ ⟩ₜ) (u ⟨ σ ⟩ₜ)
fst B t      ⟨ σ ⟩ₜ = fst (B ⟨ σ ⟩) (t ⟨ σ ⟩ₜ)
snd A t      ⟨ σ ⟩ₜ = snd (A ⟨ σ ⟩) (t ⟨ σ ⟩ₜ)
inl t        ⟨ σ ⟩ₜ = inl (t ⟨ σ ⟩ₜ)
inr t        ⟨ σ ⟩ₜ = inr (t ⟨ σ ⟩ₜ)
case A B qℓ qr s l r ⟨ σ ⟩ₜ = case (A ⟨ σ ⟩) (B ⟨ σ ⟩) qℓ qr (s ⟨ σ ⟩ₜ) (l ⟨ σ ⟩ₜ) (r ⟨ σ ⟩ₜ)
absurd t     ⟨ σ ⟩ₜ = absurd (t ⟨ σ ⟩ₜ)
roll t       ⟨ σ ⟩ₜ = roll (t ⟨ σ ⟩ₜ)
fold F a t   ⟨ σ ⟩ₜ = fold (F ⟨ σ ⟩F) (a ⟨ σ ⟩ₜ) (t ⟨ σ ⟩ₜ)
unfold A c t ⟨ σ ⟩ₜ = unfold (A ⟨ σ ⟩) (c ⟨ σ ⟩ₜ) (t ⟨ σ ⟩ₜ)
out F t      ⟨ σ ⟩ₜ = out (F ⟨ σ ⟩F) (t ⟨ σ ⟩ₜ)
coerce A B t ⟨ σ ⟩ₜ = coerce (A ⟨ σ ⟩) (B ⟨ σ ⟩) (t ⟨ σ ⟩ₜ)
lit l        ⟨ σ ⟩ₜ = lit l
prim p t     ⟨ σ ⟩ₜ = prim p (t ⟨ σ ⟩ₜ)
sigop c A    ⟨ σ ⟩ₜ = sigop c A
ref d τ      ⟨ σ ⟩ₜ = ref d (λ i → τ i ⟨ σ ⟩)

infixl 60 _⟨_⟩ᶜ _⟨_⟩ₜ
