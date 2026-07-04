-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.MeaningBridge — the fundamental lemma of the observational
-- logical relation (Plan 0.58, OCP-0006): the DIRECT meaning `⟦_⟧ᶜ`/`⟦_⟧ᵢ`
-- and `SD.⟦realize _⟧ˢ` are `RelT`-related (and `⟦_⟧ᵐ`/`⟦_⟧ᵍ` relate to
-- `evalᴰ`/`eval` of the realized IR). Applied at `main : EffUU` / `tt`, this
-- discharges the apex `bridgeᵈ` postulate — funext-free (`MeaningRelation`).
--
-- Built strictly top-down: this module STATES the four-realm fundamental
-- lemma + the `RelEnv` it inducts over; the case discharges follow.
------------------------------------------------------------------------

module Once.Adequacy.MeaningBridge where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (Type; Purity; mk-kind; Many; _⇒[_]_)
open import Once.Surface.Context using (Ctx; ∅; _,_^_; lookup)
  renaming (⟦_⟧ᶜ to ⟦_⟧ᶜᵗ)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ)
open import Once.Denotation.TraceMonad using (T; returnT; _>>=T_)
open import Once.Denotation.DenotTrace using (evalᴰ)
open import Once.TypeCheck.Classify using (NamedCtx)
open import Once.TypeCheck.Judgment using (_⊢ᶜ_∶_⨾_; _⊢ᵢ_∶_⨾_; _⊢ᵍ_∶_; _⊢ᵐ_∶_⇨[_]_)
open import Once.Denotation.Meaning using (⟦_⟧ᶜ; ⟦_⟧ᵢ; ⟦_⟧ᵍ; ⟦_⟧ᵐ; lookupᴰ; Env)
open import Once.Denotation.Realize using (realize; realize-infer; realize-morph; realize-global)
import Once.Denotation.SourceDenote as SD
open import Once.Adequacy.MeaningRelation
  using (RelV; RelT; RelT-return; RelT-bind)

------------------------------------------------------------------------
-- Related environments — pointwise `RelV` down the context.
------------------------------------------------------------------------

RelEnv : ∀ {n} (Γ : Ctx n) → ⟦ ⟦ Γ ⟧ᶜᵗ ⟧ᴰ → ⟦ ⟦ Γ ⟧ᶜᵗ ⟧ᴰ → Set
RelEnv ∅           _          _          = ⊤
RelEnv (Γ , A ^ q) (dγ₁ , a₁) (dγ₂ , a₂) = RelEnv Γ dγ₁ dγ₂ × RelV A a₁ a₂

-- A related environment yields related values at every de-Bruijn position.
rel-lookup : ∀ {n} (Γ : Ctx n) (i : Fin n) {dγ₁ dγ₂ : ⟦ ⟦ Γ ⟧ᶜᵗ ⟧ᴰ}
           → RelEnv Γ dγ₁ dγ₂ → RelV (lookup Γ i) (lookupᴰ Γ i dγ₁) (lookupᴰ Γ i dγ₂)
rel-lookup (Γ , A ^ q) zero    {dγ₁ , a₁} {dγ₂ , a₂} (_  , ra) = ra
rel-lookup (Γ , A ^ q) (suc i) {dγ₁ , a₁} {dγ₂ , a₂} (re , _)  = rel-lookup Γ i re

------------------------------------------------------------------------
-- The fundamental lemma — four mutually-recursive realms. STATED here;
-- discharged case-by-case (structural: `RelT-bind`/`RelT-return` + IH).
-- SCAFFOLD: bodies are `postulate` pending the case discharges.
------------------------------------------------------------------------

postulate
  bridge-i : ∀ {ctx : NamedCtx} {e A Ψ} (d : ctx ⊢ᵢ e ∶ A ⨾ Ψ)
             {dγ₁ dγ₂ : Env ctx} (re : RelEnv (NamedCtx.debruijn ctx) dγ₁ dγ₂)
           → RelT A (⟦ d ⟧ᵢ dγ₁) (SD.⟦ realize-infer d ⟧ˢ dγ₂)
  bridge-c : ∀ {ctx : NamedCtx} {e A Ψ} (d : ctx ⊢ᶜ e ∶ A ⨾ Ψ)
             {dγ₁ dγ₂ : Env ctx} (re : RelEnv (NamedCtx.debruijn ctx) dγ₁ dγ₂)
           → RelT A (⟦ d ⟧ᶜ dγ₁) (SD.⟦ realize d ⟧ˢ dγ₂)
  bridge-m : ∀ {ctx : NamedCtx} {e A B} {π : Purity} (d : ctx ⊢ᵐ e ∶ A ⇨[ π ] B)
           → RelV (A ⇒[ mk-kind Many π ] B) (⟦ d ⟧ᵐ) (evalᴰ (realize-morph d))
  bridge-g : ∀ {ctx : NamedCtx} {e A} {X : Type} (d : ctx ⊢ᵍ e ∶ A) (y : ⟦ X ⟧ᴰ)
           → RelT A (returnT ⟦ d ⟧ᵍ) (evalᴰ (realize-global {X = X} d) y)
