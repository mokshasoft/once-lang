{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Coherence.Env — two environments of one context AGREE
-- when, at every variable both hold, their values are the same.
--
-- Two derivations of one term may give a context different usages; the
-- environments they are run in then hold different variables. A variable
-- either derivation reads is one both hold, so agreement where both hold is
-- what the fundamental lemma needs, and it survives forgetting variables
-- (`restrict`) on either side.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Coherence.Env (Σ : Signature) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Once.Spec.Grade using (Quantity; Zero; One; Many; _≤q_; 0≤q; 1≤1; 1≤ω; ω≤ω)
open import Once.Spec.Type using (Ty; TySub; _⟨_⟩)
open import Once.Spec.Context using (Ctx; ∅; _▸_; lookup; Usage; []; _∷_; _⊑ᵘ_; _⊑∷_; singleUse; zeroUsage)
open import Once.Spec.Core.Meaning Σ fmt S using (Env; Slot; restrict; lookupᵛ)
open import Once.Spec.Equivalence Σ using (Same)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ)
open import Once.Spec.Metatheory using (SameEnv)

module _ {m : ℕ} (σ : TySub m 0) where

  SlotAgree : (A : Ty m) (q q′ : Quantity) → Slot q ⟦ A ⟨ σ ⟩ ⟧ᵛ → Slot q′ ⟦ A ⟨ σ ⟩ ⟧ᵛ → Set
  SlotAgree A Zero q′   v v′ = ⊤
  SlotAgree A One  Zero v v′ = ⊤
  SlotAgree A Many Zero v v′ = ⊤
  SlotAgree A One  One  v v′ = Same (A ⟨ σ ⟩) v v′
  SlotAgree A One  Many v v′ = Same (A ⟨ σ ⟩) v v′
  SlotAgree A Many One  v v′ = Same (A ⟨ σ ⟩) v v′
  SlotAgree A Many Many v v′ = Same (A ⟨ σ ⟩) v v′

  Agree : ∀ {n} (Γ : Ctx m n) (Ψ Ψ′ : Usage n) → Env σ Γ Ψ → Env σ Γ Ψ′ → Set
  Agree ∅       []      []        γ        γ′         = ⊤
  Agree (Γ ▸ A) (q ∷ Ψ) (q′ ∷ Ψ′) (γ , v) (γ′ , v′) = Agree Γ Ψ Ψ′ γ γ′ × SlotAgree A q q′ v v′

  -- Forgetting variables on the left, or on the right.
  restrictˡ : ∀ {n} {Γ : Ctx m n} {Ψ₀ Ψ Ψ′ : Usage n} (p : Ψ₀ ⊑ᵘ Ψ) {γ γ′}
            → Agree Γ Ψ Ψ′ γ γ′ → Agree Γ Ψ₀ Ψ′ (restrict σ p γ) γ′
  restrictˡ {Γ = ∅} {Ψ′ = []} [] a = tt
  restrictˡ {Γ = Γ ▸ A} {Ψ′ = q′ ∷ Ψ′} (0≤q ⊑∷ p) {γ , v} {γ′ , v′} (a , sv) = restrictˡ p a , tt
  restrictˡ {Γ = Γ ▸ A} {Ψ′ = q′ ∷ Ψ′} (1≤1 ⊑∷ p) {γ , v} {γ′ , v′} (a , sv) = restrictˡ p a , sv
  restrictˡ {Γ = Γ ▸ A} {Ψ′ = Zero ∷ Ψ′} (1≤ω ⊑∷ p) {γ , v} {γ′ , v′} (a , sv) = restrictˡ p a , tt
  restrictˡ {Γ = Γ ▸ A} {Ψ′ = One ∷ Ψ′}  (1≤ω ⊑∷ p) {γ , v} {γ′ , v′} (a , sv) = restrictˡ p a , sv
  restrictˡ {Γ = Γ ▸ A} {Ψ′ = Many ∷ Ψ′} (1≤ω ⊑∷ p) {γ , v} {γ′ , v′} (a , sv) = restrictˡ p a , sv
  restrictˡ {Γ = Γ ▸ A} {Ψ′ = q′ ∷ Ψ′} (ω≤ω ⊑∷ p) {γ , v} {γ′ , v′} (a , sv) = restrictˡ p a , sv

  restrictʳ : ∀ {n} {Γ : Ctx m n} {Ψ Ψ₀′ Ψ′ : Usage n} (p : Ψ₀′ ⊑ᵘ Ψ′) {γ γ′}
            → Agree Γ Ψ Ψ′ γ γ′ → Agree Γ Ψ Ψ₀′ γ (restrict σ p γ′)
  restrictʳ {Γ = ∅} {Ψ = []} [] a = tt
  restrictʳ {Γ = Γ ▸ A} {Ψ = Zero ∷ Ψ} (0≤q ⊑∷ p) {γ , v} {γ′ , v′} (a , sv) = restrictʳ p a , tt
  restrictʳ {Γ = Γ ▸ A} {Ψ = Zero ∷ Ψ} (1≤1 ⊑∷ p) {γ , v} {γ′ , v′} (a , sv) = restrictʳ p a , tt
  restrictʳ {Γ = Γ ▸ A} {Ψ = Zero ∷ Ψ} (1≤ω ⊑∷ p) {γ , v} {γ′ , v′} (a , sv) = restrictʳ p a , tt
  restrictʳ {Γ = Γ ▸ A} {Ψ = Zero ∷ Ψ} (ω≤ω ⊑∷ p) {γ , v} {γ′ , v′} (a , sv) = restrictʳ p a , tt
  restrictʳ {Γ = Γ ▸ A} {Ψ = One  ∷ Ψ} (0≤q ⊑∷ p) {γ , v} {γ′ , v′} (a , sv) = restrictʳ p a , tt
  restrictʳ {Γ = Γ ▸ A} {Ψ = One  ∷ Ψ} (1≤1 ⊑∷ p) {γ , v} {γ′ , v′} (a , sv) = restrictʳ p a , sv
  restrictʳ {Γ = Γ ▸ A} {Ψ = One  ∷ Ψ} (1≤ω ⊑∷ p) {γ , v} {γ′ , v′} (a , sv) = restrictʳ p a , sv
  restrictʳ {Γ = Γ ▸ A} {Ψ = One  ∷ Ψ} (ω≤ω ⊑∷ p) {γ , v} {γ′ , v′} (a , sv) = restrictʳ p a , sv
  restrictʳ {Γ = Γ ▸ A} {Ψ = Many ∷ Ψ} (0≤q ⊑∷ p) {γ , v} {γ′ , v′} (a , sv) = restrictʳ p a , tt
  restrictʳ {Γ = Γ ▸ A} {Ψ = Many ∷ Ψ} (1≤1 ⊑∷ p) {γ , v} {γ′ , v′} (a , sv) = restrictʳ p a , sv
  restrictʳ {Γ = Γ ▸ A} {Ψ = Many ∷ Ψ} (1≤ω ⊑∷ p) {γ , v} {γ′ , v′} (a , sv) = restrictʳ p a , sv
  restrictʳ {Γ = Γ ▸ A} {Ψ = Many ∷ Ψ} (ω≤ω ⊑∷ p) {γ , v} {γ′ , v′} (a , sv) = restrictʳ p a , sv

  -- A variable both environments hold has the same value in both.
  lookupAgree : ∀ {n} (Γ : Ctx m n) (i : Fin n) {γ γ′}
              → Agree Γ (singleUse i One) (singleUse i One) γ γ′
              → Same (lookup Γ i ⟨ σ ⟩) (lookupᵛ σ Γ i γ) (lookupᵛ σ Γ i γ′)
  lookupAgree (Γ ▸ A) zero    {γ , v} {γ′ , v′} (a , sv) = sv
  lookupAgree (Γ ▸ A) (suc i) {γ , v} {γ′ , v′} (a , sv) = lookupAgree Γ i a

  -- An environment whose values are each the same as itself agrees with itself.
  selfAgree : ∀ {n} (Γ : Ctx m n) (Ψ : Usage n) (γ : Env σ Γ Ψ)
            → SameEnv Σ fmt S σ Γ Ψ γ → Agree Γ Ψ Ψ γ γ
  selfAgree ∅       []         γ       e        = tt
  selfAgree (Γ ▸ A) (Zero ∷ Ψ) (γ , v) e        = selfAgree Γ Ψ γ e , tt
  selfAgree (Γ ▸ A) (One  ∷ Ψ) (γ , v) (e , sv) = selfAgree Γ Ψ γ e , sv
  selfAgree (Γ ▸ A) (Many ∷ Ψ) (γ , v) (e , sv) = selfAgree Γ Ψ γ e , sv
