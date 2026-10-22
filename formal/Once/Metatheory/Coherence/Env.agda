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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import Once.Spec.Grade using (Quantity; Zero; One; Many; _≤q_; 0≤q; 1≤1; 1≤ω; ω≤ω)
open import Once.Spec.Type using (Ty; TySub; _⟨_⟩)
open import Once.Spec.Context using (Ctx; ∅; _▸_; lookup; Usage; []; _∷_; _⊑ᵘ_; _⊑∷_; singleUse; zeroUsage; _+ᵘ_; _*ᵘ_)
open import Once.Spec.Core.Meaning Σ fmt S using (Env; Slot; restrict; lookupᵛ; envˡ; envʳ; env*One; env*Many)
open import Once.Metatheory.TermModel.Usage using (⊑ᵘ-+ˡ; ⊑ᵘ-+ʳ; ⊑ᵘ-trans; ⊑ᵘ-*One; ⊑ᵘ-*Many)
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

  -- The Spec's own restrictions to a part of a usage are `restrict` along the
  -- usage order (D335): each forgets exactly what the order proof forgets.
  envˡ-restrict : ∀ {n} {Γ : Ctx m n} (Ψ₁ Ψ₂ : Usage n) (γ : Env σ Γ (Ψ₁ +ᵘ Ψ₂)) → envˡ σ Ψ₁ Ψ₂ γ ≡ restrict σ (⊑ᵘ-+ˡ Ψ₁ Ψ₂) γ
  envˡ-restrict {Γ = ∅}     []          []          γ       = refl
  envˡ-restrict {Γ = Γ ▸ A} (Zero ∷ Ψ₁) (q    ∷ Ψ₂) (γ , v) = cong (_, tt) (envˡ-restrict Ψ₁ Ψ₂ γ)
  envˡ-restrict {Γ = Γ ▸ A} (One  ∷ Ψ₁) (Zero ∷ Ψ₂) (γ , v) = cong (_, v) (envˡ-restrict Ψ₁ Ψ₂ γ)
  envˡ-restrict {Γ = Γ ▸ A} (One  ∷ Ψ₁) (One  ∷ Ψ₂) (γ , v) = cong (_, v) (envˡ-restrict Ψ₁ Ψ₂ γ)
  envˡ-restrict {Γ = Γ ▸ A} (One  ∷ Ψ₁) (Many ∷ Ψ₂) (γ , v) = cong (_, v) (envˡ-restrict Ψ₁ Ψ₂ γ)
  envˡ-restrict {Γ = Γ ▸ A} (Many ∷ Ψ₁) (q    ∷ Ψ₂) (γ , v) = cong (_, v) (envˡ-restrict Ψ₁ Ψ₂ γ)

  envʳ-restrict : ∀ {n} {Γ : Ctx m n} (Ψ₁ Ψ₂ : Usage n) (γ : Env σ Γ (Ψ₁ +ᵘ Ψ₂)) → envʳ σ Ψ₁ Ψ₂ γ ≡ restrict σ (⊑ᵘ-+ʳ Ψ₁ Ψ₂) γ
  envʳ-restrict {Γ = ∅}     []          []          γ       = refl
  envʳ-restrict {Γ = Γ ▸ A} (Zero ∷ Ψ₁) (Zero ∷ Ψ₂) (γ , v) = cong (_, tt) (envʳ-restrict Ψ₁ Ψ₂ γ)
  envʳ-restrict {Γ = Γ ▸ A} (Zero ∷ Ψ₁) (One  ∷ Ψ₂) (γ , v) = cong (_, v) (envʳ-restrict Ψ₁ Ψ₂ γ)
  envʳ-restrict {Γ = Γ ▸ A} (Zero ∷ Ψ₁) (Many ∷ Ψ₂) (γ , v) = cong (_, v) (envʳ-restrict Ψ₁ Ψ₂ γ)
  envʳ-restrict {Γ = Γ ▸ A} (One  ∷ Ψ₁) (Zero ∷ Ψ₂) (γ , v) = cong (_, tt) (envʳ-restrict Ψ₁ Ψ₂ γ)
  envʳ-restrict {Γ = Γ ▸ A} (One  ∷ Ψ₁) (One  ∷ Ψ₂) (γ , v) = cong (_, v) (envʳ-restrict Ψ₁ Ψ₂ γ)
  envʳ-restrict {Γ = Γ ▸ A} (One  ∷ Ψ₁) (Many ∷ Ψ₂) (γ , v) = cong (_, v) (envʳ-restrict Ψ₁ Ψ₂ γ)
  envʳ-restrict {Γ = Γ ▸ A} (Many ∷ Ψ₁) (Zero ∷ Ψ₂) (γ , v) = cong (_, tt) (envʳ-restrict Ψ₁ Ψ₂ γ)
  envʳ-restrict {Γ = Γ ▸ A} (Many ∷ Ψ₁) (One  ∷ Ψ₂) (γ , v) = cong (_, v) (envʳ-restrict Ψ₁ Ψ₂ γ)
  envʳ-restrict {Γ = Γ ▸ A} (Many ∷ Ψ₁) (Many ∷ Ψ₂) (γ , v) = cong (_, v) (envʳ-restrict Ψ₁ Ψ₂ γ)

  env*One-restrict : ∀ {n} {Γ : Ctx m n} (Ψ : Usage n) (γ : Env σ Γ (One *ᵘ Ψ)) → env*One σ Ψ γ ≡ restrict σ (⊑ᵘ-*One Ψ) γ
  env*One-restrict {Γ = ∅}     []         γ       = refl
  env*One-restrict {Γ = Γ ▸ A} (Zero ∷ Ψ) (γ , v) = cong (_, tt) (env*One-restrict Ψ γ)
  env*One-restrict {Γ = Γ ▸ A} (One  ∷ Ψ) (γ , v) = cong (_, v) (env*One-restrict Ψ γ)
  env*One-restrict {Γ = Γ ▸ A} (Many ∷ Ψ) (γ , v) = cong (_, v) (env*One-restrict Ψ γ)

  env*Many-restrict : ∀ {n} {Γ : Ctx m n} (Ψ : Usage n) (γ : Env σ Γ (Many *ᵘ Ψ)) → env*Many σ Ψ γ ≡ restrict σ (⊑ᵘ-*Many Ψ) γ
  env*Many-restrict {Γ = ∅}     []         γ       = refl
  env*Many-restrict {Γ = Γ ▸ A} (Zero ∷ Ψ) (γ , v) = cong (_, tt) (env*Many-restrict Ψ γ)
  env*Many-restrict {Γ = Γ ▸ A} (One  ∷ Ψ) (γ , v) = cong (_, v) (env*Many-restrict Ψ γ)
  env*Many-restrict {Γ = Γ ▸ A} (Many ∷ Ψ) (γ , v) = cong (_, v) (env*Many-restrict Ψ γ)

  -- Forgetting twice is forgetting once.
  restrict-∘ : ∀ {n} {Γ : Ctx m n} {Ψ₀ Ψ₁ Ψ : Usage n} (P : Ψ₀ ⊑ᵘ Ψ₁) (Q : Ψ₁ ⊑ᵘ Ψ) (γ : Env σ Γ Ψ)
             → restrict σ P (restrict σ Q γ) ≡ restrict σ (⊑ᵘ-trans P Q) γ
  restrict-∘ {Γ = ∅} [] [] γ = refl
  restrict-∘ {Γ = Γ ▸ A} (0≤q ⊑∷ P) (0≤q ⊑∷ Q) (γ , v) = cong (_, tt) (restrict-∘ P Q γ)
  restrict-∘ {Γ = Γ ▸ A} (0≤q ⊑∷ P) (1≤1 ⊑∷ Q) (γ , v) = cong (_, tt) (restrict-∘ P Q γ)
  restrict-∘ {Γ = Γ ▸ A} (0≤q ⊑∷ P) (1≤ω ⊑∷ Q) (γ , v) = cong (_, tt) (restrict-∘ P Q γ)
  restrict-∘ {Γ = Γ ▸ A} (0≤q ⊑∷ P) (ω≤ω ⊑∷ Q) (γ , v) = cong (_, tt) (restrict-∘ P Q γ)
  restrict-∘ {Γ = Γ ▸ A} (1≤1 ⊑∷ P) (1≤1 ⊑∷ Q) (γ , v) = cong (_, v) (restrict-∘ P Q γ)
  restrict-∘ {Γ = Γ ▸ A} (1≤1 ⊑∷ P) (1≤ω ⊑∷ Q) (γ , v) = cong (_, v) (restrict-∘ P Q γ)
  restrict-∘ {Γ = Γ ▸ A} (1≤ω ⊑∷ P) (ω≤ω ⊑∷ Q) (γ , v) = cong (_, v) (restrict-∘ P Q γ)
  restrict-∘ {Γ = Γ ▸ A} (ω≤ω ⊑∷ P) (ω≤ω ⊑∷ Q) (γ , v) = cong (_, v) (restrict-∘ P Q γ)

  -- A scaled part of a part, forgotten in one step.
  env*One-envʳ-restrict : ∀ {n} {Γ : Ctx m n} (Ψ₁ Ψ₂ : Usage n) (γ : Env σ Γ (Ψ₁ +ᵘ One *ᵘ Ψ₂))
                        → env*One σ Ψ₂ (envʳ σ Ψ₁ (One *ᵘ Ψ₂) γ) ≡ restrict σ (⊑ᵘ-trans (⊑ᵘ-*One Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (One *ᵘ Ψ₂))) γ
  env*One-envʳ-restrict Ψ₁ Ψ₂ γ =
    trans (cong (env*One σ Ψ₂) (envʳ-restrict Ψ₁ (One *ᵘ Ψ₂) γ))
          (trans (env*One-restrict Ψ₂ _) (restrict-∘ (⊑ᵘ-*One Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (One *ᵘ Ψ₂)) γ))

  env*Many-envʳ-restrict : ∀ {n} {Γ : Ctx m n} (Ψ₁ Ψ₂ : Usage n) (γ : Env σ Γ (Ψ₁ +ᵘ Many *ᵘ Ψ₂))
                         → env*Many σ Ψ₂ (envʳ σ Ψ₁ (Many *ᵘ Ψ₂) γ) ≡ restrict σ (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))) γ
  env*Many-envʳ-restrict Ψ₁ Ψ₂ γ =
    trans (cong (env*Many σ Ψ₂) (envʳ-restrict Ψ₁ (Many *ᵘ Ψ₂) γ))
          (trans (env*Many-restrict Ψ₂ _) (restrict-∘ (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂)) γ))

  env*Many-envˡ-restrict : ∀ {n} {Γ : Ctx m n} (Ψ₁ Ψ₂ : Usage n) (γ : Env σ Γ (Many *ᵘ Ψ₁ +ᵘ Ψ₂))
                         → env*Many σ Ψ₁ (envˡ σ (Many *ᵘ Ψ₁) Ψ₂ γ) ≡ restrict σ (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₁) (⊑ᵘ-+ˡ (Many *ᵘ Ψ₁) Ψ₂)) γ
  env*Many-envˡ-restrict Ψ₁ Ψ₂ γ =
    trans (cong (env*Many σ Ψ₁) (envˡ-restrict (Many *ᵘ Ψ₁) Ψ₂ γ))
          (trans (env*Many-restrict Ψ₁ _) (restrict-∘ (⊑ᵘ-*Many Ψ₁) (⊑ᵘ-+ˡ (Many *ᵘ Ψ₁) Ψ₂) γ))
