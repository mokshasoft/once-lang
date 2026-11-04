{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Parametricity.Env — environments at two instances,
-- related variable by variable by the relational reading of their types,
-- at two usages (`Coherence.Env`'s `Agree`, between two instances).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Parametricity.Env (Σ : Signature) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Once.Spec.Grade using (Quantity; Zero; One; Many; 0≤q; 1≤1; 1≤ω; ω≤ω)
open import Once.Spec.Type using (Ty; TySub; _⟨_⟩)
open import Once.Spec.Context using (Ctx; ∅; _▸_; lookup; Usage; []; _∷_; _⊑ᵘ_; _⊑∷_; singleUse)
open import Once.Spec.Core.Meaning Σ fmt S using (Env; Slot; slot; restrict; lookupᵛ)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ)
open import Once.Spec.Equivalence Σ using (Rel; RelSub)
open import Once.Spec.Metatheory using (RelEnv)

module _ {m : ℕ} {σ σ′ : TySub m 0} (ρ : RelSub σ σ′) where

  RSlot : (A : Ty m) (q q′ : Quantity) → Slot q ⟦ A ⟨ σ ⟩ ⟧ᵛ → Slot q′ ⟦ A ⟨ σ′ ⟩ ⟧ᵛ → Set
  RSlot A Zero q′   v v′ = ⊤
  RSlot A One  Zero v v′ = ⊤
  RSlot A Many Zero v v′ = ⊤
  RSlot A One  One  v v′ = Rel A ρ v v′
  RSlot A One  Many v v′ = Rel A ρ v v′
  RSlot A Many One  v v′ = Rel A ρ v v′
  RSlot A Many Many v v′ = Rel A ρ v v′

  RAgree : ∀ {n} (Γ : Ctx m n) (Ψ Ψ′ : Usage n) → Env σ Γ Ψ → Env σ′ Γ Ψ′ → Set
  RAgree ∅       []      []        γ        γ′         = ⊤
  RAgree (Γ ▸ A) (q ∷ Ψ) (q′ ∷ Ψ′) (γ , v) (γ′ , v′) = RAgree Γ Ψ Ψ′ γ γ′ × RSlot A q q′ v v′

  -- Forgetting variables on the left, or on the right.
  rrestrictˡ : ∀ {n} {Γ : Ctx m n} {Ψ₀ Ψ Ψ′ : Usage n} (p : Ψ₀ ⊑ᵘ Ψ) {γ γ′}
             → RAgree Γ Ψ Ψ′ γ γ′ → RAgree Γ Ψ₀ Ψ′ (restrict σ p γ) γ′
  rrestrictˡ {Γ = ∅} {Ψ′ = []} [] a = tt
  rrestrictˡ {Γ = Γ ▸ A} {Ψ′ = q′ ∷ Ψ′} (0≤q ⊑∷ p) {γ , v} {γ′ , v′} (a , sv) = rrestrictˡ p a , tt
  rrestrictˡ {Γ = Γ ▸ A} {Ψ′ = q′ ∷ Ψ′} (1≤1 ⊑∷ p) {γ , v} {γ′ , v′} (a , sv) = rrestrictˡ p a , sv
  rrestrictˡ {Γ = Γ ▸ A} {Ψ′ = Zero ∷ Ψ′} (1≤ω ⊑∷ p) {γ , v} {γ′ , v′} (a , sv) = rrestrictˡ p a , tt
  rrestrictˡ {Γ = Γ ▸ A} {Ψ′ = One ∷ Ψ′}  (1≤ω ⊑∷ p) {γ , v} {γ′ , v′} (a , sv) = rrestrictˡ p a , sv
  rrestrictˡ {Γ = Γ ▸ A} {Ψ′ = Many ∷ Ψ′} (1≤ω ⊑∷ p) {γ , v} {γ′ , v′} (a , sv) = rrestrictˡ p a , sv
  rrestrictˡ {Γ = Γ ▸ A} {Ψ′ = q′ ∷ Ψ′} (ω≤ω ⊑∷ p) {γ , v} {γ′ , v′} (a , sv) = rrestrictˡ p a , sv

  rrestrictʳ : ∀ {n} {Γ : Ctx m n} {Ψ Ψ₀′ Ψ′ : Usage n} (p : Ψ₀′ ⊑ᵘ Ψ′) {γ γ′}
             → RAgree Γ Ψ Ψ′ γ γ′ → RAgree Γ Ψ Ψ₀′ γ (restrict σ′ p γ′)
  rrestrictʳ {Γ = ∅} {Ψ = []} [] a = tt
  rrestrictʳ {Γ = Γ ▸ A} {Ψ = Zero ∷ Ψ} (0≤q ⊑∷ p) {γ , v} {γ′ , v′} (a , sv) = rrestrictʳ p a , tt
  rrestrictʳ {Γ = Γ ▸ A} {Ψ = Zero ∷ Ψ} (1≤1 ⊑∷ p) {γ , v} {γ′ , v′} (a , sv) = rrestrictʳ p a , tt
  rrestrictʳ {Γ = Γ ▸ A} {Ψ = Zero ∷ Ψ} (1≤ω ⊑∷ p) {γ , v} {γ′ , v′} (a , sv) = rrestrictʳ p a , tt
  rrestrictʳ {Γ = Γ ▸ A} {Ψ = Zero ∷ Ψ} (ω≤ω ⊑∷ p) {γ , v} {γ′ , v′} (a , sv) = rrestrictʳ p a , tt
  rrestrictʳ {Γ = Γ ▸ A} {Ψ = One  ∷ Ψ} (0≤q ⊑∷ p) {γ , v} {γ′ , v′} (a , sv) = rrestrictʳ p a , tt
  rrestrictʳ {Γ = Γ ▸ A} {Ψ = One  ∷ Ψ} (1≤1 ⊑∷ p) {γ , v} {γ′ , v′} (a , sv) = rrestrictʳ p a , sv
  rrestrictʳ {Γ = Γ ▸ A} {Ψ = One  ∷ Ψ} (1≤ω ⊑∷ p) {γ , v} {γ′ , v′} (a , sv) = rrestrictʳ p a , sv
  rrestrictʳ {Γ = Γ ▸ A} {Ψ = One  ∷ Ψ} (ω≤ω ⊑∷ p) {γ , v} {γ′ , v′} (a , sv) = rrestrictʳ p a , sv
  rrestrictʳ {Γ = Γ ▸ A} {Ψ = Many ∷ Ψ} (0≤q ⊑∷ p) {γ , v} {γ′ , v′} (a , sv) = rrestrictʳ p a , tt
  rrestrictʳ {Γ = Γ ▸ A} {Ψ = Many ∷ Ψ} (1≤1 ⊑∷ p) {γ , v} {γ′ , v′} (a , sv) = rrestrictʳ p a , sv
  rrestrictʳ {Γ = Γ ▸ A} {Ψ = Many ∷ Ψ} (1≤ω ⊑∷ p) {γ , v} {γ′ , v′} (a , sv) = rrestrictʳ p a , sv
  rrestrictʳ {Γ = Γ ▸ A} {Ψ = Many ∷ Ψ} (ω≤ω ⊑∷ p) {γ , v} {γ′ , v′} (a , sv) = rrestrictʳ p a , sv

  -- A variable both environments hold has related values.
  rlookup : ∀ {n} (Γ : Ctx m n) (i : Fin n) {γ γ′}
          → RAgree Γ (singleUse i One) (singleUse i One) γ γ′
          → Rel (lookup Γ i) ρ (lookupᵛ σ Γ i γ) (lookupᵛ σ′ Γ i γ′)
  rlookup (Γ ▸ A) zero    {γ , v} {γ′ , v′} (a , sv) = sv
  rlookup (Γ ▸ A) (suc i) {γ , v} {γ′ , v′} (a , sv) = rlookup Γ i a

  -- Environments related by their types agree.
  relAgree : ∀ {n} (Γ : Ctx m n) (Ψ : Usage n) {γ γ′} → RelEnv Σ fmt S ρ Γ Ψ γ γ′ → RAgree Γ Ψ Ψ γ γ′
  relAgree ∅       []         e        = tt
  relAgree (Γ ▸ A) (Zero ∷ Ψ) {γ , v} {γ′ , v′} e        = relAgree Γ Ψ e , tt
  relAgree (Γ ▸ A) (One  ∷ Ψ) {γ , v} {γ′ , v′} (e , sv) = relAgree Γ Ψ e , sv
  relAgree (Γ ▸ A) (Many ∷ Ψ) {γ , v} {γ′ , v′} (e , sv) = relAgree Γ Ψ e , sv

  -- A bound value, at the binder's quantity on both sides.
  rslot : ∀ (A : Ty m) q {a a′} → Rel A ρ a a′ → RSlot A q q (slot q a) (slot q a′)
  rslot A Zero s = tt
  rslot A One  s = s
  rslot A Many s = s
