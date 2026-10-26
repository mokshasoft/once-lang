-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.EnvRel — the environment plumbing of the source semantics
-- respects the value relation (plan 0.119 D5).
--
-- A runtime environment `⟦ ⟦ Γ ↾ Ψ ⟧ᶜ ⟧ᴰ` is a nested product, so two are
-- related componentwise (`RelD ⟦ Γ ↾ Ψ ⟧ᶜ`). Narrowing (`restrictᴰ`), reading a
-- variable (`lookupᴰUsed`) and binding one (`bindᴰ`) take related environments
-- to related ones — by the same case analysis that defines them.
------------------------------------------------------------------------

module Once.Adequacy.EnvRel where

open import Once.Spec.Type using (Ty)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)

open import Once.Spec.Grade using (Quantity; Zero; One; Many)
open import Once.Spec.Type using (Type)
open import Once.Context using (⟦_⟧ᶜ; _↾_; z≤z; z≤o; z≤m; o≤o; o≤m; m≤m)
open import Once.Spec.Context using (Ctx; Usage; []; _⊑ᵘ_; lookup; singleUse; ∅)
open import Once.Spec.Context using (_∷_; _⊑∷_; _▸_)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ)
open import Once.Denotation.Phase using (lookupᴰUsed; restrictᴰ; bindᴰ; bindᴰ0)
open import Once.Denotation.ValueRel using (RelD)

restrict-rel : ∀ {m} {n} {Γ : Ctx m n} {Ψ Ψ' : Usage n} (ule : Ψ' ⊑ᵘ Ψ) {d d′ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜ ⟧ᴰ}
             → RelD ⟦ Γ ↾ Ψ ⟧ᶜ d d′ → RelD ⟦ Γ ↾ Ψ' ⟧ᶜ (restrictᴰ {Γ = Γ} ule d) (restrictᴰ {Γ = Γ} ule d′)
restrict-rel {Γ = ∅}         []          r = r
restrict-rel {Γ = Γ ▸ A} (z≤z ⊑∷ ule) r = restrict-rel {Γ = Γ} ule r
restrict-rel {Γ = Γ ▸ A} (z≤o ⊑∷ ule) r = restrict-rel {Γ = Γ} ule (proj₁ r)
restrict-rel {Γ = Γ ▸ A} (z≤m ⊑∷ ule) r = restrict-rel {Γ = Γ} ule (proj₁ r)
restrict-rel {Γ = Γ ▸ A} (o≤o ⊑∷ ule) r = restrict-rel {Γ = Γ} ule (proj₁ r) , proj₂ r
restrict-rel {Γ = Γ ▸ A} (o≤m ⊑∷ ule) r = restrict-rel {Γ = Γ} ule (proj₁ r) , proj₂ r
restrict-rel {Γ = Γ ▸ A} (m≤m ⊑∷ ule) r = restrict-rel {Γ = Γ} ule (proj₁ r) , proj₂ r

lookup-rel : ∀ {m} {n} (Γ : Ctx m n) (i : Fin n) {d d′ : ⟦ ⟦ Γ ↾ singleUse i One ⟧ᶜ ⟧ᴰ}
           → RelD ⟦ Γ ↾ singleUse i One ⟧ᶜ d d′ → RelD (lookup Γ i) (lookupᴰUsed Γ i d) (lookupᴰUsed Γ i d′)
lookup-rel (Γ ▸ A) zero    r = proj₂ r
lookup-rel (Γ ▸ A) (suc i) r = lookup-rel Γ i r

bind-rel : ∀ {m} {n} {Γ : Ctx m n} {Ψ' : Usage n} {A : Ty m} (q : Quantity) {d d′ : ⟦ ⟦ Γ ↾ Ψ' ⟧ᶜ ⟧ᴰ} {a a′ : ⟦ A ⟧ᴰ}
         → RelD ⟦ Γ ↾ Ψ' ⟧ᶜ d d′ → RelD A a a′
         → RelD ⟦ (Γ ▸ A) ↾ (q ∷ Ψ') ⟧ᶜ (bindᴰ {Γ = Γ} {A = A} q d a) (bindᴰ {Γ = Γ} {A = A} q d′ a′)
bind-rel Zero r ra = r
bind-rel One  r ra = r , ra
bind-rel Many r ra = r , ra
