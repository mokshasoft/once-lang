{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Context — typing contexts and their usages.
--
-- A context `Ctx m n` is `n` variables of types over `m` type variables. A
-- usage `Usage n` says how often each is used (`Spec.Grade`); usages add,
-- scale and are ordered pointwise (a term may claim more than it uses).
------------------------------------------------------------------------

module Once.Spec.Context where

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; zero; suc)
open import Once.Spec.Grade using (Quantity; Zero; One; Many; _+q_; _*q_; _≤q_)
import Once.Spec.Type
open import Once.Spec.Type using (Ty)

data Ctx (m : ℕ) : ℕ → Set where
  ∅   : Ctx m 0
  _▸_ : ∀ {n} → Ctx m n → Ty m → Ctx m (suc n)

infixl 5 _▸_

lookup : ∀ {m n} → Ctx m n → Fin n → Ty m
lookup (Γ ▸ A) zero    = A
lookup (Γ ▸ A) (suc i) = lookup Γ i

data Usage : ℕ → Set where
  []  : Usage 0
  _∷_ : ∀ {n} → Quantity → Usage n → Usage (suc n)

infixr 5 _∷_

zeroUsage : ∀ {n} → Usage n
zeroUsage {0}     = []
zeroUsage {suc n} = Zero ∷ zeroUsage

-- Variable `i` used `q` times, nothing else.
singleUse : ∀ {n} → Fin n → Quantity → Usage n
singleUse zero    q = q ∷ zeroUsage
singleUse (suc i) q = Zero ∷ singleUse i q

_+ᵘ_ : ∀ {n} → Usage n → Usage n → Usage n
[]       +ᵘ []       = []
(p ∷ Ψ₁) +ᵘ (q ∷ Ψ₂) = (p +q q) ∷ (Ψ₁ +ᵘ Ψ₂)

_*ᵘ_ : ∀ {n} → Quantity → Usage n → Usage n
q *ᵘ []      = []
q *ᵘ (p ∷ Ψ) = (q *q p) ∷ (q *ᵘ Ψ)

infixl 60 _+ᵘ_
infixl 70 _*ᵘ_

data _⊑ᵘ_ : ∀ {n} → Usage n → Usage n → Set where
  []  : [] ⊑ᵘ []
  _⊑∷_ : ∀ {n p q} {Ψ Ψ′ : Usage n} → p ≤q q → Ψ ⊑ᵘ Ψ′ → (p ∷ Ψ) ⊑ᵘ (q ∷ Ψ′)

infix 4 _⊑ᵘ_
infixr 5 _⊑∷_

-- A context at an instance of its type variables.
_⟨_⟩ᶜ : ∀ {m k n} → Ctx m n → Once.Spec.Type.TySub m k → Ctx k n
∅       ⟨ σ ⟩ᶜ = ∅
(Γ ▸ A) ⟨ σ ⟩ᶜ = Γ ⟨ σ ⟩ᶜ ▸ A Once.Spec.Type.⟨ σ ⟩
