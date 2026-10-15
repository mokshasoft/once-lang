{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Context — typing contexts and their usages.
--
-- A context `Ctx m n` is `n` variables of types over `m` type variables. A
-- usage `Usage n` says how often each is used (`Spec.Grade`); usages add,
-- scale and are ordered pointwise (a term may claim more than it uses). The
-- five order facts at the end are what the meaning needs to hand each part of
-- a term the part of the environment it uses.
------------------------------------------------------------------------

module Once.Spec.Context where

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; zero; suc)
open import Once.Spec.Grade using (Quantity; Zero; One; Many; _+q_; _*q_; _≤q_; 0≤q; 1≤1; 1≤ω; ω≤ω)
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

------------------------------------------------------------------------
-- The order facts the meaning uses
------------------------------------------------------------------------

private
  ≤q-+ˡ : ∀ p q → p ≤q (p +q q)
  ≤q-+ˡ Zero q    = 0≤q
  ≤q-+ˡ One Zero  = 1≤1
  ≤q-+ˡ One One   = 1≤ω
  ≤q-+ˡ One Many  = 1≤ω
  ≤q-+ˡ Many q    = ω≤ω

  ≤q-+ʳ : ∀ p q → q ≤q (p +q q)
  ≤q-+ʳ Zero Zero = 0≤q
  ≤q-+ʳ Zero One  = 1≤1
  ≤q-+ʳ Zero Many = ω≤ω
  ≤q-+ʳ One Zero  = 0≤q
  ≤q-+ʳ One One   = 1≤ω
  ≤q-+ʳ One Many  = ω≤ω
  ≤q-+ʳ Many Zero = 0≤q
  ≤q-+ʳ Many One  = 1≤ω
  ≤q-+ʳ Many Many = ω≤ω

  ≤q-trans : ∀ {a b c} → a ≤q b → b ≤q c → a ≤q c
  ≤q-trans 0≤q _   = 0≤q
  ≤q-trans 1≤1 b≤c = b≤c
  ≤q-trans 1≤ω ω≤ω = 1≤ω
  ≤q-trans ω≤ω ω≤ω = ω≤ω

  ≤q-*One : ∀ q → q ≤q (One *q q)
  ≤q-*One Zero = 0≤q
  ≤q-*One One  = 1≤1
  ≤q-*One Many = ω≤ω

  ≤q-*Many : ∀ q → q ≤q (Many *q q)
  ≤q-*Many Zero = 0≤q
  ≤q-*Many One  = 1≤ω
  ≤q-*Many Many = ω≤ω

⊑ᵘ-+ˡ : ∀ {n} (Ψ₁ Ψ₂ : Usage n) → Ψ₁ ⊑ᵘ Ψ₁ +ᵘ Ψ₂
⊑ᵘ-+ˡ []       []       = []
⊑ᵘ-+ˡ (p ∷ Ψ₁) (q ∷ Ψ₂) = ≤q-+ˡ p q ⊑∷ ⊑ᵘ-+ˡ Ψ₁ Ψ₂

⊑ᵘ-+ʳ : ∀ {n} (Ψ₁ Ψ₂ : Usage n) → Ψ₂ ⊑ᵘ Ψ₁ +ᵘ Ψ₂
⊑ᵘ-+ʳ []       []       = []
⊑ᵘ-+ʳ (p ∷ Ψ₁) (q ∷ Ψ₂) = ≤q-+ʳ p q ⊑∷ ⊑ᵘ-+ʳ Ψ₁ Ψ₂

⊑ᵘ-trans : ∀ {n} {Ψ₁ Ψ₂ Ψ₃ : Usage n} → Ψ₁ ⊑ᵘ Ψ₂ → Ψ₂ ⊑ᵘ Ψ₃ → Ψ₁ ⊑ᵘ Ψ₃
⊑ᵘ-trans []       []       = []
⊑ᵘ-trans (a ⊑∷ as) (b ⊑∷ bs) = ≤q-trans a b ⊑∷ ⊑ᵘ-trans as bs

⊑ᵘ-*One : ∀ {n} (Ψ : Usage n) → Ψ ⊑ᵘ One *ᵘ Ψ
⊑ᵘ-*One []      = []
⊑ᵘ-*One (q ∷ Ψ) = ≤q-*One q ⊑∷ ⊑ᵘ-*One Ψ

⊑ᵘ-*Many : ∀ {n} (Ψ : Usage n) → Ψ ⊑ᵘ Many *ᵘ Ψ
⊑ᵘ-*Many []      = []
⊑ᵘ-*Many (q ∷ Ψ) = ≤q-*Many q ⊑∷ ⊑ᵘ-*Many Ψ

-- A context at an instance of its type variables.
_⟨_⟩ᶜ : ∀ {m k n} → Ctx m n → Once.Spec.Type.TySub m k → Ctx k n
∅       ⟨ σ ⟩ᶜ = ∅
(Γ ▸ A) ⟨ σ ⟩ᶜ = Γ ⟨ σ ⟩ᶜ ▸ A Once.Spec.Type.⟨ σ ⟩
