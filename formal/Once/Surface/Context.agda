-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Surface.Context — the IR-FREE typing-context / QTT-usage core.
--
-- Extracted from `Once.Surface.Syntax` (Plan 0.58, OCP-0006) so that the
-- context machinery (`Ctx`/`Usage`/`⟦_⟧ᶜ`/`lookup`) is available WITHOUT the
-- `Once.IR` import that `Surface.Syntax`'s `Expr` needs (only its
-- `lift-morphism`/`morph-app` leaves carry `IR`). This is what lets the typing
-- judgment and the direct denotation `⟦_⟧ᵈ` be genuinely IR-free.
--
-- `Surface.Syntax` re-exports this module (`open … public`), so its consumers
-- are unchanged; spec/denotation modules import THIS directly to stay IR-free.
------------------------------------------------------------------------

module Once.Surface.Context where

open import Once.Type
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Bool using (Bool; true; _∧_)

-- | Typing context (de Bruijn indexed with quantities)
--
-- Ctx n represents a context with n variables.
-- Variables are indexed by Fin n (0 to n-1).
-- Each variable has a type and a quantity (usage annotation).
--
data Ctx : ℕ → Set where
  ∅   : Ctx 0
  _,_^_ : ∀ {n} → Ctx n → Type → Quantity → Ctx (ℕ.suc n)

infixl 5 _,_^_

-- | Smart constructor: extend context with unrestricted quantity
_,_ : ∀ {n} → Ctx n → Type → Ctx (ℕ.suc n)
Γ , A = Γ , A ^ Many

infixl 5 _,_

-- | Lookup type at position in context
lookup : ∀ {n} → Ctx n → Fin n → Type
lookup (Γ , A ^ q) Fin.zero    = A
lookup (Γ , _ ^ _) (Fin.suc i) = lookup Γ i

-- | Interpret a context as the (left-nested) product environment type.
--   (A₀,…,Aₙ₋₁) ↦ (…((Unit * A₀) * A₁) … * Aₙ₋₁). Pure `Ctx → Type` — it lives
--   here (with `Ctx`/`Type`), NOT in `Surface.Elaborate`, so the denotational
--   meaning can take it without importing the (operational) elaborator (0.47).
⟦_⟧ᶜ : ∀ {n} → Ctx n → Type
⟦ ∅ ⟧ᶜ         = Unit
⟦ Γ , A ^ q ⟧ᶜ = ⟦ Γ ⟧ᶜ * A

-- | Lookup quantity at position in context
lookupQuantity : ∀ {n} → Ctx n → Fin n → Quantity
lookupQuantity (Γ , A ^ q) Fin.zero    = q
lookupQuantity (Γ , _ ^ _) (Fin.suc i) = lookupQuantity Γ i

------------------------------------------------------------------------
-- Usage Vectors (QTT)
------------------------------------------------------------------------

-- | Usage vector: tracks how many times each variable is used
data Usage : ℕ → Set where
  []  : Usage 0
  _∷_ : ∀ {n} → Quantity → Usage n → Usage (ℕ.suc n)

infixr 5 _∷_

-- | Zero usage vector (all variables unused)
zeroUsage : ∀ {n} → Usage n
zeroUsage {0} = []
zeroUsage {ℕ.suc n} = Zero ∷ zeroUsage

-- | Single variable usage (one variable used with quantity q, rest unused)
singleUse : ∀ {n} → Fin n → Quantity → Usage n
singleUse {ℕ.suc n} Fin.zero    q = q ∷ zeroUsage
singleUse {ℕ.suc n} (Fin.suc i) q = Zero ∷ singleUse i q

-- | Add two usage vectors (combine usage from different branches)
_+ᵘ_ : ∀ {n} → Usage n → Usage n → Usage n
[] +ᵘ [] = []
(q₁ ∷ ψ₁) +ᵘ (q₂ ∷ ψ₂) = (q₁ +q q₂) ∷ (ψ₁ +ᵘ ψ₂)

infixl 60 _+ᵘ_

-- | Scale usage vector by quantity (usage in a context scaled by q)
_*ᵘ_ : ∀ {n} → Quantity → Usage n → Usage n
q *ᵘ [] = []
q *ᵘ (q' ∷ ψ) = (q *q q') ∷ (q *ᵘ ψ)

infixl 70 _*ᵘ_

-- | Per-position maximum of two usage vectors (for case branches).
_⊔ᵘ_ : ∀ {n} → Usage n → Usage n → Usage n
[]        ⊔ᵘ []        = []
(q₁ ∷ ψ₁) ⊔ᵘ (q₂ ∷ ψ₂) = (q₁ ⊔q q₂) ∷ (ψ₁ ⊔ᵘ ψ₂)

infixl 55 _⊔ᵘ_

-- | Check if usage respects declared quantities
_≤ᵘ_ : ∀ {n} → Usage n → Ctx n → Set
[] ≤ᵘ ∅ = ⊤
  where
    open import Data.Unit using (⊤)
(q ∷ ψ) ≤ᵘ (Γ , A ^ q') = (q ≤q q' ≡ true) × (ψ ≤ᵘ Γ)
  where
    open import Data.Bool using (true)
    open import Relation.Binary.PropositionalEquality using (_≡_)
    open import Data.Product using (_×_)

-- | Boolean version of subusaging check (for validation)
_≤ᵘ?_ : ∀ {n} → Usage n → Ctx n → Bool
[] ≤ᵘ? ∅ = true
(q ∷ ψ) ≤ᵘ? (Γ , A ^ q') = (q ≤q q') ∧ (ψ ≤ᵘ? Γ)

-- | Lookup quantity at specific index in usage vector
lookupUsage : ∀ {n} → Usage n → Fin n → Quantity
lookupUsage (q ∷ ψ) Fin.zero    = q
lookupUsage (q ∷ ψ) (Fin.suc i) = lookupUsage ψ i

-- | Drop first element from usage vector (for removing bound variable)
tailUsage : ∀ {n} → Usage (ℕ.suc n) → Usage n
tailUsage (q ∷ ψ) = ψ

------------------------------------------------------------------------
-- Plan 0.58 (OCP-0006): the IR-FREE variable witness. A de-Bruijn `Fin`
-- carrying the same type/usage indices a `var i : Expr` would — so
-- `lookupLocal`/`t-var-local` can name a local WITHOUT the IR-carrying `Expr`.
-- (`Surface.var i` rebuilds the `Expr` from `svar i` in the impl side.)
------------------------------------------------------------------------
data SVar : ∀ {n} → Ctx n → Usage n → Type → Set where
  svar : ∀ {n} {Γ : Ctx n} (i : Fin n) → SVar Γ (singleUse i One) (lookup Γ i)
