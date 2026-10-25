-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Surface.Properties
--
-- Properties of QTT usage algebra and subusaging relation.
-- Ensures the quantitative type system is sound.
------------------------------------------------------------------------

module Once.Surface.Properties where

import Once.Internal.Laws.Grade as G

open import Once.Spec.Grade
open import Once.Type.Grade
open import Once.Internal.Type
open import Once.Spec.Type using (Type; Unit; Void; _*_; _+_; _⇒[_]_; Int; Float; K; Id; _⊕_; _⊗_)
open import Once.Spec.Surface.Syntax using (PolyType; PolyFunctor; PK; PId; _P⊕_; _P⊗_; PUnit; PVoid; _P*_; _P+_; _P⇒[_]_; PEff; PAct; Pμ; Pν; PInt; PFloat; PTVar)
open import Once.Internal.Type.Poly
open import Once.Type
open import Once.Internal.Context
open import Once.Spec.Context using (Ctx; Usage; _*ᵘ_; _+ᵘ_; zeroUsage; ∅)
open import Once.Spec.Context using ([]; _∷_; _⊑∷_; _▸_)
open import Once.Surface.Context
open import Once.Surface.Syntax

open import Data.Nat using (ℕ)
open import Data.Bool using (true; _∧_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans)

------------------------------------------------------------------------
-- Quantity Properties
------------------------------------------------------------------------

-- | Subusaging is reflexive
≤q-refl : ∀ (q : Quantity) → q ≤qᵇ q ≡ true
≤q-refl Zero = refl
≤q-refl One  = refl
≤q-refl Many = refl

-- | Subusaging is transitive
≤q-trans : ∀ {q₁ q₂ q₃ : Quantity}
         → q₁ ≤qᵇ q₂ ≡ true
         → q₂ ≤qᵇ q₃ ≡ true
         → q₁ ≤qᵇ q₃ ≡ true
≤q-trans {Zero} {q₂} {q₃} p₁₂ p₂₃ = refl
≤q-trans {One} {Zero} {q₃} () p₂₃
≤q-trans {One} {One} {Zero} p₁₂ ()
≤q-trans {One} {One} {One} p₁₂ p₂₃ = refl
≤q-trans {One} {One} {Many} p₁₂ p₂₃ = refl
≤q-trans {One} {Many} {Zero} p₁₂ ()
≤q-trans {One} {Many} {One} p₁₂ ()
≤q-trans {One} {Many} {Many} p₁₂ p₂₃ = refl
≤q-trans {Many} {Zero} {q₃} () p₂₃
≤q-trans {Many} {One} {q₃} () p₂₃
≤q-trans {Many} {Many} {Zero} p₁₂ ()
≤q-trans {Many} {Many} {One} p₁₂ ()
≤q-trans {Many} {Many} {Many} p₁₂ p₂₃ = refl

-- | Quantity addition is commutative
+q-comm : ∀ (q₁ q₂ : Quantity) → q₁ +q q₂ ≡ q₂ +q q₁
+q-comm = G.+q-comm

-- | Quantity addition is associative
+q-assoc : ∀ (q₁ q₂ q₃ : Quantity) → (q₁ +q q₂) +q q₃ ≡ q₁ +q (q₂ +q q₃)
+q-assoc = G.+q-assoc

-- | Zero is left identity for addition
+q-identityˡ : ∀ (q : Quantity) → Zero +q q ≡ q
+q-identityˡ = G.+q-identityˡ

-- | Zero is right identity for addition
+q-identityʳ : ∀ (q : Quantity) → q +q Zero ≡ q
+q-identityʳ = G.+q-identityʳ

-- | Many is absorbing for addition
+q-absorb : ∀ (q : Quantity) → Many +q q ≡ Many
+q-absorb q = refl

------------------------------------------------------------------------
-- Usage Vector Properties
------------------------------------------------------------------------

-- | Usage addition is commutative
+ᵘ-comm : ∀ {n} (ψ₁ ψ₂ : Usage n) → ψ₁ +ᵘ ψ₂ ≡ ψ₂ +ᵘ ψ₁
+ᵘ-comm [] [] = refl
+ᵘ-comm (q₁ ∷ ψ₁) (q₂ ∷ ψ₂) = cong₂ _∷_ (+q-comm q₁ q₂) (+ᵘ-comm ψ₁ ψ₂)

-- | Usage addition is associative
+ᵘ-assoc : ∀ {n} (ψ₁ ψ₂ ψ₃ : Usage n) → (ψ₁ +ᵘ ψ₂) +ᵘ ψ₃ ≡ ψ₁ +ᵘ (ψ₂ +ᵘ ψ₃)
+ᵘ-assoc [] [] [] = refl
+ᵘ-assoc (q₁ ∷ ψ₁) (q₂ ∷ ψ₂) (q₃ ∷ ψ₃) = cong₂ _∷_ (+q-assoc q₁ q₂ q₃) (+ᵘ-assoc ψ₁ ψ₂ ψ₃)

-- | Zero usage is left identity for addition
+ᵘ-identityˡ : ∀ {n} (ψ : Usage n) → zeroUsage +ᵘ ψ ≡ ψ
+ᵘ-identityˡ [] = refl
+ᵘ-identityˡ (q ∷ ψ) = cong₂ _∷_ (+q-identityˡ q) (+ᵘ-identityˡ ψ)

-- | Zero usage is right identity for addition
+ᵘ-identityʳ : ∀ {n} (ψ : Usage n) → ψ +ᵘ zeroUsage ≡ ψ
+ᵘ-identityʳ [] = refl
+ᵘ-identityʳ (q ∷ ψ) = cong₂ _∷_ (+q-identityʳ q) (+ᵘ-identityʳ ψ)

-- | One is identity for scaling (left)
*ᵘ-identityˡ : ∀ {n} (ψ : Usage n) → One *ᵘ ψ ≡ ψ
*ᵘ-identityˡ [] = refl
*ᵘ-identityˡ (Zero ∷ ψ) = cong₂ _∷_ refl (*ᵘ-identityˡ ψ)
*ᵘ-identityˡ (One ∷ ψ) = cong₂ _∷_ refl (*ᵘ-identityˡ ψ)
*ᵘ-identityˡ (Many ∷ ψ) = cong₂ _∷_ refl (*ᵘ-identityˡ ψ)

-- | Zero scaling gives zero usage
*ᵘ-zeroˡ : ∀ {n} (ψ : Usage n) → Zero *ᵘ ψ ≡ zeroUsage
*ᵘ-zeroˡ [] = refl
*ᵘ-zeroˡ (q ∷ ψ) = cong₂ _∷_ refl (*ᵘ-zeroˡ ψ)

-- | Scaling zero usage gives zero usage
*ᵘ-zeroʳ : ∀ {n} (q : Quantity) → q *ᵘ zeroUsage {n} ≡ zeroUsage
*ᵘ-zeroʳ {ℕ.zero} q = refl
*ᵘ-zeroʳ {ℕ.suc n} Zero = cong₂ _∷_ refl (*ᵘ-zeroʳ {n} Zero)
*ᵘ-zeroʳ {ℕ.suc n} One = cong₂ _∷_ refl (*ᵘ-zeroʳ {n} One)
*ᵘ-zeroʳ {ℕ.suc n} Many = cong₂ _∷_ refl (*ᵘ-zeroʳ {n} Many)

------------------------------------------------------------------------
-- Subusaging Properties
------------------------------------------------------------------------

-- | Subusaging is reflexive
≤ᵘ?-refl : ∀ {m} {n} (Γ : Ctx m n) → zeroUsage ≤ᵘ? Γ ≡ true
≤ᵘ?-refl ∅ = refl
≤ᵘ?-refl (Γ ▸ A) = cong (true ∧_) (≤ᵘ?-refl Γ)

-- | Zero usage satisfies any context
≤ᵘ?-zero : ∀ {m} {n} (Γ : Ctx m n) → zeroUsage ≤ᵘ? Γ ≡ true
≤ᵘ?-zero ∅ = refl
≤ᵘ?-zero (Γ ▸ A) = cong (true ∧_) (≤ᵘ?-zero Γ)
-- | ERASURE AT THE USAGE LEVEL (D143) — the Once analogue of `NbEPQTTJ`'s
--   judgment-level `erase-arg` (`(ρf +ᵘ (𝟘 ·ᵘ ρa)) ≡ ρf`). An application at a
--   `Zero`-graded arrow uses exactly what the FUNCTION uses: the argument's
--   usage scales away, so its variables are not in the runtime environment at
--   all. This is what makes the erased `app`/`let'` clauses type-correct
--   without widening the environment.
+ᵘ-idʳ : ∀ {n} (Ψ : Usage n) → Ψ +ᵘ zeroUsage ≡ Ψ
+ᵘ-idʳ []      = refl
+ᵘ-idʳ (q ∷ Ψ) = cong₂ _∷_ (+q-identityʳ q) (+ᵘ-idʳ Ψ)

erase-arg-usage : ∀ {n} (Ψ₁ Ψ₂ : Usage n) → Ψ₁ +ᵘ (Zero *ᵘ Ψ₂) ≡ Ψ₁
erase-arg-usage Ψ₁ Ψ₂ = trans (cong (Ψ₁ +ᵘ_) (*ᵘ-zeroˡ Ψ₂)) (+ᵘ-idʳ Ψ₁)
