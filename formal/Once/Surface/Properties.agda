-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Surface.Properties
--
-- Properties of QTT usage algebra and subusaging relation.
-- Ensures the quantitative type system is sound.
------------------------------------------------------------------------

module Once.Surface.Properties where

open import Once.Type
open import Once.Surface.Syntax

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Bool using (Bool; true; false; _∧_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)
open import Data.Product using (_×_; _,_)

------------------------------------------------------------------------
-- Quantity Properties
------------------------------------------------------------------------

-- | Subusaging is reflexive
≤q-refl : ∀ (q : Quantity) → q ≤q q ≡ true
≤q-refl Zero = refl
≤q-refl One  = refl
≤q-refl Many = refl

-- | Subusaging is transitive
≤q-trans : ∀ {q₁ q₂ q₃ : Quantity}
         → q₁ ≤q q₂ ≡ true
         → q₂ ≤q q₃ ≡ true
         → q₁ ≤q q₃ ≡ true
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
+q-comm Zero Zero = refl
+q-comm Zero One = refl
+q-comm Zero Many = refl
+q-comm One Zero = refl
+q-comm One One = refl
+q-comm One Many = refl
+q-comm Many Zero = refl
+q-comm Many One = refl
+q-comm Many Many = refl

-- | Quantity addition is associative
+q-assoc : ∀ (q₁ q₂ q₃ : Quantity) → (q₁ +q q₂) +q q₃ ≡ q₁ +q (q₂ +q q₃)
+q-assoc Zero q₂ q₃ = refl
+q-assoc One Zero q₃ = refl
+q-assoc One One Zero = refl
+q-assoc One One One = refl
+q-assoc One One Many = refl
+q-assoc One Many q₃ = refl
+q-assoc Many q₂ q₃ = refl

-- | Zero is left identity for addition
+q-identityˡ : ∀ (q : Quantity) → Zero +q q ≡ q
+q-identityˡ q = refl

-- | Zero is right identity for addition
+q-identityʳ : ∀ (q : Quantity) → q +q Zero ≡ q
+q-identityʳ Zero = refl
+q-identityʳ One = refl
+q-identityʳ Many = refl

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
≤ᵘ?-refl : ∀ {n} (Γ : Ctx n) → zeroUsage ≤ᵘ? Γ ≡ true
≤ᵘ?-refl ∅ = refl
≤ᵘ?-refl (Γ , A ^ q) = cong (true ∧_) (≤ᵘ?-refl Γ)

-- | Zero usage satisfies any context
≤ᵘ?-zero : ∀ {n} (Γ : Ctx n) → zeroUsage ≤ᵘ? Γ ≡ true
≤ᵘ?-zero ∅ = refl
≤ᵘ?-zero (Γ , A ^ q) = cong (true ∧_) (≤ᵘ?-zero Γ)