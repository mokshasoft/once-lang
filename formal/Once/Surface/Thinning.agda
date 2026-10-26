-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Surface.Thinning
--
-- Order-Preserving Embeddings (Thinnings) for context manipulation.
--
-- A thinning Γ ⊆ Δ witnesses that Γ is a sub-context of Δ. Its actions on
-- variables (`thin-var`) and usages (`thin-usage`, a homomorphism of the usage
-- algebra) are what the core's renaming lemma (`Spec.Core.Rename.ren-⊢`) and
-- its meaning (`Metatheory.CoreRenameSem`) need.
------------------------------------------------------------------------

module Once.Surface.Thinning where

open import Once.Spec.Type using (Ty)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat as Nat using ()
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst; trans; sym)

open import Once.Spec.Grade
open import Once.Type.Grade
open import Once.Type.Core
open import Once.Spec.Type using (Type; Unit; Void; _*_; _+_; _⇒[_]_; Int; Float; K; Id; _⊕_; _⊗_)
open import Once.Spec.Surface.Syntax using (PolyType; PolyFunctor; PK; PId; _P⊕_; _P⊗_; PUnit; PVoid; _P*_; _P+_; _P⇒[_]_; PEff; PAct; Pμ; Pν; PInt; PFloat; PTVar)
open import Once.Type.Poly
open import Once.Type
open import Once.Context using (z≤z)
open import Once.Spec.Context using ([]; _⊑ᵘ_; lookup; Usage; zeroUsage; singleUse; _+ᵘ_; _*ᵘ_)
open import Once.Spec.Context using ([]; _∷_; _⊑∷_; _▸_)
open import Once.Context as Surface renaming (_,_ to _S,_)
open import Once.Spec.Context using () renaming (Ctx to SCtx; ∅ to S∅)
open import Once.Surface.Context as Surface

------------------------------------------------------------------------
-- Thinnings (Order-Preserving Embeddings)
------------------------------------------------------------------------

-- A thinning from Γ to Δ says "Γ's variables appear in Δ in order,
-- but Δ may have extra variables interspersed."

data _⊆_ {k} : ∀ {n m} → SCtx k n → SCtx k m → Set where
  -- Empty context embeds into empty context
  done : S∅ ⊆ S∅

  -- Skip: Δ has an extra variable that Γ doesn't have
  skip : ∀ {n m} {Γ : SCtx k n} {Δ : SCtx k m} {A : Ty k}
       → Γ ⊆ Δ → Γ ⊆ (Δ ▸ A)

  -- Keep: both contexts have the same variable at this position
  keep : ∀ {n m} {Γ : SCtx k n} {Δ : SCtx k m} {A : Ty k}
       → Γ ⊆ Δ → (Γ ▸ A) ⊆ (Δ ▸ A)

infixr 4 _⊆_

------------------------------------------------------------------------
-- Basic Thinnings
------------------------------------------------------------------------

-- Identity thinning: Γ ⊆ Γ
⊆-refl : ∀ {m} {n} {Γ : SCtx m n} → Γ ⊆ Γ
⊆-refl {Γ = S∅}            = done
⊆-refl {Γ = Γ' ▸ _} = keep ⊆-refl

-- Weakening thinning: Γ ⊆ (Γ ▸ A)
⊆-wk : ∀ {m} {n} {Γ : SCtx m n} {A : Ty m} → Γ ⊆ (Γ ▸ A)
⊆-wk = skip ⊆-refl

------------------------------------------------------------------------
-- Variable Thinning
------------------------------------------------------------------------

-- Apply thinning to a variable index
thin-var : ∀ {mₜ} {n m} {Γ : SCtx mₜ n} {Δ : SCtx mₜ m}
         → Γ ⊆ Δ → Fin n → Fin m
thin-var (skip θ) i       = suc (thin-var θ i)
thin-var (keep θ) zero    = zero
thin-var (keep θ) (suc i) = suc (thin-var θ i)

-- Key lemma: thinning preserves lookup
thin-var-lookup : ∀ {mₜ} {n m} {Γ : SCtx mₜ n} {Δ : SCtx mₜ m}
                → (θ : Γ ⊆ Δ) → (i : Fin n)
                → lookup Γ i ≡ lookup Δ (thin-var θ i)
thin-var-lookup (skip θ) i       = thin-var-lookup θ i
thin-var-lookup (keep θ) zero    = refl
thin-var-lookup (keep θ) (suc i) = thin-var-lookup θ i

------------------------------------------------------------------------
-- Thinning on Usage Vectors
------------------------------------------------------------------------

-- Apply a thinning to a usage vector.
-- skip inserts Zero at the new position (the skipped variable is unused).
-- keep copies the head, recurses on the tail.
thin-usage : ∀ {mₜ} {n m} {Γ : SCtx mₜ n} {Δ : SCtx mₜ m}
           → Γ ⊆ Δ → Usage n → Usage m
thin-usage done     []        = []
thin-usage (skip θ) Ψ         = Zero ∷ thin-usage θ Ψ
thin-usage (keep θ) (q ∷ Ψ)  = q ∷ thin-usage θ Ψ

-- Distribution lemmas: thin-usage commutes with QTT usage arithmetic.

thin-usage-+ᵘ : ∀ {mₜ} {n m} {Γ : SCtx mₜ n} {Δ : SCtx mₜ m}
              → (θ : Γ ⊆ Δ) (Ψ₁ Ψ₂ : Usage n)
              → thin-usage θ (Ψ₁ +ᵘ Ψ₂) ≡ thin-usage θ Ψ₁ +ᵘ thin-usage θ Ψ₂
thin-usage-+ᵘ done     [] []               = refl
thin-usage-+ᵘ (skip θ) Ψ₁ Ψ₂
  rewrite thin-usage-+ᵘ θ Ψ₁ Ψ₂             = refl
thin-usage-+ᵘ (keep θ) (q₁ ∷ Ψ₁) (q₂ ∷ Ψ₂)
  rewrite thin-usage-+ᵘ θ Ψ₁ Ψ₂             = refl

thin-usage-*ᵘ : ∀ {mₜ} {n m} {Γ : SCtx mₜ n} {Δ : SCtx mₜ m}
              → (θ : Γ ⊆ Δ) (q : Quantity) (Ψ : Usage n)
              → thin-usage θ (q *ᵘ Ψ) ≡ q *ᵘ thin-usage θ Ψ
thin-usage-*ᵘ done     q []                 = refl
thin-usage-*ᵘ {Γ = Γ} {Δ = Δ ▸ _} (skip θ) q Ψ
  rewrite thin-usage-*ᵘ θ q Ψ               = cong (_∷ (q *ᵘ thin-usage θ Ψ)) (sym (q*q-zero q))
  where
    -- q *q Zero = Zero for all q (needed for the skip case)
    q*q-zero : (q : Quantity) → q *q Zero ≡ Zero
    q*q-zero Zero = refl
    q*q-zero One  = refl
    q*q-zero Many = refl
thin-usage-*ᵘ (keep θ) q (q' ∷ Ψ)
  rewrite thin-usage-*ᵘ θ q Ψ               = refl

thin-usage-⊔ᵘ : ∀ {mₜ} {n m} {Γ : SCtx mₜ n} {Δ : SCtx mₜ m}
              → (θ : Γ ⊆ Δ) (Ψ₁ Ψ₂ : Usage n)
              → thin-usage θ (Ψ₁ ⊔ᵘ Ψ₂) ≡ thin-usage θ Ψ₁ ⊔ᵘ thin-usage θ Ψ₂
thin-usage-⊔ᵘ done     [] []               = refl
thin-usage-⊔ᵘ (skip θ) Ψ₁ Ψ₂
  rewrite thin-usage-⊔ᵘ θ Ψ₁ Ψ₂             = refl
thin-usage-⊔ᵘ (keep θ) (q₁ ∷ Ψ₁) (q₂ ∷ Ψ₂)
  rewrite thin-usage-⊔ᵘ θ Ψ₁ Ψ₂             = refl

-- D276: thinning is monotone in the usage order (a skipped slot is `Zero`).
thin-usage-⊑ᵘ : ∀ {mₜ} {n m} {Γ : SCtx mₜ n} {Δ : SCtx mₜ m}
              → (θ : Γ ⊆ Δ) {Ψ Ψ′ : Usage n}
              → Ψ ⊑ᵘ Ψ′ → thin-usage θ Ψ ⊑ᵘ thin-usage θ Ψ′
thin-usage-⊑ᵘ done     []       = []
thin-usage-⊑ᵘ (skip θ) p         = z≤z ⊑∷ thin-usage-⊑ᵘ θ p
thin-usage-⊑ᵘ (keep θ) (q ⊑∷ p)  = q ⊑∷ thin-usage-⊑ᵘ θ p

thin-usage-zeroUsage : ∀ {mₜ} {n m} {Γ : SCtx mₜ n} {Δ : SCtx mₜ m}
                     → (θ : Γ ⊆ Δ) → thin-usage θ (zeroUsage {n}) ≡ zeroUsage {m}
thin-usage-zeroUsage done     = refl
thin-usage-zeroUsage (skip θ) = cong (Zero ∷_) (thin-usage-zeroUsage θ)
thin-usage-zeroUsage (keep θ) = cong (Zero ∷_) (thin-usage-zeroUsage θ)

thin-usage-refl : ∀ {m} {n} {Γ : SCtx m n} (Ψ : Usage n)
                → thin-usage (⊆-refl {Γ = Γ}) Ψ ≡ Ψ
thin-usage-refl {Γ = S∅} []                = refl
thin-usage-refl {Γ = _ ▸ _} (q ∷ Ψ)  = cong (q ∷_) (thin-usage-refl Ψ)

thin-usage-singleUse : ∀ {mₜ} {n m} {Γ : SCtx mₜ n} {Δ : SCtx mₜ m}
                     → (θ : Γ ⊆ Δ) (i : Fin n) (q : Quantity)
                     → thin-usage θ (singleUse i q) ≡ singleUse (thin-var θ i) q
thin-usage-singleUse done     ()       q
thin-usage-singleUse (skip θ) i        q
  rewrite thin-usage-singleUse θ i q    = refl
thin-usage-singleUse (keep θ) zero     q = cong (q ∷_) (thin-usage-zeroUsage θ)
thin-usage-singleUse (keep θ) (suc i) q  = cong (Zero ∷_) (thin-usage-singleUse θ i q)
