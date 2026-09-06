-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Optimizer.Cost
--
-- Cost model for Once IR terms.
-- Counts allocating constructors (pairs, sums, closures, In/in-ν).
--
-- This is the measure we want the optimizer to minimize.
------------------------------------------------------------------------

module Once.Optimizer.Cost where

open import Once.Type
open import Once.IR

open import Data.Nat using (ℕ; zero; suc; _⊔_; _≤_; _<_; z≤n)
open import Data.Nat as ℕ using () renaming (_+_ to _ℕ+_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; +-comm; +-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

------------------------------------------------------------------------
-- Cost: Count allocating operations
------------------------------------------------------------------------

-- | Cost of an IR term
--
-- Counts the number of allocating constructors:
--   - ⟨_,_⟩  : pair allocation (1)
--   - inl/inr: sum allocation (1)
--   - curry  : closure allocation (1)
--   - In     : μ-type wrapper allocation (1)
--   - in-ν   : ν-type wrapper allocation (1)
--
-- Non-allocating operations have cost 0.
--
cost : ∀ {A B} → IR A B → ℕ
-- D062: cost of the natural transform a Fuse/Hylo carries = Σ of its
-- constant-leaf (ntK) IR costs.
cost-nt : ∀ {G F} → NatTr G F → ℕ
cost id            = 0
cost (g ∘ f)       = cost g ℕ+ cost f
cost fst           = 0
cost snd           = 0
cost (⟨ f , g ⟩) = 1 ℕ+ cost f ℕ+ cost g   -- pair allocation
cost (inl _)       = 1                        -- sum allocation
cost (inr _)       = 1                        -- sum allocation
cost (case f g)    = cost f ℕ+ cost g
cost terminal      = 0
cost initial       = 0
cost (curry f _)   = 1 ℕ+ cost f              -- closure allocation
cost apply         = 0
cost arr           = 0
-- Recursion schemes (OCP-0003)
cost (In _ _)      = 1                        -- μ-type wrapper allocation
cost (out-μ _)     = 0                        -- destructor is free
cost (Cata _ alg)  = cost alg                 -- cost of algebra
cost (Para _ alg)  = cost alg                 -- cost of algebra
cost (Out _)       = 0                        -- observation is free
cost (in-ν _ _)    = 1                        -- ν-type wrapper allocation
cost (Ana _ coalg) = cost coalg               -- cost of coalgebra
cost (Hylo _ _ alg t) = cost alg ℕ+ cost-nt t  -- fusion: algebra + natural transform
cost (Fuse _ _ alg t) = cost alg ℕ+ cost-nt t  -- fusion: algebra + natural transform
-- Memory and primitives
cost (free-heap _) = 0                        -- deallocation doesn't allocate
cost (SigOp _)      = 0                        -- primitives are opaque
cost (const _ _)  = 0                        -- literal global element

cost-nt ntId         = 0
cost-nt (ntK ir)     = cost ir
cost-nt (ntFst t)    = cost-nt t
cost-nt (ntSnd t)    = cost-nt t
cost-nt (ntCase t u) = cost-nt t ℕ+ cost-nt u
cost-nt (ntInl t)    = cost-nt t
cost-nt (ntInr t)    = cost-nt t
cost-nt (ntPair t u) = cost-nt t ℕ+ cost-nt u

------------------------------------------------------------------------
-- Basic properties
------------------------------------------------------------------------

-- | Cost is non-negative (trivial for ℕ, but useful for documentation)
cost-≥-0 : ∀ {A B} (t : IR A B) → 0 ≤ cost t
cost-≥-0 _ = Data.Nat.z≤n

-- | Cost of composition is sum of costs
cost-compose : ∀ {A B C} (g : IR B C) (f : IR A B) →
  cost (g ∘ f) ≡ cost g ℕ+ cost f
cost-compose g f = refl

------------------------------------------------------------------------
-- Cost ordering
------------------------------------------------------------------------

-- | One term is cheaper than another
_≤-cost_ : ∀ {A B} → IR A B → IR A B → Set
t ≤-cost t' = cost t ≤ cost t'

-- | Strict cost ordering
_<-cost_ : ∀ {A B} → IR A B → IR A B → Set
t <-cost t' = cost t < cost t'

-- | Cost ordering is reflexive
≤-cost-refl : ∀ {A B} (t : IR A B) → t ≤-cost t
≤-cost-refl t = ≤-refl

-- | Cost ordering is transitive
≤-cost-trans : ∀ {A B} {t₁ t₂ t₃ : IR A B} →
  t₁ ≤-cost t₂ → t₂ ≤-cost t₃ → t₁ ≤-cost t₃
≤-cost-trans = ≤-trans