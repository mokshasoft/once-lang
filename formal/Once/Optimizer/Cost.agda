------------------------------------------------------------------------
-- Once.Optimizer.Cost
--
-- Cost model for Once IR terms.
-- Counts allocating constructors (pairs, sums, closures, folds).
--
-- This is the measure we want the optimizer to minimize.
------------------------------------------------------------------------

module Once.Optimizer.Cost where

open import Once.Type
open import Once.CCC.IR

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
--   - fold   : recursive type wrapper (1)
--
-- Non-allocating operations have cost 0.
--
cost : ∀ {A B} → IR A B → ℕ
cost id            = 0
cost (g ∘ f)       = cost g ℕ+ cost f
cost fst           = 0
cost snd           = 0
cost (⟨ f , g ⟩ _) = 1 ℕ+ cost f ℕ+ cost g   -- pair allocation
cost (inl _)       = 1                        -- sum allocation
cost (inr _)       = 1                        -- sum allocation
cost (case f g)     = cost f ℕ+ cost g
cost terminal      = 0
cost initial       = 0
cost (curry f _)   = 1 ℕ+ cost f              -- closure allocation
cost apply         = 0
cost (fold _)          = 1                        -- Fix wrapper allocation
cost unfold        = 0                        -- unwrapping is free
cost arr           = 0
cost (Prim _)      = 0                        -- primitives are opaque

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
