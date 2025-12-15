------------------------------------------------------------------------
-- Once.Backend.Common.Memory
--
-- Common helper lemmas for memory proofs shared by all backends.
-- These are pure lemmas about natural numbers and boolean equality
-- that are used in memory-related proofs.
--
-- Usage in backend Correct.agda:
--   open import Once.Backend.Common.Memory public
------------------------------------------------------------------------

module Once.Backend.Common.Memory where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _+_; _≡ᵇ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; _≢_)

------------------------------------------------------------------------
-- Boolean equality lemmas
------------------------------------------------------------------------

-- | n ≡ᵇ n is always true
≡ᵇ-refl : ∀ (n : ℕ) → (n ≡ᵇ n) ≡ true
≡ᵇ-refl zero = refl
≡ᵇ-refl (suc n) = ≡ᵇ-refl n

------------------------------------------------------------------------
-- Address inequality helpers
------------------------------------------------------------------------

-- | n ≢ n + suc k (used for proving disjoint stack addresses)
n≢n+suc : ∀ (n k : ℕ) → n ≢ (n + suc k)
n≢n+suc n k eq = helper n k (sym eq)
  where
    suc-injective : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n
    suc-injective refl = refl

    helper : ∀ n k → (n + suc k) ≢ n
    helper zero k ()
    helper (suc n) k eq = helper n k (suc-injective eq)

-- | n ≡ᵇ (n + 8) is false (used for 8-byte aligned stack operations)
n≢n+8-bool : ∀ (n : ℕ) → (n ≡ᵇ (n + 8)) ≡ false
n≢n+8-bool zero = refl
n≢n+8-bool (suc n) = n≢n+8-bool n

-- | (n + 8) ≡ᵇ n is false (swapped version)
n+8≢n-bool : ∀ (n : ℕ) → ((n + 8) ≡ᵇ n) ≡ false
n+8≢n-bool zero = refl
n+8≢n-bool (suc n) = n+8≢n-bool n

-- | n ≡ᵇ (n + 16) is false
n≢n+16-bool : ∀ (n : ℕ) → (n ≡ᵇ (n + 16)) ≡ false
n≢n+16-bool zero = refl
n≢n+16-bool (suc n) = n≢n+16-bool n

-- | (n + 16) ≡ᵇ n is false
n+16≢n-bool : ∀ (n : ℕ) → ((n + 16) ≡ᵇ n) ≡ false
n+16≢n-bool zero = refl
n+16≢n-bool (suc n) = n+16≢n-bool n
