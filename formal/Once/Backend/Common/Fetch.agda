------------------------------------------------------------------------
-- Once.Backend.Common.Fetch
--
-- Generic list indexing lemmas for instruction fetching.
-- These lemmas are polymorphic over the element type (Instr),
-- allowing reuse across all backends (AArch64, RiscV64, X86).
--
-- Usage in backend:
--   open import Once.Backend.Common.Fetch
--   -- Then use fetch-0, fetch-append-left, etc. with your Instr type
------------------------------------------------------------------------

module Once.Backend.Common.Fetch where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Nat using () renaming (_+_ to _+ℕ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Data.Nat using (_≤_; z≤n; s≤s)

------------------------------------------------------------------------
-- Generic fetch function (list indexing)
------------------------------------------------------------------------

-- | Fetch element at index n from a list
-- Returns nothing if index is out of bounds
fetch : ∀ {A : Set} → List A → ℕ → Maybe A
fetch [] _ = nothing
fetch (x ∷ xs) zero = just x
fetch (x ∷ xs) (suc n) = fetch xs n

------------------------------------------------------------------------
-- Immediate indexing lemmas (all trivial refl proofs)
------------------------------------------------------------------------

-- | Fetching at index 0 returns the first element
fetch-0 : ∀ {A : Set} (x : A) (xs : List A) → fetch (x ∷ xs) 0 ≡ just x
fetch-0 x xs = refl

-- | Fetching at index 1 returns the second element
fetch-1 : ∀ {A : Set} (x₀ x₁ : A) (xs : List A) → fetch (x₀ ∷ x₁ ∷ xs) 1 ≡ just x₁
fetch-1 x₀ x₁ xs = refl

-- | Fetching at index 2 returns the third element
fetch-2 : ∀ {A : Set} (x₀ x₁ x₂ : A) (xs : List A) → fetch (x₀ ∷ x₁ ∷ x₂ ∷ xs) 2 ≡ just x₂
fetch-2 x₀ x₁ x₂ xs = refl

-- | Fetching at index 3 returns the fourth element
fetch-3 : ∀ {A : Set} (x₀ x₁ x₂ x₃ : A) (xs : List A) → fetch (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ xs) 3 ≡ just x₃
fetch-3 x₀ x₁ x₂ x₃ xs = refl

-- | Fetching at index 4 returns the fifth element
fetch-4 : ∀ {A : Set} (x₀ x₁ x₂ x₃ x₄ : A) (xs : List A) → fetch (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ xs) 4 ≡ just x₄
fetch-4 x₀ x₁ x₂ x₃ x₄ xs = refl

-- | Fetching at index 5 returns the sixth element
fetch-5 : ∀ {A : Set} (x₀ x₁ x₂ x₃ x₄ x₅ : A) (xs : List A) → fetch (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ xs) 5 ≡ just x₅
fetch-5 x₀ x₁ x₂ x₃ x₄ x₅ xs = refl

-- | Fetching at index 6 returns the seventh element
fetch-6 : ∀ {A : Set} (x₀ x₁ x₂ x₃ x₄ x₅ x₆ : A) (xs : List A) → fetch (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ x₆ ∷ xs) 6 ≡ just x₆
fetch-6 x₀ x₁ x₂ x₃ x₄ x₅ x₆ xs = refl

------------------------------------------------------------------------
-- Structural lemmas
------------------------------------------------------------------------

-- | Fetching at index (suc n) is fetching from the tail at index n
fetch-suc : ∀ {A : Set} (x : A) (xs : List A) (n : ℕ) → fetch (x ∷ xs) (suc n) ≡ fetch xs n
fetch-suc x xs n = refl

-- | Fetching from empty list returns nothing
fetch-empty : ∀ {A : Set} (n : ℕ) → fetch {A} [] n ≡ nothing
fetch-empty n = refl

------------------------------------------------------------------------
-- Past-end lemmas (fetching beyond list length)
------------------------------------------------------------------------

-- | Fetching past end of single-element list returns nothing
fetch-1-single : ∀ {A : Set} (x : A) → fetch (x ∷ []) 1 ≡ nothing
fetch-1-single x = refl

-- | Fetching past end of 4-element list returns nothing
fetch-4-of-4 : ∀ {A : Set} (x₀ x₁ x₂ x₃ : A) → fetch (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ []) 4 ≡ nothing
fetch-4-of-4 x₀ x₁ x₂ x₃ = refl

-- | Fetching past end of 5-element list returns nothing
fetch-5-of-5 : ∀ {A : Set} (x₀ x₁ x₂ x₃ x₄ : A) → fetch (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ []) 5 ≡ nothing
fetch-5-of-5 x₀ x₁ x₂ x₃ x₄ = refl

-- | Fetching at exactly length returns nothing
fetch-past-end : ∀ {A : Set} (xs : List A) → fetch xs (length xs) ≡ nothing
fetch-past-end [] = refl
fetch-past-end (x ∷ xs) = fetch-past-end xs

------------------------------------------------------------------------
-- Append lemmas (key for program concatenation reasoning)
------------------------------------------------------------------------

-- | Fetching from append (left part): if n < length xs, fetch from xs
-- Proof by induction on xs
fetch-append-left : ∀ {A : Set} (xs ys : List A) (n : ℕ) → n < length xs →
  fetch (xs ++ ys) n ≡ fetch xs n
fetch-append-left [] ys n ()
fetch-append-left (x ∷ xs) ys zero pf = refl
fetch-append-left (x ∷ xs) ys (suc n) (s≤s pf) = fetch-append-left xs ys n pf

-- | Fetching from append (right part): fetch at (length xs + n) gets from ys
-- Proof by induction on xs
fetch-append-right : ∀ {A : Set} (xs ys : List A) (n : ℕ) →
  fetch (xs ++ ys) (length xs +ℕ n) ≡ fetch ys n
fetch-append-right [] ys n = refl
fetch-append-right (x ∷ xs) ys n = fetch-append-right xs ys n

-- | Fetching at exactly length xs gets the first element of ys
-- Corollary of fetch-append-right with n = 0
fetch-at-length : ∀ {A : Set} (xs : List A) (y : A) (ys : List A) →
  fetch (xs ++ y ∷ ys) (length xs) ≡ just y
fetch-at-length xs y ys =
  subst (λ n → fetch (xs ++ y ∷ ys) n ≡ just y)
        (+-identityʳ (length xs))
        (fetch-append-right xs (y ∷ ys) 0)
