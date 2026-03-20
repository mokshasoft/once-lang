------------------------------------------------------------------------
-- RunTest: Verify the fixpoint property at type-checking time
--
-- If this file type-checks successfully, the fixpoint holds!
-- Run: agda Level0/RunTest.agda
-- Success = fixpoint achieved
------------------------------------------------------------------------

module normalizer.Level0.RunTest where

open import normalizer.Level0.Evaluator

-- Type-level assertion: this will only type-check if fixpoint-holds ≡ true
-- (using a unit type that only exists when the condition is met)

data IsTrue : Bool → Set where
  indeed : IsTrue true

-- If this type-checks, the fixpoint test passed!
fixpoint-proof : IsTrue fixpoint-holds
fixpoint-proof = indeed

-- Alternative: using propositional equality
-- This asserts that fixpoint-holds normalizes to true
open import normalizer.Foundations.Types using (_≡_; refl)

fixpoint-verified : fixpoint-holds ≡ true
fixpoint-verified = refl
