------------------------------------------------------------------------
-- Normalize.Properties: Properties of the normalizer
--
-- This module contains claims about the normalizer's behavior.
-- These are proof obligations to be discharged.
------------------------------------------------------------------------

module normalizer.Level0V2.Normalize.Properties where

open import normalizer.Foundations.Types
open import normalizer.Foundations.MinimalCCC
open import normalizer.Foundations.Encoding
  using (TermCode')
open import normalizer.Foundations.NormalForm
  using (IsNormalForm)

open import normalizer.Level0V2.Normalize
  using (normalize)

------------------------------------------------------------------------
-- The normalizer produces normal forms
------------------------------------------------------------------------

-- Proof obligation: normalize always produces a normal form
postulate
  normalize-produces-nf : ∀ (t : Term Unit TermCode') →
                          IsNormalForm (normalize ∘ t)
