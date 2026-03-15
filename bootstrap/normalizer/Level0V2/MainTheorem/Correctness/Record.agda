------------------------------------------------------------------------
-- Correctness.Record: The CorrectNormalizer record definition
--
-- Defines what it means for a normalizer to be correct.
-- No heavy dependencies - just the record type.
------------------------------------------------------------------------

module normalizer.Level0V2.MainTheorem.Correctness.Record where

open import normalizer.Foundations.Types
open import normalizer.Foundations.MinimalCCC
open import normalizer.Foundations.Encoding
  using (TermCode')
open import normalizer.Foundations.NormalForm
  using (IsNormalForm)

------------------------------------------------------------------------
-- What "correctly normalizes" means
------------------------------------------------------------------------

record CorrectNormalizer (N : Term TermCode' TermCode') : Set where
  field
    -- N terminates on all inputs (produces a result)
    terminates : ∀ (t : Term Unit TermCode') →
                 ∃[ result ] ((N ∘ t) ⟶* result)

    -- N produces normal forms
    produces-nf : ∀ (t : Term Unit TermCode') →
                  ∀ {result} → (N ∘ t) ⟶* result → IsNormalForm result

    -- N preserves semantics (result equivalent to input)
    preserves : ∀ (t : Term Unit TermCode') →
                ∀ {result} → (N ∘ t) ⟶* result →
                ∃[ nf ] ((t ⟶* nf) × (result ⟶* nf))
