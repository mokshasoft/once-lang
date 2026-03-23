------------------------------------------------------------------------
-- Correctness.Record: The CorrectNormalizer record definition
--
-- Defines what it means for a normalizer to be correct.
-- No heavy dependencies - just the record type.
------------------------------------------------------------------------

module normalizer.Theory.GeneralCorrectness.Record where

open import normalizer.Syntax.Types
open import normalizer.Syntax.CCC
open import normalizer.Encoding.Encoding
  using (TermCode')
open import normalizer.Syntax.BetaNormalForm
  using (IsBetaNormalForm)

------------------------------------------------------------------------
-- What "correctly normalizes" means
--
-- Note: We use IsBetaNormalForm rather than IsNormalForm because:
--   - IsNormalForm means "no reduction applies" (including structural)
--   - IsBetaNormalForm means "no computational reduction applies"
--   - Encodings are beta-normal but NOT structurally normal (assoc applies)
--   - For the bootstrap, beta-normality is what matters for correctness
------------------------------------------------------------------------

record CorrectNormalizer (N : Term TermCode' TermCode') : Set where
  field
    -- N terminates on all inputs (produces a result)
    terminates : ∀ (t : Term Unit TermCode') →
                 ∃[ result ] ((N ∘ t) ⟶* result)

    -- N produces beta-normal forms
    -- (The result has no computational redexes, though structural rewrites may apply)
    produces-betanf : ∀ (t : Term Unit TermCode') →
                      ∀ {result} → (N ∘ t) ⟶* result → IsBetaNormalForm result

    -- N preserves semantics (result equivalent to input)
    preserves : ∀ (t : Term Unit TermCode') →
                ∀ {result} → (N ∘ t) ⟶* result →
                ∃[ nf ] ((t ⟶* nf) × (result ⟶* nf))
