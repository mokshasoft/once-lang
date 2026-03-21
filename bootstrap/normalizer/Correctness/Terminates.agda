------------------------------------------------------------------------
-- Correctness.Terminates: Termination proof
--
-- Parameterized by normalize and strong-normalization assumption.
-- No heavy imports - type-checks fast.
------------------------------------------------------------------------

open import normalizer.Foundations.Types
open import normalizer.Foundations.CCC
open import normalizer.Foundations.Encoding
  using (TermCode')
open import normalizer.Foundations.NormalForm
  using (IsNormalForm)

module normalizer.Correctness.Terminates
  (normalize : Term TermCode' TermCode')
  (strong-normalization : ∀ {A B} (t : Term A B) →
                          ∃[ nf ] ((t ⟶* nf) × IsNormalForm nf))
  where

------------------------------------------------------------------------
-- Termination proof
------------------------------------------------------------------------

-- Follows directly from strong-normalization
abstract
  normalize-terminates : ∀ (t : Term Unit TermCode') →
                         ∃[ result ] ((normalize ∘ t) ⟶* result)
  normalize-terminates t with strong-normalization (normalize ∘ t)
  ... | nf , (reduction , _) = nf , reduction
