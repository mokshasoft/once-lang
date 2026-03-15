------------------------------------------------------------------------
-- Correctness.ProducesNF: Normal form production proof
--
-- Parameterized by normalize and normalize-produces-nf assumption.
-- No heavy imports - type-checks fast.
------------------------------------------------------------------------

open import normalizer.Foundations.Types
open import normalizer.Foundations.MinimalCCC
open import normalizer.Foundations.Encoding
  using (TermCode')
open import normalizer.Foundations.NormalForm
  using (IsNormalForm; nf-stable)

module normalizer.Level0V2.MainTheorem.Correctness.ProducesNF
  (normalize : Term TermCode' TermCode')
  (normalize-produces-nf : ∀ (t : Term Unit TermCode') →
                           IsNormalForm (normalize ∘ t))
  where

------------------------------------------------------------------------
-- Normal form production proof
------------------------------------------------------------------------

-- The result of normalize is a normal form.
--
-- Key insight: normalize-produces-nf tells us (normalize ∘ t) is already
-- in normal form. By nf-stable, any reduction from it must be trivial (≡).
-- Therefore the result must equal (normalize ∘ t) and thus be normal.
abstract
  normalize-output-is-nf : ∀ (t : Term Unit TermCode') →
                           ∀ {result} → (normalize ∘ t) ⟶* result →
                           IsNormalForm result
  normalize-output-is-nf t {result} reduction =
    subst IsNormalForm (nf-stable (normalize-produces-nf t) reduction)
                       (normalize-produces-nf t)
