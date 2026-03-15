------------------------------------------------------------------------
-- Correctness: Proof that a normalizer is correct
--
-- Parameterized by the normalizer and its assumed properties.
-- No heavy imports - type-checks fast.
-- Instantiated with concrete normalize in MainTheorem.
------------------------------------------------------------------------

open import normalizer.Foundations.Types
open import normalizer.Foundations.MinimalCCC
open import normalizer.Foundations.Encoding
  using (TermCode')
open import normalizer.Foundations.NormalForm
  using (IsNormalForm)

module normalizer.Level0V2.MainTheorem.Correctness
  (normalize : Term TermCode' TermCode')
  (normalize-produces-nf : ∀ (t : Term Unit TermCode') →
                           IsNormalForm (normalize ∘ t))
  (strong-normalization : ∀ {A B} (t : Term A B) →
                          ∃[ nf ] ((t ⟶* nf) × IsNormalForm nf))
  (normalize-preserves-semantics : ∀ (t : Term Unit TermCode') →
                                   ((normalize ∘ t) ⟶* t) ⊎ (t ⟶* (normalize ∘ t)))
  (confluence : ∀ {A B} {t u v : Term A B} →
                t ⟶* u → t ⟶* v →
                ∃[ w ] ((u ⟶* w) × (v ⟶* w)))
  where

------------------------------------------------------------------------
-- Re-export the record definition
------------------------------------------------------------------------

open import normalizer.Level0V2.MainTheorem.Correctness.Record public

------------------------------------------------------------------------
-- Import the parameterized proofs
------------------------------------------------------------------------

open import normalizer.Level0V2.MainTheorem.Correctness.Terminates
  normalize strong-normalization
  public

open import normalizer.Level0V2.MainTheorem.Correctness.ProducesNF
  normalize normalize-produces-nf
  public

open import normalizer.Level0V2.MainTheorem.Correctness.Preserves
  normalize normalize-preserves-semantics confluence
  public

------------------------------------------------------------------------
-- The Concrete Theorem: The normalizer is correct
------------------------------------------------------------------------

normalizer-correct : CorrectNormalizer normalize
normalizer-correct = record
  { terminates  = normalize-terminates
  ; produces-nf = normalize-output-is-nf
  ; preserves   = normalize-preserves
  }
