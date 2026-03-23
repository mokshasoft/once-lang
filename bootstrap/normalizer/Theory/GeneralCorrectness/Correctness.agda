------------------------------------------------------------------------
-- Correctness: Proof that a normalizer is correct
--
-- Parameterized by the normalizer and its assumed properties.
-- No heavy imports - type-checks fast.
-- Instantiated with concrete normalize in MainTheorem.
--
-- Key change from original: Uses IsBetaNormalForm instead of IsNormalForm.
-- For the bootstrap case, produces-betanf follows from:
--   1. noredex-fixpoint: (normalize ∘ encode t) ⟶* encode t
--   2. encode-is-betanf: IsBetaNormalForm (encode t)
------------------------------------------------------------------------

open import normalizer.Syntax.Types
open import normalizer.Syntax.CCC
open import normalizer.Encoding.Encoding
  using (TermCode'; encode)
open import normalizer.Syntax.BetaNormalForm
  using (IsBetaNormalForm; encode-is-betanf)
open import normalizer.Syntax.NormalForm
  using (IsNormalForm)

module normalizer.Theory.GeneralCorrectness.Correctness
  (normalize : Term TermCode' TermCode')
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

open import normalizer.Theory.GeneralCorrectness.Record public

------------------------------------------------------------------------
-- Import the parameterized proofs
------------------------------------------------------------------------

open import normalizer.Theory.GeneralCorrectness.Terminates
  normalize strong-normalization
  public

open import normalizer.Theory.GeneralCorrectness.ProducesNF
  normalize
  public

open import normalizer.Theory.GeneralCorrectness.Preserves
  normalize normalize-preserves-semantics confluence
  public

------------------------------------------------------------------------
-- Bootstrap-Specific Correctness
--
-- For the bootstrap, we don't need the general CorrectNormalizer record.
-- We need the specific facts:
--   1. (normalize ∘ encode normalize) ⟶* encode normalize  [fixpoint]
--   2. IsBetaNormalForm (encode normalize)                  [beta-stability]
--
-- The first is noredex-fixpoint (from NormalForm.agda).
-- The second is encode-is-betanf (from BetaNormalForm.agda).
--
-- Together, these prove the normalizer achieves a stable fixpoint.
------------------------------------------------------------------------
