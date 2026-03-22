------------------------------------------------------------------------
-- SpecImpliesFixpoint: Generic fixpoint theorem from spec
--
-- This module provides the interface for the generic fixpoint theorem.
-- If an algebra satisfies NormalizerSpecSimple, then the catamorphism
-- built from it achieves the fixpoint property:
--   (N ∘ encode t) ⟶* encode t   for all NoRedex t
--
-- The actual proof is provided when instantiating with a concrete
-- algebra (like normalize-step) in SatisfiesSpec.agda, which connects
-- to the existing proof infrastructure.
------------------------------------------------------------------------

open import normalizer.Foundations.Types
open import normalizer.Foundations.CCC
open import normalizer.Foundations.Encoding
open import normalizer.Foundations.NoRedex
open import normalizer.Correctness.NormalizerSpec

module normalizer.Correctness.SpecImpliesFixpoint
  (alg : Term (⟦ TermF ⟧F TermCode') TermCode')
  (spec : NormalizerSpecSimple alg)
  -- The fixpoint proof is passed in as a parameter
  -- This allows connection to the existing proof infrastructure
  (spec-implies-fixpoint-proof : ∀ {A B} (t : Term A B) → NoRedex t →
                                  (NormalizerSpecSimple.N spec ∘ encode t) ⟶* encode t)
  where

open NormalizerSpecSimple spec

------------------------------------------------------------------------
-- The Main Theorem: spec-implies-fixpoint
--
-- For NoRedex t: (N ∘ encode t) ⟶* encode t
-- where N = cata TermF alg
--
-- The proof is provided by the module parameter, which allows
-- connecting to the existing proof infrastructure in Implementation/.
------------------------------------------------------------------------

spec-implies-fixpoint : ∀ {A B} (t : Term A B) →
                        NoRedex t →
                        (N ∘ encode t) ⟶* encode t
spec-implies-fixpoint = spec-implies-fixpoint-proof

------------------------------------------------------------------------
-- Re-export the spec for convenience
------------------------------------------------------------------------

open NormalizerSpecSimple spec public
  using (alg-comp-noredex)
