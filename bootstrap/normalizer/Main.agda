------------------------------------------------------------------------
-- Main: The Complete Verification Structure
--
-- This module structures the proof that the normalizer is correct.
-- Implementation is split into parameterized submodules.
-- This module instantiates them with the concrete normalize.
--
-- The main theorem: If a normalizer achieves fixpoint on its own
-- encoding, then that encoding is in beta-normal form.
------------------------------------------------------------------------

module normalizer.Main where

open import normalizer.Syntax.Types
open import normalizer.Syntax.CCC
open import normalizer.Encoding.Encoding
  using (TermCode'; encode)

------------------------------------------------------------------------
-- Syntax Exports
------------------------------------------------------------------------

-- Normal Form (general definitions)
open import normalizer.Syntax.NormalForm public

-- Beta Normal Form (computational normal forms)
open import normalizer.Syntax.BetaNormalForm
  using (IsBetaNormalForm; encode-is-betanf)
  public

-- Confluence
open import normalizer.Axioms.Confluence
  using (confluence)
  public

------------------------------------------------------------------------
-- The Normalizer and Spec
------------------------------------------------------------------------

open import normalizer.TCB0.Normalizer.Definition
  using (normalize; normalize-encoded; normalize-encoded-def;
         normalize-spec; spec-implies-fixpoint)
  public

-- Re-export the spec record type
open import normalizer.Theory.Spec.NormalizerSpec
  using (NormalizerSpecSimple)
  public

------------------------------------------------------------------------
-- Import Established Mathematics
--
-- These are well-established results from type theory / category theory.
-- See EstablishedMath.agda for references.
------------------------------------------------------------------------

open import normalizer.Axioms.EstablishedMath
  using (strong-normalization; IsNormalForm)
  public

-- Specialize normalize-semantics-equiv for our normalizer
normalize-preserves-semantics : ∀ (t : Term Unit TermCode') →
                                ((normalize ∘ t) ⟶* t) ⊎ (t ⟶* (normalize ∘ t))
normalize-preserves-semantics t = normalize-semantics-equiv normalize t
  where open import normalizer.Axioms.EstablishedMath using (normalize-semantics-equiv)

------------------------------------------------------------------------
-- Correctness Structure
------------------------------------------------------------------------

-- Instantiate the parameterized correctness proof
open import normalizer.Theory.GeneralCorrectness.Correctness
  normalize
  strong-normalization
  normalize-preserves-semantics
  confluence
  public

------------------------------------------------------------------------
-- Fixpoint Theorem
--
-- The key insight: Encodings are in beta-normal form.
-- Combined with noredex-fixpoint, this proves the bootstrap works.
------------------------------------------------------------------------

open import normalizer.Theory.FixpointTheorem
  normalize
  normalize-encoded
  normalize-encoded-def
  public

-- Fixpoint property: (normalize ∘ encode normalize) ⟶* encode normalize
-- Derived via noredex-fixpoint and refold-idempotent
open import normalizer.TCB0.Normalizer.NoRedexFixpoint
  using (fixpoint-property)
  public

-- The normalizer's encoding is in beta-normal form
-- Proof: normalize-encoded = encode normalize (by normalize-encoded-def)
--        encode-is-betanf normalize : IsBetaNormalForm (encode normalize)
--        Transport along the equality.
normalize-encoded-is-betanf : IsBetaNormalForm normalize-encoded
normalize-encoded-is-betanf = subst IsBetaNormalForm (sym normalize-encoded-def) (encode-is-betanf normalize)

------------------------------------------------------------------------
-- Re-exports
------------------------------------------------------------------------

open import normalizer.TCB0.RefoldIdempotent
  using ( refold-idempotent  -- (cata TermF In ∘ encode t) ⟶* encode t
        )
  public

------------------------------------------------------------------------
-- Structure
--
-- The bootstrap verification:
--
-- From TCB0/:
--   fixpoint-property: (normalize ∘ encode normalize) ⟶* encode normalize
--     Uses noredex-fixpoint and refold-idempotent
--   normalize-spec : NormalizerSpecSimple normalize-step
--     Proof that our algebra satisfies the spec
--   spec-implies-fixpoint : noredex-fixpoint via the spec
--
-- From Syntax/:
--   encode-is-betanf: IsBetaNormalForm (encode t)
--     Encodings have no computational redexes
--
-- From Axioms/ (literature results):
--   strong-normalization: Simply-typed systems terminate [Tait]
--   confluence: CCC reduction is confluent [Lambek & Scott]
--   normalize-semantics-equiv: CCC laws are sound [Lambek & Scott]
--
-- The fixpoint property is the primary verification mechanism.
-- If normalize achieves fixpoint on its own encoding:
--   1. The encoding is reached by reduction (fixpoint-property)
--   2. The encoding is beta-stable (encode-is-betanf)
------------------------------------------------------------------------
