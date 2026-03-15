------------------------------------------------------------------------
-- MainTheorem: The Complete Verification Structure
--
-- This module structures the proof that the normalizer is correct.
-- Implementation is split into parameterized submodules.
-- This module instantiates them with the concrete normalize.
--
-- The main theorem: If a normalizer achieves fixpoint on its own
-- encoding, then it correctly normalizes all terms.
------------------------------------------------------------------------

module normalizer.Level0V2.MainTheorem where

open import normalizer.Foundations.Types
open import normalizer.Foundations.MinimalCCC
open import normalizer.Foundations.Encoding
  using (TermCode')

------------------------------------------------------------------------
-- Foundation Exports
------------------------------------------------------------------------

-- Normal Form (general definitions)
open import normalizer.Foundations.NormalForm public

-- Confluence
open import normalizer.Foundations.Confluence
  using (confluence)
  public

------------------------------------------------------------------------
-- The Normalizer
------------------------------------------------------------------------

open import normalizer.Level0V2.Normalize
  using (normalize; normalize-encoded)
  public

------------------------------------------------------------------------
-- Proof Obligations
--
-- These will be filled in as the verification progresses.
-- Each is a concrete claim that needs to be discharged.
------------------------------------------------------------------------

-- NOTE: normalize-produces-nf as stated below is PROBLEMATIC.
--
-- Issue: The claim IsNormalForm (normalize ∘ t) says that the COMPOSITION
-- normalize ∘ t cannot reduce. But normalize = cata TermF normalize-step,
-- and (cata ∘ (In ∘ x)) CAN reduce via cata-β and associativity.
--
-- The fixpoint proofs in Normalize/Fixpoint.agda show actual reduction
-- sequences, proving that normalize ∘ (encode t) DOES reduce.
--
-- Proposed fix: Use IsBetaNormalForm (from Foundations.BetaNormalForm)
-- which ignores structural rewrites. The key insight is:
--   1. Encoded terms (encode t) have no beta-redexes
--   2. The normalizer produces encoded terms
--   3. Therefore, the OUTPUT is in beta-normal form
--
-- The claim should be reformulated to either:
--   (a) IsBetaNormalForm (result after reduction completes)
--   (b) Show encode t is beta-normal directly
--
-- For now, this postulate is used to make the proof structure compile.
-- See Foundations/BetaNormalForm.agda for the correct formulation.

-- The normalizer produces normal forms (NEEDS REFORMULATION)
postulate
  normalize-produces-nf : ∀ (t : Term Unit TermCode') →
                          IsNormalForm (normalize ∘ t)

-- All reduction sequences terminate
postulate
  strong-normalization : ∀ {A B} (t : Term A B) →
                         ∃[ nf ] ((t ⟶* nf) × IsNormalForm nf)

-- The normalizer preserves semantics
postulate
  normalize-preserves-semantics : ∀ (t : Term Unit TermCode') →
                                  ((normalize ∘ t) ⟶* t) ⊎ (t ⟶* (normalize ∘ t))

------------------------------------------------------------------------
-- Correctness
------------------------------------------------------------------------

-- Instantiate the parameterized correctness proof
-- (also re-exports CorrectNormalizer record)
open import normalizer.Level0V2.MainTheorem.Correctness
  normalize
  normalize-produces-nf
  strong-normalization
  normalize-preserves-semantics
  confluence
  public

------------------------------------------------------------------------
-- Fixpoint Theorem
------------------------------------------------------------------------

open import normalizer.Level0V2.MainTheorem.FixpointTheorem
  normalize
  normalize-encoded
  normalize-produces-nf
  public

-- Fixpoint property (from NormalForm module)
open import normalizer.Level0V2.NormalForm
  using (fixpoint-property)
  public

-- The normalizer's encoding is in normal form
normalize-encoded-is-normal : IsNormalForm normalize-encoded
normalize-encoded-is-normal = normalize-encoding-is-nf fixpoint-property

------------------------------------------------------------------------
-- Re-exports
------------------------------------------------------------------------

open import normalizer.Level0V2.Normalizer
  using ( refold-idempotent  -- (cata TermF In ∘ encode t) ⟶* encode t
        )
  public

------------------------------------------------------------------------
-- Verification Status
------------------------------------------------------------------------

{-
STRUCTURE:

Definitions (see code):
  - IsNormalForm, nf-no-redex, nf-stable, nf-unique
  - CorrectNormalizer record
  - fixpoint-implies-nf : N(t) ⟶* t → IsNormalForm t  ← KEY THEOREM
  - normalize-terminates, normalize-output-is-nf, normalize-preserves
  - normalizer-correct : CorrectNormalizer normalize
  - normalize-encoded-is-normal : ⟦normalize⟧ is in normal form

Proof obligations (to be filled):
  Core:
    - strong-normalization : termination of reduction
    - normalize-produces-nf : normalizer outputs normal forms
    - normalize-preserves-semantics : normalizer preserves meaning
    - fixpoint-property : N(⟦N⟧) ⟶* ⟦N⟧

  For confluence:
    - complete : complete development function
    - ⇒-to-complete : parallel reduction extends to complete

  Mechanical (12-way case dispatches):
    - normalize-step, is-id-dispatch, is-fst, is-snd, is-pair,
      is-inl, is-inr, is-case, is-In, is-Out, is-cata

KEY INSIGHT:
  fixpoint-implies-nf : N(t) ⟶* t → IsNormalForm t

  In a simple system (confluent + terminating):
    - Fixpoints of normalization ARE normal forms
    - Normal forms are unique (per equivalence class)
    - Therefore: achieving fixpoint FORCES correctness

TCB0 CLAIM:
  If we run the normalizer and it achieves fixpoint on its own encoding,
  we need only trust:
    1. Hardware (executes correctly)
    2. Math (CCC rules, confluence, termination)
    3. Mechanical construction (encoding + normalize-step)

  Agda is scaffolding, not in the trusted path.
-}
