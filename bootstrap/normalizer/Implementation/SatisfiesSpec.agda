------------------------------------------------------------------------
-- SatisfiesSpec: Proof that normalize-step satisfies NormalizerSpec
--
-- This module proves that our concrete normalize-step algebra satisfies
-- the NormalizerSpecSimple specification. This consists of:
--
--   1. alg-comp-noredex: handle-comp falls through to rebuild-1 on
--      NoRedex compositions where neither operand is id
--
-- Most handlers (14 out of 15) are trivial because they're just
-- rebuild-N = In ∘ inj-N. Only handle-comp needs a real proof,
-- which uses the is-id-noredex lemma.
--
-- Combined with SpecImpliesFixpoint, this gives us noredex-fixpoint.
------------------------------------------------------------------------

module normalizer.Implementation.SatisfiesSpec where

open import normalizer.Foundations.Types
open import normalizer.Foundations.CCC
open import normalizer.Foundations.Encoding
open import normalizer.Foundations.NoRedex
open import normalizer.Foundations.ReductionCombinators
open import normalizer.Correctness.NormalizerSpec

-- Import the handlers and normalize-step
open import normalizer.Implementation.Normalize.Handlers
  using (normalize-step; normalize; handle-comp)

-- Import the existing fixpoint proof (which includes handle-comp-rebuild)
open import normalizer.Implementation.Normalize.Fixpoint.MainTheorem
  using (noredex-fixpoint)

-- Import the key lemma for composition (brings in handle-comp-rebuild)
open import normalizer.Implementation.Normalize.Fixpoint.DispatchLemmas
  using (handle-comp-rebuild; nstep-at-1'; ∘-cong-left'; ∘-cong-right')

------------------------------------------------------------------------
-- Proof that normalize-step satisfies NormalizerSpecSimple
------------------------------------------------------------------------

-- The comp case uses handle-comp-rebuild from DispatchLemmas
private
  alg-comp-proof : ∀ {A B C} {f : Term B C} {g : Term A B} →
                   NoRedex f → NoRedex g →
                   NotIdStruct f → NotIdStruct g →
                   (normalize-step ∘ inr ∘ inl ∘ ⟨ encode f , encode g ⟩) ⟶*
                   (In ∘ inr ∘ inl ∘ ⟨ encode f , encode g ⟩)
  alg-comp-proof {f = f} {g = g} nrf nrg nisf nisg =
    -- normalize-step ∘ inr ∘ inl ∘ payload
    -- ⟶ handle-comp ∘ payload   (by case dispatch)
    -- ⟶* (In ∘ inr ∘ inl) ∘ payload   (by handle-comp-rebuild)
    -- ⟶* In ∘ inr ∘ inl ∘ payload   (by associativity)
    step1 >> step2 >> step3
    where
      payload : Term Unit (TermCode' * TermCode')
      payload = ⟨ encode f , encode g ⟩

      -- Step 1: normalize-step ∘ inr ∘ inl ⟶ handle-comp
      -- This follows from the structure of normalize-step as nested cases
      step1 : (normalize-step ∘ inr ∘ inl ∘ payload) ⟶* (handle-comp ∘ payload)
      step1 = ⟶1 assoc-l >> ⟶1 assoc-l >> ∘-cong-left' payload nstep-at-1'

      -- Step 2: handle-comp ∘ payload ⟶* (In ∘ inr ∘ inl) ∘ payload
      step2 : (handle-comp ∘ payload) ⟶* ((In ∘ inr ∘ inl) ∘ payload)
      step2 = handle-comp-rebuild nrf nrg nisf nisg

      -- Step 3: (In ∘ inr ∘ inl) ∘ payload ⟶* In ∘ inr ∘ inl ∘ payload
      step3 : ((In ∘ inr ∘ inl) ∘ payload) ⟶* (In ∘ inr ∘ inl ∘ payload)
      step3 = ⟶1 assoc-r >> ∘-cong-right' In (⟶1 assoc-r)

------------------------------------------------------------------------
-- The spec instance
------------------------------------------------------------------------

normalize-spec : NormalizerSpecSimple normalize-step
normalize-spec = record
  { alg-comp-noredex = alg-comp-proof
  }

------------------------------------------------------------------------
-- The fixpoint property via the spec
--
-- We now instantiate SpecImpliesFixpoint with our spec and proof.
------------------------------------------------------------------------

-- Re-export noredex-fixpoint from the existing infrastructure
-- This is the same theorem, just now understood through the spec lens.
open import normalizer.Correctness.SpecImpliesFixpoint
  normalize-step
  normalize-spec
  noredex-fixpoint
  public

------------------------------------------------------------------------
-- Summary of what we export:
--
--   normalize-spec : NormalizerSpecSimple normalize-step
--   spec-implies-fixpoint : ∀ t → NoRedex t → (normalize ∘ encode t) ⟶* encode t
--
-- The spec-implies-fixpoint is just noredex-fixpoint, but now understood
-- as an instance of the generic pattern: spec satisfaction implies fixpoint.
------------------------------------------------------------------------
