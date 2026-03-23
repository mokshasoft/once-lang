------------------------------------------------------------------------
-- TCB0: Trusted Computing Base Zero
--
-- This module collects proofs about the normalizer that are verified
-- directly by Agda's type-checker through structural induction.
--
-- Key theorem: fixpoint-property
--   (normalize ∘ encode normalize) ⟶* encode normalize
--
-- This shows that when the normalizer processes its own encoding,
-- it produces that encoding unchanged (up to reduction).
------------------------------------------------------------------------

module normalizer.TCB0 where

------------------------------------------------------------------------
-- Core Definitions
------------------------------------------------------------------------

-- The normalizer definition
open import normalizer.TCB0.Normalizer.Definition
  using ( normalize           -- The normalizer: cata TermF normalize-step
        ; normalize-step      -- The normalization algebra
        ; normalize-noredex   -- NoRedex (by case analysis on handlers)
        ; normalize-encoded   -- The normalizer as encoded data
        ; normalize-encoded-def  -- normalize-encoded ≡ encode normalize
        )
  public

------------------------------------------------------------------------
-- Key Theorems
------------------------------------------------------------------------

-- The main fixpoint theorem: normalizing the normalizer's encoding
-- produces that same encoding.
-- Derived: instantiates noredex-fixpoint with normalize and normalize-noredex
open import normalizer.TCB0.Normalizer.NoRedexFixpoint
  using ( fixpoint-property   -- (normalize ∘ encode normalize) ⟶* encode normalize
        )
  public

-- For any NoRedex t: (normalize ∘ encode t) ⟶* encode t
-- Derived: by structural induction on t, using AlgebraSpec satisfaction
open import normalizer.TCB0.Normalizer.SelfFixpoint
  using ( noredex-fixpoint
        )
  public

-- Refold idempotency: cata TermF In is identity on encodings
-- Derived: by structural induction on t
open import normalizer.TCB0.RefoldIdempotent
  using ( refold-idempotent   -- (cata TermF In ∘ encode t) ⟶* encode t
        )
  public

------------------------------------------------------------------------
-- Supporting Infrastructure
------------------------------------------------------------------------

-- Spec satisfaction: the normalizer algebra satisfies the spec
-- Derived: by case analysis on each handler
open import normalizer.TCB0.Compiler.SatisfiesSpec
  using ( normalize-spec        -- NormalizerSpecSimple normalize-step
        ; spec-implies-fixpoint -- Spec implies noredex-fixpoint
        )
  public

------------------------------------------------------------------------
-- Proof Structure
--
-- The proof chain uses structural induction verified by Agda:
--
--   1. normalize-step is defined (Handlers.agda)
--   2. normalize = cata TermF normalize-step (Definition.agda)
--   3. normalize-spec: satisfies AlgebraSpec (by case analysis)
--   4. noredex-fixpoint: follows from spec (by structural induction on t)
--   5. fixpoint-property: instantiates noredex-fixpoint for normalize
--
-- Results from Axioms/EstablishedMath.agda are NOT used here.
-- Those are needed for:
--   - strong-normalization (general termination)
--   - confluence (general confluence)
--   - normalize-semantics-equiv (semantic preservation)
--
-- TCB0 establishes the bootstrap property through direct induction.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Extended Theory: MinimalTheory
--
-- For UNIQUENESS of normal forms (not just existence), see:
--   normalizer.MinimalTheory
--
-- MinimalTheory combines TCB0 with standard CCC confluence
-- (Lambek & Scott) to derive:
--
--   - normalizer-unique     : NoRedex t → unique normal form
--   - fixpoint-unique       : The fixpoint has a unique normal form
--   - canonical-normal-form : NoRedex t → any nf is encode t
--
-- Trust levels:
--   TCB0          : Structural induction only
--   MinimalTheory : + Standard CCC confluence
--   Main          : + All EstablishedMath results
------------------------------------------------------------------------

------------------------------------------------------------------------
-- COMPILER VERIFICATION INTERFACE
--
-- The key theorems for verifying compilers and other programs:
--
-- 1. EXISTENCE (this module):
--      noredex-fixpoint : NoRedex t →
--                         (normalize ∘ encode t) ⟶* encode t
--
--    "Normalizing any encoded NoRedex term reduces to that encoding."
--    Derived by structural induction on t.
--
-- 2. UNIQUENESS (MinimalTheory):
--      canonical-normal-form : NoRedex t →
--                              (normalize ∘ encode t) ⟶* u →
--                              IsNormalForm u →
--                              u ≡ encode t
--
--    "Any normal form is exactly the original encoding."
--    Derived from existence + confluence.
--
-- Together these give the CANONICAL FORM PROPERTY:
--
--    The normalizer faithfully preserves NoRedex terms.
--
-- This is exactly what bootstrapping requires: when the normalizer
-- processes its own encoding (or any well-formed program), it
-- produces that program's encoding as output.
--
-- For applications:
--   - Compiler correctness: input encoding = output encoding
--   - Program equivalence: normalize respects NoRedex identity
--   - Bootstrap verification: the normalizer compiles itself correctly
------------------------------------------------------------------------
