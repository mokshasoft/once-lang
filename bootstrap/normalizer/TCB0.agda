------------------------------------------------------------------------
-- TCB0: Trusted Computing Base Zero - Postulate-Free Verification
--
-- This module collects all postulate-free proofs about the normalizer.
-- Everything here is proven by Agda's type-checker without any axioms.
--
-- Key theorem: fixpoint-property
--   (normalize ∘ encode normalize) ⟶* encode normalize
--
-- This proves that when the normalizer processes its own encoding,
-- it produces that encoding unchanged (up to reduction).
------------------------------------------------------------------------

module normalizer.TCB0 where

------------------------------------------------------------------------
-- Core Definitions (postulate-free)
------------------------------------------------------------------------

-- The normalizer definition
open import normalizer.TCB0.Normalizer.Definition
  using ( normalize           -- The normalizer: cata TermF normalize-step
        ; normalize-step      -- The normalization algebra
        ; normalize-noredex   -- NoRedex proof for the normalizer
        ; normalize-encoded   -- The normalizer as encoded data
        ; normalize-encoded-def  -- normalize-encoded ≡ encode normalize
        )
  public

------------------------------------------------------------------------
-- Key Theorems (postulate-free)
------------------------------------------------------------------------

-- The main fixpoint theorem: normalizing the normalizer's encoding
-- produces that same encoding.
open import normalizer.TCB0.Normalizer.NoRedexFixpoint
  using ( fixpoint-property   -- (normalize ∘ encode normalize) ⟶* encode normalize
        )
  public

-- For any NoRedex t: (normalize ∘ encode t) ⟶* encode t
open import normalizer.TCB0.Normalizer.SelfFixpoint
  using ( noredex-fixpoint
        )
  public

-- Refold idempotency: cata TermF In is identity on encodings
open import normalizer.TCB0.RefoldIdempotent
  using ( refold-idempotent   -- (cata TermF In ∘ encode t) ⟶* encode t
        )
  public

------------------------------------------------------------------------
-- Supporting Infrastructure (postulate-free)
------------------------------------------------------------------------

-- Spec satisfaction: the normalizer algebra satisfies the spec
open import normalizer.TCB0.Compiler.SatisfiesSpec
  using ( normalize-spec        -- NormalizerSpecSimple normalize-step
        ; spec-implies-fixpoint -- Spec implies noredex-fixpoint
        )
  public

------------------------------------------------------------------------
-- Structure
--
-- The proof chain is entirely postulate-free:
--
--   1. normalize-step is defined (Handlers.agda)
--   2. normalize = cata TermF normalize-step (Definition.agda)
--   3. normalize-spec proves it satisfies AlgebraSpec (SatisfiesSpec.agda)
--   4. noredex-fixpoint follows by structural induction (SelfFixpoint.agda)
--   5. fixpoint-property instantiates for normalize itself
--
-- No postulates from Axioms/ are used. Those are only needed for:
--   - strong-normalization (general termination)
--   - confluence (general confluence)
--   - normalize-semantics-equiv (semantic preservation)
--
-- TCB0 proves the bootstrap works without these general theorems.
------------------------------------------------------------------------
