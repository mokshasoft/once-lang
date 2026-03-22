------------------------------------------------------------------------
-- Level 0 Normalizer V2 - Concrete Approach
--
-- This module provides the concrete normalizer definitions.
-- The generic CCC catamorphism theory has been extracted to:
--   - Foundations/Catamorphisms.agda (fmap-id, cata-β-right, etc.)
--   - Foundations/OutIn.agda (out-in-compose, assoc helpers)
--   - Foundations/TermFunctor.agda (TermF decomposition, fmap lemmas)
--   - Correctness/RefoldIdempotent.agda (refold-idempotent proof)
--
-- This file now contains only the example normalizers and re-exports.
------------------------------------------------------------------------

module normalizer.Implementation.Normalizer where

-- Re-export the refactored components for backward compatibility
open import normalizer.Correctness.RefoldIdempotent public

------------------------------------------------------------------------
-- The Simplest Normalizer: Identity
------------------------------------------------------------------------

-- The identity function on encoded terms.
-- This is the trivial normalizer that doesn't actually normalize anything,
-- but it lets us verify the proof structure works.

N-id : Term TermCode' TermCode'
N-id = id

-- Fixpoint proof for identity normalizer:
-- N-id ∘ encode(N-id) ⟶* encode(N-id)
--
-- Proof: id ∘ t ⟶ t (by id-left), so id ∘ encode(id) ⟶ encode(id)

N-id-fixpoint : (N-id ∘ encode N-id) ⟶* encode N-id
N-id-fixpoint = step id-left done

-- Alternative proof using parallel reduction
N-id-fixpoint' : (N-id ∘ encode N-id) ⟶* encode N-id
N-id-fixpoint' = ⟹→⟶* (⟹-id-l (⟹-refl (encode N-id)))

------------------------------------------------------------------------
-- Key Insight: The Fixpoint is About Self-Reference
------------------------------------------------------------------------

-- The fixpoint property N ∘ encode(N) ⟶* encode(N) is really about
-- what happens when a normalizer encounters its own description.
--
-- For a normalizer to be a fixpoint, it must "recognize" its own encoding
-- and return it unchanged (after normalization).
--
-- The identity normalizer trivially satisfies this: id returns everything unchanged.
--
-- A cata-based normalizer processes the term structure. For it to be a fixpoint,
-- the processing must be idempotent on its own encoding.

------------------------------------------------------------------------
-- The fmap-id lemma (K case is definitional)
------------------------------------------------------------------------

-- For K functors, fmap is definitionally id
fmap-K-is-id : ∀ {X A B} (f : Term A B) → fmap (K X) f ≡ id
fmap-K-is-id f = refl
