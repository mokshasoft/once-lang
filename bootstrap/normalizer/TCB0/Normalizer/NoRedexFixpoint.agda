------------------------------------------------------------------------
-- NormalForm: Theorems about terms without redexes
--
-- This module proves that terms without redexes are fixpoints of the
-- normalizer when encoded.
--
-- Key theorem: If t has no redexes, then normalize ∘ encode t ⟶* encode t
------------------------------------------------------------------------

module normalizer.TCB0.Normalizer.NoRedexFixpoint where

open import normalizer.Syntax.Types
open import normalizer.Syntax.CCC
open import normalizer.Encoding.Encoding

-- Import NoRedex definitions
open import normalizer.TCB0.Normalizer.NoRedexProof public

-- Import normalize, its NoRedex proof, and the fixpoint theorem
open import normalizer.TCB0.Normalizer.Definition
  using (normalize; normalize-noredex; normalize-encoded; normalize-encoded-def;
         noredex-fixpoint; normalize-spec; spec-implies-fixpoint)

------------------------------------------------------------------------
-- The Key Insight: normalize ≈ refold on NoRedex data
--
-- Both are catamorphisms with different algebras:
--   normalize = cata TermF normalize-step
--   refold    = cata TermF In
--
-- For NoRedex terms, they produce the same result because at each
-- position, normalize-step produces the same output as In:
--
-- Position 0 (id):     handle-id = In ∘ inl
-- Position 1 (comp):   handle-comp → In ∘ inr ∘ inl   (for NoRedex inputs)
-- Position 2 (fst):    handle-fst = In ∘ inr² ∘ inl
-- Position 3 (snd):    handle-snd = In ∘ inr³ ∘ inl
-- ... (all handle-X = In ∘ inj-X for X ≠ comp)
--
-- For position 1 (comp), handle-comp checks for redexes. When none
-- are found (NoRedex input), it produces In ∘ inr ∘ inl.
--
-- Therefore: For NoRedex t, normalize ∘ encode t ⟶* refold ∘ encode t
--
-- Combined with refold-idempotent: refold ∘ encode t ⟶* encode t
-- We get: normalize ∘ encode t ⟶* encode t
------------------------------------------------------------------------

open import normalizer.TCB0.RefoldIdempotent
  using (refold-idempotent)

------------------------------------------------------------------------
-- The Core Lemma: normalize ≈ refold on NoRedex data
--
-- This captures the algebra equivalence:
--   For NoRedex t: (normalize ∘ encode t) ⟶* (cata TermF In ∘ encode t)
--
-- Proof strategy (by structural induction on t):
--
-- 1. Base cases (atoms): Both normalize-step and In produce the same
--    handler after case dispatch. The case reduction gives the same result.
--
-- 2. Composition (f ∘ g) with NoRedex:
--    - handle-comp checks detect-id on f and g
--    - Since f ≠ id and g ≠ id (by NoRedex), detect-id returns inr for both
--    - handle-comp falls through to rebuild-1 = In ∘ inr ∘ inl
--    - This is exactly what In produces for composition
--
-- 3. Recursive cases (pair, case, curry, cata):
--    - Both algebras recursively apply themselves to subterms
--    - By IH, the recursive calls produce equivalent results
--    - The final result is equivalent
--
-- The proof is mechanical but requires tracking through:
-- - The 14-way case dispatch of normalize-step
-- - The nested case dispatch of handle-comp for position 1
-- - The detect-id function's behavior on non-id encodings
------------------------------------------------------------------------

------------------------------------------------------------------------
-- The Fixpoint Property
--
-- The main theorem noredex-fixpoint is in Normalize.agda since it
-- needs access to the abstract definition of normalize.
-- This module uses it to derive the fixpoint property for the
-- normalizer's own encoding.
------------------------------------------------------------------------

-- The normalizer itself has no redexes (see Normalize.agda).
-- Therefore it is a fixpoint when encoded.

fixpoint-from-noredex : (normalize ∘ encode normalize) ⟶* encode normalize
fixpoint-from-noredex = noredex-fixpoint normalize normalize-noredex

-- Version using normalize-encoded (for export to MainTheorem)
fixpoint-property : (normalize ∘ normalize-encoded) ⟶* normalize-encoded
fixpoint-property = subst (λ x → (normalize ∘ x) ⟶* x) (sym normalize-encoded-def) fixpoint-from-noredex

------------------------------------------------------------------------
-- Summary
--
-- After the spec refactoring, the structure is:
--
-- 1. NormalizerSpecSimple: The specification record that captures what
--    a correct normalizer algebra must satisfy (alg-comp-noredex).
--
-- 2. normalize-spec: Proof that normalize-step satisfies the spec.
--    Uses handle-comp-rebuild to show composition handler is correct.
--
-- 3. spec-implies-fixpoint: The generic theorem that spec satisfaction
--    implies the fixpoint property. Same as noredex-fixpoint.
--
-- 4. fixpoint-property: The normalizer's encoding is a fixpoint.
--
-- The key insight: the spec separates:
--   - WHAT any correct algebra must satisfy (spec definition)
--   - WHY spec implies fixpoint (generic induction)
--   - THAT our algebra satisfies spec (14 trivial + 1 real proof)
------------------------------------------------------------------------
