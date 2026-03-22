------------------------------------------------------------------------
-- NormalizerSpec: Specification for a correct normalizer algebra
--
-- This module defines the NormalizerSpec record, which captures what
-- any correct normalizer algebra must satisfy. The key insight is:
--
--   If an algebra preserves encodings of NoRedex terms (up to reduction),
--   then the catamorphism built from that algebra achieves the fixpoint
--   property: (N ∘ encode t) ⟶* encode t for all NoRedex t.
--
-- This separates:
--   - The SPEC (what any correct algebra must satisfy)
--   - The GENERIC THEOREM (spec implies fixpoint, by structural induction)
--   - The CONCRETE PROOF (our normalize-step satisfies the spec)
--
-- The spec moves complexity from 15 interwoven cases in a monolithic
-- proof to: 1 generic theorem + 14 trivial proofs + 1 real proof.
------------------------------------------------------------------------

module normalizer.Correctness.NormalizerSpec where

open import normalizer.Foundations.Types
open import normalizer.Foundations.CCC
open import normalizer.Foundations.Encoding
open import normalizer.Foundations.NoRedex

------------------------------------------------------------------------
-- Helper: Extract the payload of an encoded term
--
-- For encoded terms, we can describe how the algebra interacts with
-- the encoding structure. The key is that `encode t` has the form:
--   In ∘ inj-N ∘ payload
--
-- Where `payload` contains:
--   - Type information (TyFuncCode values)
--   - Recursively encoded subterms (TermCode' values)
--
-- The catamorphism unfolds this to:
--   alg ∘ fmap TermF N ∘ inj-N ∘ payload
--
-- And the fmap distributes through the injections to apply N to
-- the recursive positions.
------------------------------------------------------------------------

-- For each term constructor, we define what it means for the algebra
-- to "preserve" that constructor's encoding.
--
-- The idea: after N is applied to all subterms, the algebra should
-- produce the same encoding as if we just re-encoded.
--
-- For atoms (no recursive subterms): alg ∘ inj-X ∘ payload ⟶* In ∘ inj-X ∘ payload
-- For recursive terms: alg ∘ inj-X ∘ ⟨encode f, encode g⟩ ⟶* In ∘ inj-X ∘ ⟨encode f, encode g⟩
--   (assuming N ∘ encode f ⟶* encode f and N ∘ encode g ⟶* encode g already)

------------------------------------------------------------------------
-- The Specification Record
--
-- A normalizer algebra is specified by a single property:
-- For NoRedex terms, after the fmap brings normalized subterms,
-- the algebra produces the same result as just wrapping with In.
--
-- In other words: on NoRedex data, the algebra behaves like In.
------------------------------------------------------------------------

record NormalizerSpec (alg : Term (⟦ TermF ⟧F TermCode') TermCode') : Set where
  field
    -- The algebra preserves encodings of NoRedex terms.
    --
    -- More precisely: For any NoRedex term t, after recursively normalizing
    -- subterms (which by IH returns them unchanged), the algebra applied to
    -- the resulting payload produces a term that reduces to the original encoding.
    --
    -- The key insight is that this is the ONLY thing we need to prove about
    -- the algebra. Once we have this, structural induction gives us fixpoint.
    --
    -- For simple handlers (handle-X = rebuild-N = In ∘ inj-N), this is trivial.
    -- For handle-comp, this requires showing the is-id checks return inr on
    -- NoRedex inputs (which uses is-id-noredex lemmas).
    --
    alg-preserves : ∀ {A B} (t : Term A B) → NoRedex t →
                    ∀ (normalized-payload : Term Unit (⟦ TermF ⟧F TermCode')) →
                    -- The payload encodes the "shape" of t with subterms already normalized
                    -- For this version, we state the property at the full term level:
                    -- The normalizer built from alg achieves fixpoint on encode t
                    (alg ∘ normalized-payload) ⟶* (In ∘ normalized-payload)

  -- The normalizer derived from the algebra
  N : Term TermCode' TermCode'
  N = cata TermF alg

------------------------------------------------------------------------
-- Alternative formulation: Position-based spec
--
-- Instead of parameterizing over arbitrary payloads, we could state
-- the spec position-by-position. This makes the proofs more direct.
------------------------------------------------------------------------

-- Each position has a specific payload type:
--   Position 0 (id):       TyFuncCode
--   Position 1 (comp):     TermCode' * TermCode'
--   Position 2 (fst):      TyFuncCode * TyFuncCode
--   Position 3 (snd):      TyFuncCode * TyFuncCode
--   Position 4 (pair):     TermCode' * TermCode'
--   Position 5 (inl):      TyFuncCode * TyFuncCode
--   Position 6 (inr):      TyFuncCode * TyFuncCode
--   Position 7 (case):     TermCode' * TermCode'
--   Position 8 (terminal): TyFuncCode
--   Position 9 (initial):  TyFuncCode
--   Position 10 (In):      TyFuncCode
--   Position 11 (Out):     TyFuncCode
--   Position 12 (cata):    TyFuncCode * TermCode'
--   Position 13 (curry):   (TyFuncCode * TyFuncCode) * (TyFuncCode * TermCode')
--   Position 14 (apply):   TyFuncCode * TyFuncCode

-- The simple version: alg acts like In on NoRedex inputs
-- This is what we'll actually prove and use.

record NormalizerSpecSimple (alg : Term (⟦ TermF ⟧F TermCode') TermCode') : Set where
  field
    -- For the composition position (the only non-trivial case):
    -- When neither component is id (which NoRedex requires),
    -- handle-comp falls through to rebuild-1
    alg-comp-noredex : ∀ {A B C} {f : Term B C} {g : Term A B} →
                       NoRedex f → NoRedex g →
                       NotIdStruct f → NotIdStruct g →
                       (alg ∘ inr ∘ inl ∘ ⟨ encode f , encode g ⟩) ⟶*
                       (In ∘ inr ∘ inl ∘ ⟨ encode f , encode g ⟩)

  -- The normalizer
  N : Term TermCode' TermCode'
  N = cata TermF alg
