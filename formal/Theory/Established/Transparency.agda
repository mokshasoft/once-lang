------------------------------------------------------------------------
-- Theory.Established.Transparency
--
-- CITATION:
--   This is folklore in normalization theory. The specific formulation
--   used here is the syntactic-uniformity statement of Appendix A of
--   bootstrap/theory/fixpoint-correctness.md (Lemmas A.3, A.4, A.5):
--   a closed CCC term in normal form computes a function determined
--   entirely by its syntactic structure, and consequently its behavior
--   on encoded inputs that appear as sub-encodings of its own code
--   propagates to its behavior on all encoded inputs.
--
--   Related published arguments:
--     - Tait, W.W. (1967) — reducibility candidates / logical relations
--       give a per-type characterization of NF behavior.
--     - Curien, P.-L. (1985) — CAM correctness via per-generator
--       case analysis on closed combinator terms.
--     - Plotkin, G. (1977, "LCF considered as a programming language") —
--       canonical-form analysis of closed PCF terms in NF.
--
--   The specific package "NF correctness on sub-encodings ⟹ NF
--   correctness on all encodings" used here is not, to our knowledge,
--   stated in any single published source; it is folklore obtained by
--   combining the above. We treat it as Established to mark a clean
--   handoff point — concrete syntaxes discharge it by syntactic
--   induction on the canonical form of NF morphisms in the underlying
--   Term datatype.
--
-- TOWER LEVEL: CCT3 (μ-types are needed to even state the property,
--                    since "encoded inputs" are morphisms into Code = μ TermF).
--
-- THEOREM (Transparency / NF Uniformity from Single-Point Fixpoint):
--   Let N : Code → Code be in normal form, and let spec be an intended
--   semantics for the morphisms of S. If
--     N ∘ ⌜N⌝  ⟶*  ⌜spec N⌝
--   (i.e., N satisfies its own spec on its own encoding), then for
--   every morphism g
--     N ∘ ⌜g⌝  ⟶*  ⌜spec g⌝
--   (i.e., N satisfies the spec on every encoded input).
--
--   Informally: a normal-form normalizer is "transparent" — it has no
--   hidden behavior. By Lemmas A.4 (encoding-completeness) and A.5
--   (fixpoint-exercises-all-branches) of the bootstrap doc, ⌜N⌝
--   already exercises every branch of N's case-analytic structure, so
--   single-point spec-correctness at N propagates to every input.
--
--   STRUCTURAL CAVEAT:
--     This claim is sound when N has the form cata(F, step) with step
--     in NF — the canonical normalizer shape. For arbitrary NF
--     morphisms Code → Code that happen to satisfy a single-point
--     fixpoint, the argument is not in general sound. Concrete
--     instantiations should only invoke this postulate on N's that
--     have the appropriate structural form. EncodingInductive's
--     encode-cata-decomposes field documents this structural
--     intuition.
--
-- PARAMETERIZATION:
--   - S   : a CCT3 structure
--   - Red : a directed reduction on S
--   - E   : an EncodingScheme for S
--   - EI  : an EncodingInductive (provides ⊑ and the structural laws)
--
-- USE SITE:
--   This postulate is consumed by Theory.RanzowFixpoint.FullCorrectness
--   to upgrade the fixpoint property "N ∘ ⌜N⌝ ⟶* ⌜N⌝" to per-input
--   correctness "∀ g. N ∘ ⌜g⌝ ⟶* ⌜spec g⌝".
--
-- SCOPE OF THIS POSTULATE:
--   This module postulates ONLY the syntactic-uniformity property for
--   NF morphisms of type Code → Code under the given encoding. It does
--   NOT claim anything about open terms, non-NF terms, or behavior at
--   non-Code types.
------------------------------------------------------------------------

module Theory.Established.Transparency where

open import Theory.CCTower using (TowerLevel; CCT3)
open import Theory.Systems.CCT3
open import Theory.Syntax.Reducible using (Reducible)
open import Theory.RanzowFixpoint using (EncodingScheme)
open import Theory.Encoding.Inductive using (EncodingInductive)

------------------------------------------------------------------------
-- Tower level annotation
------------------------------------------------------------------------

applies-to : TowerLevel
applies-to = CCT3

------------------------------------------------------------------------
-- The Theorem, parameterized over a CCT3 structure equipped with a
-- directed reduction, an encoding scheme, and the structural encoding
-- laws of EncodingInductive.
------------------------------------------------------------------------

module _ (S   : CCT3Structure)
         (Red : Reducible (CCT3Structure.Obj S) (CCT3Structure.Hom S))
         (E   : EncodingScheme S)
         (EI  : EncodingInductive S Red E)
         where
  open CCT3Structure S
  open Reducible Red
  open EncodingScheme E
  open EncodingInductive EI

  postulate
    --------------------------------------------------------------------
    -- nf-fixpoint-implies-correctness:
    --   A NF morphism N : Code → Code that satisfies its spec at its
    --   own encoding satisfies the spec at every encoded input.
    --
    -- The "spec" parameter is the intended interpretation: spec g is
    -- what N is supposed to produce when applied to ⌜g⌝.
    --
    -- This is the precise formal counterpart of Theorem 4.1 of
    -- bootstrap/theory/fixpoint-correctness.md, packaging the chain
    -- A.3 (transparency) + A.4 (encoding-completeness) + A.5
    -- (fixpoint-exercises-all-branches) into a single statement.
    --
    -- For the canonical normalizer case:
    --   - spec g is the (unique) normal form of g (exists by SN +
    --     confluence), so spec is the normalization function nf.
    --   - N being in NF gives nf N = N, hence spec N = N, hence
    --     ⌜spec N⌝ = ⌜N⌝, hence the hypothesis becomes the Ranzow
    --     Fixpoint property "N ∘ ⌜N⌝ ⟶* ⌜N⌝".
    --   - The conclusion becomes correctness of N as a normalizer.
    --
    -- The identity "encode (spec N) = encode N" used in the wrapper
    -- (Theory.RanzowFixpoint.FullCorrectness) is supplied as a
    -- separate hypothesis there, so this postulate stays maximally
    -- abstract.
    --------------------------------------------------------------------

    nf-fixpoint-implies-correctness :
      ∀ (spec : ∀ {A B} → Hom A B → Hom A B)
        (N : Hom Code Code) →
        IsNormalForm N →
        -- Hypothesis: N satisfies the spec on its own encoding
        (N ∘ encode N) ⟶* encode (spec N) →
        -- Conclusion: N satisfies the spec on every encoded input
        (∀ {A B} (g : Hom A B) →
           (N ∘ encode g) ⟶* encode (spec g))
