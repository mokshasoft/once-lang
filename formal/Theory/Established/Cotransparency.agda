------------------------------------------------------------------------
-- Theory.Established.Cotransparency
--
-- CITATION:
--   Coinductive dual of Theory.Established.Transparency. Whereas
--   Transparency captures the syntactic-uniformity claim "a NF
--   morphism that satisfies its spec on its own encoding satisfies it
--   everywhere" (Tait/Plotkin/Curien folklore), Cotransparency states
--   the dual claim about productive corecursive transformations:
--
--     "A productive ana-form transformation that satisfies its spec at
--      its own co-encoding (up to bisimilarity) satisfies it for every
--      seed."
--
--   Related published arguments:
--     - Rutten, J.J.M.M. (2000). "Universal coalgebra: a theory of
--       systems." Theoretical Computer Science 249. — final-coalgebra
--       uniqueness gives the dual to initial-algebra induction.
--     - Aczel-Mendler bisimulation provides the equational backbone.
--     - Pitts/Stark coinductive techniques for observational
--       equivalence.
--
--   The specific package "ana-form productive transformation correct
--   on its own state ⟹ correct on all seeds" used here is, to our
--   knowledge, not stated cleanly in any single published source. It
--   is the coinductive dual of the bootstrap-doc Theorem 4.1, derived
--   by analogy. We treat it as Established to mark a clean handoff
--   point — concrete syntaxes discharge it by coinduction on the
--   productive structure of the co-encoding.
--
--   PROVENANCE NOTE: Cotransparency rests on thinner literature than
--   Transparency. The transparency intuition (NF behavior is uniform
--   in matched components) is centuries-old folklore in syntactic
--   reasoning; the dual (productive head behavior is uniform in
--   bisimilar seeds) is younger and more contested. Consumers should
--   be aware that this postulate carries somewhat more risk than its
--   μ-side counterpart.
--
-- TOWER LEVEL: CCT4 (ν-types are needed even to state the property).
--
-- THEOREM (Cotransparency / Productive Uniformity from Single-Point
--          CoFixpoint):
--   Let T : CoCode → CoCode be productive, and let cospec be an
--   intended semantics. If
--     T ∘ ⌜T⌝ω  ≈ω  ⌜cospec T⌝ω
--   (i.e., T satisfies its cospec on its own co-encoding up to
--   bisimilarity), then for every morphism g
--     T ∘ ⌜g⌝ω  ≈ω  ⌜cospec g⌝ω.
--
-- PARAMETERIZATION:
--   - S    : a CCT4 structure
--   - CoR  : a Coreducible carrier on S
--   - E    : a CoEncodingScheme for S
--   - CoEI : a CoEncodingInductive (provides ⊑ω and structural laws)
--
-- USE SITE:
--   This postulate is consumed by Theory.RanzowFixpoint.CoFullCorrectness
--   to upgrade the cofixpoint property "T ∘ ⌜T⌝ω ≈ω ⌜T⌝ω" to per-seed
--   correctness "∀g. T ∘ ⌜g⌝ω ≈ω ⌜cospec g⌝ω".
--
-- SCOPE OF THIS POSTULATE:
--   This module postulates ONLY the productive-uniformity property
--   for productive morphisms of type CoCode → CoCode under the given
--   co-encoding. It does NOT claim anything about non-productive
--   morphisms or behavior at non-CoCode types.
------------------------------------------------------------------------

module Theory.Established.Cotransparency where

open import Theory.CCTower using (TowerLevel; CCT4)
open import Theory.Systems.CCT4
open import Theory.Syntax.Coreducible using (Coreducible)
open import Theory.RanzowFixpoint.Coinductive using (CoEncodingScheme)
open import Theory.Encoding.Coinductive using (CoEncodingInductive)

------------------------------------------------------------------------
-- Tower level annotation
------------------------------------------------------------------------

applies-to : TowerLevel
applies-to = CCT4

------------------------------------------------------------------------
-- The Theorem, parameterized over a CCT4 structure equipped with a
-- bisimilarity carrier, a co-encoding scheme, and the structural
-- co-encoding laws.
------------------------------------------------------------------------

module _ (S    : CCT4Structure)
         (CoR  : Coreducible (CCT4Structure.Obj S) (CCT4Structure.Hom S))
         (E    : CoEncodingScheme S)
         (CoEI : CoEncodingInductive S CoR E)
         where
  open CCT4Structure S
  open Coreducible CoR
  open CoEncodingScheme E
  open CoEncodingInductive CoEI

  postulate
    --------------------------------------------------------------------
    -- productive-cofixpoint-implies-correctness:
    --   A productive transformation T : CoCode → CoCode that
    --   satisfies its cospec at its own co-encoding (up to ≈ω)
    --   satisfies the cospec at every co-encoded input.
    --
    -- This is the coinductive dual of
    -- Transparency.nf-fixpoint-implies-correctness.
    --
    -- For the canonical productive-corecursor case:
    --   - cospec g is the (unique up to bisim) productive output of g.
    --   - T being productive gives cospec T ≈ T (productive morphisms
    --     are fixed points of the "evaluate to productive form"
    --     function up to bisim).
    --   - The hypothesis becomes the coinductive Ranzow Fixpoint
    --     property "T ∘ ⌜T⌝ω ≈ω ⌜T⌝ω".
    --   - The conclusion becomes correctness of T as a corecursor.
    --------------------------------------------------------------------

    productive-cofixpoint-implies-correctness :
      ∀ (cospec : ∀ {A B} → Hom A B → Hom A B)
        (T : Hom CoCode CoCode) →
        IsProductive T →
        -- Hypothesis: T satisfies the cospec on its own co-encoding
        (T ∘ co-encode T) ≈ω co-encode (cospec T) →
        -- Conclusion: T satisfies the cospec on every co-encoded input
        (∀ {A B} (g : Hom A B) →
           (T ∘ co-encode g) ≈ω co-encode (cospec g))
