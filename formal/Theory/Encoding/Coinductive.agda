------------------------------------------------------------------------
-- Theory.Encoding.Coinductive
--
-- A strengthening of CoEncodingScheme with the structural properties
-- a co-encoding must satisfy for the coinductive Ranzow Fixpoint ⟹
-- correctness chain to go through.
--
-- Coinductive sibling of Theory.Encoding.Inductive.
--
-- A CoEncodingScheme alone (Theory.RanzowFixpoint.Coinductive) only
-- provides:
--   - a CoCode object
--   - co-encode : Hom A B → Hom Unit CoCode
-- with no structural laws. That is enough to STATE the cofixpoint
-- property but not enough to prove "cofixpoint ⟹ correctness on all
-- inputs".
--
-- This record adds three syntactic obligations dual to the μ-side:
--
--   1. co-encode-is-productive   (dual of encode-is-nf)
--      Co-encodings are productive — their head structure is always
--      observable.
--
--   2. co-encode-faithful        (dual of encode-faithful)
--      Bisimilar co-encodings come from equivalent (≈) morphisms.
--
--   3. co-encode-ana-decomposes  (dual of encode-cata-decomposes)
--      The co-encoding of an anamorphism ana(F, coalg) exposes the
--      co-encoding of coalg as a sub-encoding.
--
-- These properties are DEFINITIONAL — they describe the co-encoding,
-- not the bisimilarity. They are discharged at instantiation by
-- inspection of the concrete co-encoding scheme.
--
-- TOWER LEVEL: CCT4.
------------------------------------------------------------------------

module Theory.Encoding.Coinductive where

open import Theory.CCTower using (TowerLevel; CCT4)
open import Theory.Systems.CCT4
open import Theory.Syntax.Coreducible using (Coreducible)
open import Theory.RanzowFixpoint.Coinductive using (CoEncodingScheme)

------------------------------------------------------------------------
-- Tower level annotation
------------------------------------------------------------------------

applies-to : TowerLevel
applies-to = CCT4

------------------------------------------------------------------------
-- The Coinductive Encoding Record
--
-- Parameterized over:
--   S    : a CCT4 structure (gives ν-types so CoCode = ν TermF is
--          meaningful)
--   CoR  : a bisimilarity carrier (gives _≈ω_ and IsProductive)
--   E    : the underlying CoEncodingScheme being strengthened
------------------------------------------------------------------------

record CoEncodingInductive
         (S    : CCT4Structure)
         (CoR  : Coreducible (CCT4Structure.Obj S) (CCT4Structure.Hom S))
         (E    : CoEncodingScheme S) : Set₁ where
  open CCT4Structure S
  open Coreducible CoR
  open CoEncodingScheme E

  field
    --------------------------------------------------------------------
    -- Sub-coencoding relation.
    --
    -- ⌜g⌝ω ⊑ω ⌜h⌝ω means: the co-encoded morphism ⌜g⌝ω appears as a
    -- sub-component of ⌜h⌝ω, in the productive-coinductive sense
    -- (e.g., reachable from the head by a finite number of νOut
    -- unfoldings).
    --------------------------------------------------------------------

    _⊑ω_ : Hom Unit CoCode → Hom Unit CoCode → Set

    --------------------------------------------------------------------
    -- (1) Co-encodings are productive.
    --
    -- Dual to encode-is-nf: where μ-encodings are NFs (no further
    -- reduction applies), ν-encodings are productive (head structure
    -- is always reachable).
    --------------------------------------------------------------------

    co-encode-is-productive :
      ∀ {A B} (g : Hom A B) → IsProductive (co-encode g)

    --------------------------------------------------------------------
    -- (2) Co-encoding is faithful.
    --
    -- Bisimilarity of co-encodings reflects equality (up to ≈) of the
    -- underlying morphisms. This is the right notion of "injectivity"
    -- for ν-data, since propositional equality on ν-data is finer
    -- than the operational equivalence we care about.
    --------------------------------------------------------------------

    co-encode-faithful :
      ∀ {A B} {g h : Hom A B} → co-encode g ≈ω co-encode h → g ≈ h

    --------------------------------------------------------------------
    -- (3) Anamorphism co-encodings decompose.
    --
    -- Dual to encode-cata-decomposes: the co-encoding of ana(F, coalg)
    -- exposes ⌜coalg⌝ω as a sub-co-encoding. For a corecursive T
    -- defined as ana(coalg), this means ⌜T⌝ω contains ⌜coalg⌝ω, so
    -- the cofixpoint property exercises every productive step of T.
    --------------------------------------------------------------------

    co-encode-ana-decomposes :
      ∀ {F : Obj → Obj} {A} (coalg : Hom A (F A)) →
      co-encode coalg ⊑ω co-encode (ana {F} coalg)
