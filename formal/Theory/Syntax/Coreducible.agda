------------------------------------------------------------------------
-- Theory.Syntax.Coreducible
--
-- A bisimilarity / productivity carrier on a categorical Hom-type.
-- Coinductive sibling of Theory.Syntax.Reducible.
--
-- Rationale:
--   The directed reduction of Reducible is the natural carrier for
--   reasoning about TERMINATING normalization (cata-form transforms,
--   strong normalization, NFs). The dual situation — productive
--   corecursive transformations on ν-types — is captured operationally
--   by BISIMILARITY (`_≈ω_`) plus a productivity predicate
--   (`IsProductive`) rather than by reduction-to-NF.
--
--   This record is used in tandem with Reducible at CCT4: a concrete
--   syntax provides BOTH (its directed _⟶_/IsNormalForm for finite
--   syntactic data and its _≈ω_/IsProductive for ν-typed
--   computations).
--
-- Notion-of-bisimilarity left abstract:
--   We do not commit to strong, weak, or observational bisimilarity —
--   each concrete Coreducible instance picks one. The Cotransparency
--   postulate downstream consumes _≈ω_ uniformly.
------------------------------------------------------------------------

module Theory.Syntax.Coreducible where

------------------------------------------------------------------------
-- Coreducible carrier
--
-- Like Reducible, parameterized only over the categorical carrier.
-- Concrete instances at CCT4 supply both a Reducible (for the μ-side
-- reduction) and a Coreducible (for the ν-side bisimilarity), sharing
-- the same Obj and Hom.
------------------------------------------------------------------------

record Coreducible (Obj : Set) (Hom : Obj → Obj → Set) : Set₁ where
  field
    -- Bisimilarity on morphisms. Left abstract; concrete instances
    -- choose strong, weak, or observational bisimulation.
    _≈ω_ : ∀ {A B} → Hom A B → Hom A B → Set

    -- Productivity: a morphism is productive when its application to
    -- any input reveals head structure within a finite number of
    -- reduction steps. Analog of IsNormalForm for the ν-side.
    IsProductive : ∀ {A B} → Hom A B → Set
