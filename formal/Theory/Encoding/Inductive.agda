------------------------------------------------------------------------
-- Theory.Encoding.Inductive
--
-- A strengthening of EncodingScheme with the structural properties an
-- encoding must satisfy for the Ranzow Fixpoint ⟹ correctness chain
-- to go through.
--
-- An EncodingScheme alone (Theory.RanzowFixpoint) only provides:
--   - a Code object
--   - encode : Hom A B → Hom Unit Code
-- with no structural laws. That is enough to STATE the fixpoint
-- property but not enough to prove "fixpoint ⟹ correctness on all
-- inputs" (only the uniqueness fragment).
--
-- This record adds the three syntactic obligations identified in
-- bootstrap/theory/fixpoint-correctness.md:
--
--   1. encode-is-nf            (Lemma 3.1)
--      Encodings are normal forms — they are stable under reduction.
--
--   2. encode-faithful         (Lemma 3.2)
--      The encoding is injective (up to ≈) — distinct morphisms have
--      distinct encodings.
--
--   3. encode-cata-decomposes  (Lemma A.4)
--      The encoding of a catamorphism cata(F, step) exposes the
--      encoding of step as a sub-encoding. This is what makes the
--      fixpoint property ACTUALLY EXERCISE every branch of step.
--
-- These properties are DEFINITIONAL — they describe the encoding, not
-- the reduction. They are discharged at instantiation by inspection of
-- the concrete encoding scheme.
--
-- TOWER LEVEL: CCT3.
------------------------------------------------------------------------

module Theory.Encoding.Inductive where

open import Theory.CCTower using (TowerLevel; CCT3)
open import Theory.Systems.CCT3
open import Theory.Syntax.Reducible using (Reducible)
open import Theory.RanzowFixpoint using (EncodingScheme)
open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------
-- Tower level annotation
------------------------------------------------------------------------

applies-to : TowerLevel
applies-to = CCT3

------------------------------------------------------------------------
-- The Inductive Encoding Record
--
-- Parameterized over:
--   S   : a CCT3 structure (gives μ-types so Code = μ TermF is meaningful)
--   Red : a directed reduction (gives IsNormalForm)
--   E   : the underlying EncodingScheme being strengthened
------------------------------------------------------------------------

record EncodingInductive
         (S   : CCT3Structure)
         (Red : Reducible (CCT3Structure.Obj S) (CCT3Structure.Hom S))
         (E   : EncodingScheme S) : Set₁ where
  open CCT3Structure S
  open Reducible Red
  open EncodingScheme E

  field
    --------------------------------------------------------------------
    -- Sub-encoding relation.
    --
    -- ⌜g⌝ ⊑ ⌜h⌝ means: the encoded morphism ⌜g⌝ appears positionally
    -- inside ⌜h⌝ as a syntactic sub-encoding.
    --
    -- Concrete syntaxes define this in terms of subterm-occurrence in
    -- the underlying Term datatype, then lift it through the encoding.
    --------------------------------------------------------------------

    _⊑_ : Hom Unit Code → Hom Unit Code → Set

    --------------------------------------------------------------------
    -- (1) Encodings are normal forms.
    --
    -- Lemma 3.1 of bootstrap/theory/fixpoint-correctness.md:
    --   For all morphisms g, the encoding ⌜g⌝ is in normal form.
    --
    -- Justification at instantiation: every encoding has the form
    --   In ∘ inj_i ∘ ⟨⌜t₁⌝, …, ⌜tₙ⌝⟩
    -- and the head constructor In is none of {id, fst, snd, [_,_],
    -- apply, cata}, so no redex pattern applies at the root; subterms
    -- are NF by induction.
    --------------------------------------------------------------------

    encode-is-nf :
      ∀ {A B} (g : Hom A B) → IsNormalForm (encode g)

    --------------------------------------------------------------------
    -- (2) Encoding is faithful (injective up to ≈).
    --
    -- Lemma 3.2 of bootstrap/theory/fixpoint-correctness.md:
    --   If ⌜g⌝ ≡ ⌜h⌝, then g ≈ h.
    --
    -- Justification at instantiation: each constructor maps to a
    -- distinct sum-injection tag; subterms recover by induction.
    --
    -- We use propositional equality of encodings (since encodings live
    -- in Hom Unit Code and concrete syntaxes typically realize this as
    -- propositional equality of Term values) and the equational ≈ of S
    -- on the recovered morphisms.
    --------------------------------------------------------------------

    encode-faithful :
      ∀ {A B} {g h : Hom A B} → encode g ≡ encode h → g ≈ h

    --------------------------------------------------------------------
    -- (3) Catamorphism encodings decompose.
    --
    -- Lemma A.4 of bootstrap/theory/fixpoint-correctness.md:
    --   The encoding of cata(F, step) contains ⌜step⌝ as a
    --   sub-encoding. Consequently, ⌜N⌝ for N = cata(F, step) exposes
    --   every case branch of step at a definite syntactic position.
    --
    -- This is the structural fact that makes the fixpoint property
    -- N ∘ ⌜N⌝ ⟶* ⌜N⌝ a meaningful TEST: reaching the fixpoint forces
    -- N to handle each subterm of ⌜N⌝ (and in particular, each branch
    -- of its own step) correctly.
    --------------------------------------------------------------------

    encode-cata-decomposes :
      ∀ {F : Obj → Obj} {A} (step : Hom (F A) A) →
      encode step ⊑ encode (cata {F} step)
