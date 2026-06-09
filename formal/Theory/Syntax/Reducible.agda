------------------------------------------------------------------------
-- Theory.Syntax.Reducible
--
-- A directed reduction relation on a categorical carrier (Obj, Hom).
--
-- Rationale:
--   The Systems.CCT* records are purely equational — they specify the
--   CCC laws that any concrete presentation must satisfy, and are
--   silent about HOW those laws are realized operationally.
--
--   But most computational content about a CCC (strong normalization,
--   confluence, normal forms, the Ranzow Fixpoint property itself) is
--   phrased in terms of DIRECTED REWRITING. A specific Syntax provides
--   that reduction; different Syntaxes may orient the laws differently
--   and so have different reduction properties.
--
--   This record packages a reduction relation (and its reflexive-
--   transitive closure, plus the predicate "no reduction applies") as
--   a separate layer. Downstream modules that reason about directed
--   rewriting take a `Reducible Obj Hom` in addition to whatever
--   Systems record they use.
--
-- A Syntax discharges this by giving its own reduction relation and
-- NF predicate, and it discharges the Systems record by proving the
-- laws — typically by showing reductions imply the equational _≈_.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Theory.Syntax.Reducible where

------------------------------------------------------------------------
-- Reducible carrier
--
-- Parameterized only over the categorical carrier — not over any
-- particular Systems level. This lets the same record serve CCTB,
-- CCT1, CCT2, CCT3, CCT4 without duplication: the rules in _⟶_
-- simply include whichever level's constructors are relevant.
------------------------------------------------------------------------

record Reducible (Obj : Set) (Hom : Obj → Obj → Set) : Set₁ where
  field
    _⟶_          : ∀ {A B} → Hom A B → Hom A B → Set
    _⟶*_         : ∀ {A B} → Hom A B → Hom A B → Set
    IsNormalForm : ∀ {A B} → Hom A B → Set
