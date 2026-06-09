------------------------------------------------------------------------
-- Theory.Syntax.Evaluable
--
-- A big-step EVALUATION relation on a categorical carrier (Obj, Hom).
--
-- The evaluator-form dual of Theory.Syntax.Reducible. Where Reducible
-- packages directed *rewriting* (_⟶_, _⟶*_, IsNormalForm), this packages
-- *evaluation to canonical values* (_⇓_ : term → value).
--
-- Rationale:
--   For the bootstrap we normalise by EVALUATION, not by term rewriting
--   (see bootstrap/theory/normalizer-vs-compiler-path.md). An evaluator
--   computes a closed term to a canonical value; the Ranzow fixpoint
--   check then reduces to value equality. In this presentation the two
--   properties the correctness argument needs are
--
--     determinism : a term evaluates to at most one value
--     totality    : a term evaluates to at least one value
--
--   which TOGETHER play the role that (confluence + strong normalization)
--   play in the rewriting presentation — except determinism is free for a
--   functional evaluator, and totality is supplied by Once's structured
--   recursion (cata total, ana productive). Crucially, NO confluence
--   obligation arises: the full βη rewrite system is not confluent
--   (Theory.Syntax.StrongCCL.CCT1.NonConfluenceWitness), but a
--   deterministic evaluator sidesteps that entirely.
--
-- A concrete VM (the inspectable CCC-VM) discharges this record by giving
-- its value domain and its evaluation relation, and discharges
-- determinism/totality from the evaluator's functional/total character.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Theory.Syntax.Evaluable where

------------------------------------------------------------------------
-- Evaluable carrier
--
-- Parameterized only over the categorical carrier — not over any
-- particular Systems level — exactly like Reducible.
------------------------------------------------------------------------

record Evaluable (Obj : Set) (Hom : Obj → Obj → Set) : Set₁ where
  field
    -- Canonical values, indexed by the same (source, target) as Hom.
    Value : Obj → Obj → Set
    -- Big-step evaluation: `t ⇓ v` means term t evaluates to value v.
    _⇓_   : ∀ {A B} → Hom A B → Value A B → Set

  infix 4 _⇓_
