------------------------------------------------------------------------
-- normalizer.Theory.Eval.Instance
--
-- A concrete Evaluable carrier for the normalizer syntax, built on the
-- existing denotational evaluator (Testing.Evaluator.eval).
--
-- This discharges — FOR FREE — the two hypotheses that the abstract
-- evaluator-form Ranzow correctness (Theory.RanzowFixpoint.EvalCorrectness)
-- requires:
--
--   determinism : a term evaluates to at most one value
--   totality    : a term evaluates to at least one value
--
-- Both are immediate because `eval` is a total, deterministic Agda
-- function. No confluence obligation (cf. NonConfluenceWitness) and no
-- strong-normalization obligation (cf. WeakNormalizationFails) — the two
-- false postulates the rewriting developments rest on are simply not
-- needed here. This is the concrete payoff of the evaluator route.
--
-- Step 4 of plans/evaluator-instance.md, architecture option (A): the
-- instance lives in the bootstrap lib, where the model already exists.
------------------------------------------------------------------------

module normalizer.Theory.Eval.Instance where

open import normalizer.Syntax.Types
open import normalizer.Syntax.CCC using (Term)
open import normalizer.Testing.Evaluator using (⟦_⟧T; eval)

------------------------------------------------------------------------
-- The Evaluable carrier (bootstrap-local mirror of
-- Theory.Syntax.Evaluable, against the bootstrap prelude).
------------------------------------------------------------------------

record Evaluable : Set₁ where
  field
    Value : Ty → Ty → Set
    _⇓_   : ∀ {A B} → Term A B → Value A B → Set
  infix 4 _⇓_

------------------------------------------------------------------------
-- The denotational instance: a value is a model function, and a term
-- "evaluates to" the function it denotes.
------------------------------------------------------------------------

Denotational : Evaluable
Denotational = record
  { Value = λ A B → ⟦ A ⟧T → ⟦ B ⟧T
  ; _⇓_   = λ t v → eval t ≡ v
  }

open Evaluable Denotational public

------------------------------------------------------------------------
-- determinism — free: eval is a function.
------------------------------------------------------------------------

determinism : ∀ {A B} {t : Term A B} {v w : Value A B} →
              t ⇓ v → t ⇓ w → v ≡ w
determinism p q = trans (sym p) q

------------------------------------------------------------------------
-- totality — free: eval is total.
------------------------------------------------------------------------

totality : ∀ {A B} (t : Term A B) → ∃[ v ] (t ⇓ v)
totality t = eval t , refl
