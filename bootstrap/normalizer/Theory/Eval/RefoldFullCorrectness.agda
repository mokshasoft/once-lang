------------------------------------------------------------------------
-- normalizer.Theory.Eval.RefoldFullCorrectness
--
-- Capstone: the conclusion of the FULL "fixpoint ⟹ correct on all
-- inputs" theorem (Theory.RanzowFixpoint.EvalFullCorrectness), for the
-- refold normalizer with spec = identity, proved concretely.
--
-- The refold normalizer N = cata TermF In is denotationally the identity
-- (RefoldFixpoint.cata-In-id), so it computes spec = id on EVERY encoded
-- input:
--
--     ∀ g.  eval (N ∘ ⌜g⌝)  ≡  eval ⌜g⌝            (= ⌜id g⌝'s value)
--
-- This is exactly what `EvalFullCorrectness.Theorem.fixpoint-implies-
-- correctness` yields here: its decomposition is encoding-completeness
-- (trivial, BranchwiseCorrect = ⊤) followed by transparency, and for this
-- N transparency IS the cata-reflection law below — so the formal theorem
-- reduces definitionally to exactly `refold-correct-all`.
--
-- We prove the conclusion directly rather than instantiate the formal
-- module: with the function-based denotational model `_⇓_` compares
-- functions, so passing `determinism` into the module application trips
-- the same eval-eta unifier issue documented in Instance (canonicity).
-- The result and its type are identical to the formal theorem's output.
--
-- Degenerate (spec = id) but a real, postulate-free witness of
-- correct-on-all-inputs. No confluence, no SN.
--
-- Build: bootstrap/check.sh normalizer/Theory/Eval/RefoldFullCorrectness.agda
------------------------------------------------------------------------

module normalizer.Theory.Eval.RefoldFullCorrectness where

open import normalizer.Syntax.Types using (⊤; tt)
open import normalizer.Syntax.CCC using (Term; _∘_)
open import normalizer.Encoding.Encoding using (TermF; encode)
open import normalizer.Testing.Evaluator using (eval; normalizer)
open import normalizer.Theory.Eval.Instance using (mkVal; _⇓ᵈ_)
open import normalizer.Theory.Eval.RefoldFixpoint using (cata-In-id)

open import Relation.Binary.PropositionalEquality using (_≡_; cong)

-- Correct on ALL inputs, for spec = id: on every encoded input ⌜g⌝, the
-- refold normalizer evaluates to ⌜g⌝'s value. (`encVal (id g) = ⌜g⌝`'s
-- value `mkVal (eval (encode g))`.) The cata-reflection law lifted from
-- the value at `tt` via ⊤/fun eta (the `cong (λ z → λ _ → z)`); no funext.
refold-correct-all :
  ∀ {A B} (g : Term A B) →
  (normalizer ∘ encode g) ⇓ᵈ mkVal (eval (encode g))
refold-correct-all g =
  cong (λ z → λ (_ : ⊤) → z) (cata-In-id TermF (eval (encode g) tt))
