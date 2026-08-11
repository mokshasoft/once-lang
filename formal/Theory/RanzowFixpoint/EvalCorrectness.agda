------------------------------------------------------------------------
-- Theory.RanzowFixpoint.EvalCorrectness
--
-- The evaluator-form of the Ranzow Fixpoint correctness fragment — the
-- dual of Theory.RanzowFixpoint.Correctness.
--
-- As in the rewriting version, every theorem takes the required facts as
-- explicit hypotheses; a
-- concrete inspectable CCC-VM discharges them from the evaluator's
-- functional/total character.
--
-- TOWER LEVEL: CCT3.
--
-- DUALITY WITH THE REWRITING VERSION
--
--   rewriting (Correctness)        evaluator (this module)
--   ----------------------------   ----------------------------------
--   _⟶_, _⟶*_, IsNormalForm        _⇓_ (eval to value)
--   nf-stable + confluence         determinism
--   (unique normal forms)          (unique values)
--   strong normalization           totality
--   T ∘ ⌜T⌝ ⟶* ⌜T⌝                 eval(T ∘ ⌜T⌝) ≡ eval(⌜T⌝)
--   fixpoint-is-canonical          eval-fixpoint-is-canonical
--   fixpoint-is-unique             eval-fixpoint-is-unique
--
-- The point of the reformulation: in the rewriting version `nf-unique`
-- needs BOTH confluence and nf-stable; here the same canonicity result
-- needs only `determinism`. `totality` is what makes the fixpoint check
-- runnable on every input (a defined canonical value always exists) — it
-- is supplied by Once's structured recursion, not assumed about an
-- arbitrary rewrite system. No confluence obligation appears, so the
-- non-confluence of full βη (NonConfluenceWitness) is irrelevant here.
--
-- Like the rewriting version, this is the HONEST canonicity/uniqueness
-- fragment. The full jump from "fixpoint on ⌜T⌝" to "correct on all
-- inputs" still additionally requires transparency and encoding-
-- completeness, which are not formalised here.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Theory.RanzowFixpoint.EvalCorrectness where

open import Theory.CCTower using (TowerLevel; CCT3)
open import Theory.Syntax.Evaluable using (Evaluable)
open import Theory.RanzowFixpoint.SelfEncoding using (SelfEncoding)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans)
open import Data.Product
  using (Σ; _,_; proj₁; proj₂) renaming (_×_ to _∧_)

------------------------------------------------------------------------
-- Tower level annotation
------------------------------------------------------------------------

applies-to : TowerLevel
applies-to = CCT3

------------------------------------------------------------------------
-- The evaluator-form correctness fragment
--
-- Parameterized over exactly what the proof uses (Theory.RanzowFixpoint.
-- SelfEncoding):
--   - SE : a self-encoding carrier (Obj/Hom/∘/Unit/Code/encode)
--   - Ev : an Evaluable carrier on it (big-step evaluation)
------------------------------------------------------------------------

module Fixpoint (SE : SelfEncoding)
                (Ev : Evaluable (SelfEncoding.Obj SE) (SelfEncoding.Hom SE)) where
  open SelfEncoding SE
  open Evaluable Ev

  ----------------------------------------------------------------------
  -- The Ranzow Fixpoint property, evaluator form.
  --
  -- T applied to its own encoding evaluates to the SAME value as the
  -- encoding itself: eval(T ∘ ⌜T⌝) and eval(⌜T⌝) agree. This is the
  -- value-equality check of the inspectable CCC-VM.
  ----------------------------------------------------------------------

  HasEvalRanzowFixpoint : Hom Code Code → Set
  HasEvalRanzowFixpoint T =
    Σ (Value Unit Code) (λ v → ((T ∘ encode T) ⇓ v) ∧ (encode T ⇓ v))

  module Canonical
    ------------------------------------------------------------------
    -- HYPOTHESIS (determinism):
    --   A term evaluates to at most one value. Free for a functional
    --   evaluator; it is what replaces confluence + nf-stable.
    ------------------------------------------------------------------
    (determinism :
      ∀ {A B} {t : Hom A B} {v w} → t ⇓ v → t ⇓ w → v ≡ w)

    ------------------------------------------------------------------
    -- HYPOTHESIS (totality):
    --   A term evaluates to at least one value. Supplied by Once's
    --   structured recursion; it is what makes the fixpoint check
    --   runnable on every input.
    ------------------------------------------------------------------
    (totality :
      ∀ {A B} (t : Hom A B) → Σ (Value A B) (λ v → t ⇓ v))

    where

    --------------------------------------------------------------------
    -- The canonical value of a term: it exists (totality) and is unique
    -- (determinism). This is the evaluator-form analogue of "unique
    -- normal forms" — a defined canonical form for every input.
    --------------------------------------------------------------------

    canonical-value :
      ∀ {A B} (t : Hom A B) →
      Σ (Value A B) (λ v → (t ⇓ v) ∧ (∀ {w} → t ⇓ w → w ≡ v))
    canonical-value t with totality t
    ... | (v , t⇓v) = v , t⇓v , (λ t⇓w → determinism t⇓w t⇓v)

    --------------------------------------------------------------------
    -- Main theorem: the Ranzow Fixpoint value is canonical.
    --
    -- Any observed value of (T ∘ ⌜T⌝) equals the value of ⌜T⌝.
    --------------------------------------------------------------------

    eval-fixpoint-is-canonical :
      ∀ (T : Hom Code Code) →
      HasEvalRanzowFixpoint T →
      ∀ {u} → (T ∘ encode T) ⇓ u →
      Σ (Value Unit Code) (λ w → (encode T ⇓ w) ∧ (u ≡ w))
    eval-fixpoint-is-canonical T (v , fix-lhs , fix-rhs) lhs⇓u =
      v , fix-rhs , determinism lhs⇓u fix-lhs

    --------------------------------------------------------------------
    -- Corollary: the Ranzow Fixpoint value is unique (pure determinism).
    --------------------------------------------------------------------

    eval-fixpoint-is-unique :
      ∀ (T : Hom Code Code) →
      ∀ {u w} → (T ∘ encode T) ⇓ u → (T ∘ encode T) ⇓ w →
      u ≡ w
    eval-fixpoint-is-unique T lhs⇓u lhs⇓w = determinism lhs⇓u lhs⇓w
