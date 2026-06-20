------------------------------------------------------------------------
-- Once.CCC.IR.Productivity
--
-- Productivity of anamorphisms (corecursion).
--
-- This module proves that Ana produces productive codata:
-- every observation (application of Out) terminates.
--
-- KEY INSIGHT (OCP-0003):
-- Productivity follows DIRECTLY from IR totality. No additional
-- postulates or proofs are needed beyond eval-total.
--
-- The reasoning:
--   1. An "observation" of (ana c a) is: eval (Out ∘ Ana c) a
--   2. (Out ∘ Ana c) is an IR morphism
--   3. By eval-total, evaluating any IR morphism terminates
--   4. Therefore, each observation terminates
--   5. Therefore, Ana is productive
--
-- This also means:
--   - "Guardedness" is automatic — coalgebras are IR morphisms, so they terminate
--   - GuardedT is unnecessary — any IR coalgebra is valid
--   - Productivity is a TRIVIAL COROLLARY of totality
------------------------------------------------------------------------

module Once.CCC.IR.Productivity where

open import Data.Product using (Σ; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (Type; Functor; ν-type; ⟦_⟧T)
open import Once.Functor.Translate using (WellFormedF)
open import Once.IR
open import Once.CCC.Eval using (⟦_⟧; eval)

-- Import totality foundation
open import Once.CCC.IR.Totality using (eval-total; coalg-produces-layer)

------------------------------------------------------------------------
-- Productivity: Each Observation Terminates
--
-- This is the ONLY theorem we need. Everything else follows.
------------------------------------------------------------------------

-- | One observation of codata terminates
--
-- Observing (ana c a) with Out is just evaluating an IR morphism.
-- By eval-total, this terminates.
--
-- This IS productivity: each observation produces a value in finite time.
--
observation-terminates : ∀ {F A} (wf : WellFormedF F) (c : IR A (⟦ F ⟧T A)) (a : ⟦ A ⟧)
                       → ∃[ v ] (eval (Out wf ∘ Ana wf c) a ≡ v)
observation-terminates wf c a = eval-total (Out wf ∘ Ana wf c) a

------------------------------------------------------------------------
-- Guardedness is Automatic
--
-- A coalgebra is an IR morphism. IR morphisms terminate.
-- Therefore coalgebras produce their output type (one F-layer).
-- This is exactly what "guarded" means.
------------------------------------------------------------------------

-- | Coalgebras produce F-layers (re-exported from Totality)
--
-- Any coalgebra c : IR A (⟦ F ⟧T A) terminates and produces ⟦ F ⟧T A.
-- This is "guardedness" — but it's automatic, not checked.
--
guardedness-automatic : ∀ {F A} (c : IR A (⟦ F ⟧T A)) (a : ⟦ A ⟧)
                      → ∃[ layer ] (eval c a ≡ layer)
guardedness-automatic {F} {A} c a = coalg-produces-layer {F} {A} c a

------------------------------------------------------------------------
-- Consequence: GuardedT is Unnecessary
--
-- The IR now uses:
--   Ana : WellFormedF F → IR A (⟦ F ⟧T A) → IR A (ν-type F)
--
-- Since any IR coalgebra IR A (⟦ F ⟧T A) is automatically "guarded"
-- (it terminates and produces an F-layer), no GuardedT wrapper is needed.
--
-- GuardedT, Guard, and Unguard have been removed from the IR.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Summary
------------------------------------------------------------------------
--
-- From eval-total (Totality.agda):
--
--   eval-total
--       |
--       +-- coalg-produces-layer (guardedness-automatic)
--       |     "Coalgebras terminate and produce F-layers"
--       |
--       +-- observation-terminates
--             "Each observation of Ana terminates"
--             = PRODUCTIVITY
--
-- That's it. Productivity is a trivial corollary of totality.
-- No syntactic guardedness checking. No GuardedT wrapper.
-- Just: IR morphisms terminate, therefore Ana is productive.
------------------------------------------------------------------------
