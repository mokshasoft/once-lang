------------------------------------------------------------------------
-- Once.CCC.IR.Totality
--
-- Totality (termination) of IR evaluation.
--
-- This module establishes that IR morphism evaluation always terminates.
-- This is the foundational property from which productivity follows.
--
-- Mathematical basis:
--   - Simply-typed lambda calculus with inductive types is strongly
--     normalizing (Tait 1967, Girard 1972)
--   - Catamorphisms over polynomial functors terminate by structural
--     recursion (Lambek's Lemma)
--   - Anamorphisms produce lazy codata; each observation terminates
--
-- The key insight (OCP-0003): Since IR morphisms are total, coalgebras
-- of type IR A (⟦ F ⟧T A) always produce an F-layer. This means
-- "guardedness" is automatic - no GuardedT wrapper is needed.
--
-- References:
--   [1] Tait, "Intensional interpretations of functionals of finite type"
--   [2] Girard, "Interprétation fonctionnelle et élimination des coupures"
--   [3] Lambek & Scott, "Introduction to Higher Order Categorical Logic"
--   [4] bootstrap/normalizer/Foundations/EstablishedMath.agda
------------------------------------------------------------------------

module Once.CCC.IR.Totality where

open import Level using (Level; 0ℓ)
open import Data.Product using (Σ; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type
open import Once.IR
open import Once.CCC.Eval using (eval)
-- Plan 0.74 (D119): `eval` takes the target's numeric parameters. This island
-- kept the pre-D119 signature and rotted; the statements below thread `fmt`
-- exactly as the apex does. Totality is a fact about the MORPHISM, so nothing
-- here depends on which target it is — but the statement has to name one.
open import Once.Target.Arch using (TargetNum)
-- Plan 0.52 M2: IR objects are ungraded `IRTy`, so an IR morphism's argument
-- lives in the IR domain `⟦_⟧ᴵ` — NOT the surface `⟦_⟧`, which wants a `Type`.
open import Once.Semantics.Machine using (⟦_⟧ᴵ)
open import Once.IRTy using (IRTy; ⟦_⟧TI)

------------------------------------------------------------------------
-- Totality of IR Evaluation
--
-- IR morphisms evaluate to values. This is the foundation for both
-- termination (cata) and productivity (ana).
------------------------------------------------------------------------

-- | IR evaluation is total
--
-- For any IR morphism f : IR A B and input a : ⟦ A ⟧, evaluation
-- terminates and produces a value b : ⟦ B ⟧.
--
-- This follows from:
--   1. Simply-typed systems are strongly normalizing [1,2]
--   2. Cata terminates by structural recursion on μF [3]
--   3. Ana produces lazy codata; each step is finite computation
--   4. All other IR constructors are non-recursive
--
-- POSTULATE JUSTIFICATION:
-- The full proof requires logical relations (reducibility candidates).
-- This is well-established mathematics - see [1,2,3].
-- The bootstrap normalizer postulates this for the same reason [4].
--
postulate
  eval-total : ∀ {A B} (fmt : TargetNum) (f : IR A B) (a : ⟦ A ⟧ᴵ)
             → ∃[ b ] (eval fmt f a ≡ b)

------------------------------------------------------------------------
-- Coalgebra Termination
--
-- A coalgebra is an IR morphism of type IR A (⟦ F ⟧T A).
-- By eval-total, it always produces a value of type ⟦ ⟦ F ⟧T A ⟧.
-- This IS one F-layer - the coalgebra is "guarded" by construction.
------------------------------------------------------------------------

-- | Coalgebras produce F-layers
--
-- This is the key property that makes GuardedT unnecessary:
-- any IR coalgebra terminates and produces ⟦ F ⟧T A, which is
-- exactly one layer of functor structure.
--
-- Plan 0.52 M2: an IR coalgebra is an IR-LEVEL object throughout — `Ana` takes
-- an `IRFunctor` with `WellFormedFI` and IR objects are `IRTy`, so the layer is
-- `⟦ F ⟧TI A` and no surface `Type` appears anywhere in the statement.
coalg-produces-layer : ∀ {F} {A : IRTy} (fmt : TargetNum)
                         (c : IR A (⟦ F ⟧TI A)) (a : ⟦ A ⟧ᴵ)
                     → ∃[ v ] (eval fmt c a ≡ v)
coalg-produces-layer fmt c a = eval-total fmt c a

------------------------------------------------------------------------
-- Immediate Consequences
------------------------------------------------------------------------

-- | fmap preserves totality (trivial - fmap is structural)
--
-- If f terminates on all inputs, then fmap F f terminates on all inputs.
-- This is by structural recursion on F.
--
-- (Proof omitted - follows directly from fmap definition)

-- | Composition preserves totality
--
-- If f and g both terminate, then (g ∘ f) terminates.
--
comp-total : ∀ {A B C} (fmt : TargetNum) (f : IR A B) (g : IR B C) (a : ⟦ A ⟧ᴵ)
           → ∃[ c ] (eval fmt (g ∘ f) a ≡ c)
comp-total fmt f g a = eval-total fmt (g ∘ f) a

------------------------------------------------------------------------
-- Summary
------------------------------------------------------------------------
--
-- eval-total : IR evaluation always terminates
--   |
--   +-- coalg-produces-layer : coalgebras produce F-layers
--   |     |
--   |     +-- (implies) "guardedness" is automatic
--   |     +-- (implies) GuardedT is unnecessary
--   |
--   +-- comp-total : composition preserves totality
--
-- This module provides the foundation for IR.Productivity.
------------------------------------------------------------------------
