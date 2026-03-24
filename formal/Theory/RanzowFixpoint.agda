------------------------------------------------------------------------
-- Theory.RanzowFixpoint
--
-- The Ranzow Fixpoint: Self-Verification via Fixpoint Property
--
-- A semantics-preserving transformation T is correct if T(⌜T⌝) →* ⌜T⌝
--
-- This module is PARAMETERIZED by the reduction system, so it can be
-- instantiated at any tower level (CCT1, CCT2, CCT3, CCT4).
------------------------------------------------------------------------

module Theory.RanzowFixpoint where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)

------------------------------------------------------------------------
-- Parameterized Reduction System
--
-- The Ranzow Fixpoint can be stated for ANY system that provides:
--   1. Objects and morphisms
--   2. A reduction relation
--   3. Confluence
--   4. Normalization
--   5. An encoding function
------------------------------------------------------------------------

record ReductionSystem : Set₁ where
  field
    -- Objects and morphisms
    Obj : Set
    Hom : Obj → Obj → Set

    -- Distinguished object for encodings
    Code : Obj
    Unit : Obj

    -- Composition
    _∘_ : ∀ {A B C} → Hom B C → Hom A B → Hom A C

    -- Reduction relation
    _⟶_ : ∀ {A B} → Hom A B → Hom A B → Set
    _⟶*_ : ∀ {A B} → Hom A B → Hom A B → Set

    -- Normal form predicate
    IsNormalForm : ∀ {A B} → Hom A B → Set

------------------------------------------------------------------------
-- Required Properties (provided by tower level)
------------------------------------------------------------------------

record RFProperties (R : ReductionSystem) : Set₁ where
  open ReductionSystem R
  field
    -- Confluence: any two reduction paths can be joined
    confluence : ∀ {A B} {t u v : Hom A B} →
                 t ⟶* u → t ⟶* v →
                 Σ (Hom A B) (λ w → (u ⟶* w) × (v ⟶* w))

    -- Normalization: every term has a normal form
    normalization : ∀ {A B} (t : Hom A B) →
                    Σ (Hom A B) (λ nf → (t ⟶* nf) × IsNormalForm nf)

    -- Encoding function
    encode : ∀ {A B} → Hom A B → Hom Unit Code

------------------------------------------------------------------------
-- The Ranzow Fixpoint
--
-- DEFINITION: A transformation T has the Ranzow Fixpoint property
-- if applying T to its own encoding yields that encoding.
--
--   T(⌜T⌝) →* ⌜T⌝
--
-- Theorems about the Ranzow Fixpoint (e.g., that it implies
-- correctness) live in Theory.RanzowFixpoint.Correctness.
------------------------------------------------------------------------

module RF (R : ReductionSystem) (P : RFProperties R) where
  open ReductionSystem R
  open RFProperties P

  -- The Ranzow Fixpoint property for a transformation T : Code → Code
  -- (T must be an endomorphism on Code to apply to its own encoding)
  HasRanzowFixpoint : Hom Code Code → Set
  HasRanzowFixpoint T = (T ∘ encode T) ⟶* encode T

  -- A transformation is self-verifying if it has the Ranzow Fixpoint
  SelfVerifying : Hom Code Code → Set
  SelfVerifying = HasRanzowFixpoint

------------------------------------------------------------------------
-- Instantiation at Tower Levels
--
-- To use RF at a specific tower level, provide:
--   1. The reduction system for that level
--   2. The properties (confluence, normalization) from Established/
--
-- Example:
--   RF-CCT1 = RF cct1-system cct1-properties
--   RF-CCT3 = RF cct3-system cct3-properties
------------------------------------------------------------------------

-- Tower level marker (for documentation)
open import Theory.CCTower using (TowerLevel; CCT1; CCT2; CCT3; CCT4)

-- Each instantiation would provide:
--   cctN-system : ReductionSystem
--   cctN-properties : RFProperties cctN-system
-- From Established/StrongNormalization and the concrete syntax

------------------------------------------------------------------------
-- Summary
--
-- The Ranzow Fixpoint captures a key insight:
--
--   "A transformation is correct if it is a fixpoint on its own encoding"
--
-- This module DEFINES the property. It is parameterized so it can be
-- instantiated at any level of the tower:
--   - CCT1: CCC (simply-typed λ-calculus)
--   - CCT2: BCC (+ coproducts)
--   - CCT3: BCC + μ-types (+ inductive types)
--   - CCT4: BCCR (+ coinductive types)
--
-- Proofs about the Ranzow Fixpoint live in:
--   - Theory.RanzowFixpoint.Correctness (RF implies semantics preservation)
------------------------------------------------------------------------
