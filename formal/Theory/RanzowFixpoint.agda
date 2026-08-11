------------------------------------------------------------------------
-- Theory.RanzowFixpoint
--
-- The Ranzow Fixpoint: Self-Verification via Fixpoint Property.
--
--   A transformation T has the Ranzow Fixpoint property if applying T
--   to its own encoding reduces back to that encoding:
--
--     T ∘ ⌜T⌝  ⟶*  ⌜T⌝
--
-- This file contains DEFINITIONS ONLY.
-- The definitions are parameterized over a CCT3 structure (the minimum
-- level that supports self-encoding via μ-types), a directed reduction
-- on that structure, and an encoding scheme.
--
-- Theorems about the Ranzow Fixpoint (e.g., fixpoint-is-canonical)
-- live in Theory.RanzowFixpoint.Correctness and take Established math
-- hypotheses as explicit arguments.
--
-- TOWER LEVEL: CCT3 (BCC + μ-types).
-- Self-encoding requires μ-types; RF is not meaningful below CCT3.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Theory.RanzowFixpoint where

open import Theory.CCTower using (TowerLevel; CCT3)
open import Theory.Systems.CCT3
open import Theory.Syntax.Reducible using (Reducible)

------------------------------------------------------------------------
-- Tower level annotation
------------------------------------------------------------------------

applies-to : TowerLevel
applies-to = CCT3

------------------------------------------------------------------------
-- Encoding Scheme
--
-- An encoding scheme for a CCT3 structure S is:
--   - a distinguished Code object (typically Code ≡ μ TermF for some
--     functor TermF that represents the term syntax)
--   - an encoding function mapping any morphism of S to a closed
--     morphism Unit → Code representing its syntactic structure.
------------------------------------------------------------------------

record EncodingScheme (S : CCT3Structure) : Set₁ where
  open CCT3Structure S
  field
    Code   : Obj
    encode : ∀ {A B} → Hom A B → Hom Unit Code

------------------------------------------------------------------------
-- The Ranzow Fixpoint property.
--
-- Stated in terms of directed reduction: we require an explicit
-- Reducible carrier on the CCT3 structure.
------------------------------------------------------------------------

module _ (S : CCT3Structure)
         (Red : Reducible (CCT3Structure.Obj S) (CCT3Structure.Hom S))
         (E : EncodingScheme S) where
  open CCT3Structure S
  open Reducible Red
  open EncodingScheme E

  -- A transformation T : Code → Code has the Ranzow Fixpoint property
  -- when its composition with its own encoding reduces back to that
  -- encoding.
  HasRanzowFixpoint : Hom Code Code → Set
  HasRanzowFixpoint T = (T ∘ encode T) ⟶* encode T

  -- Alias used in the literature ("self-verifying transformation").
  SelfVerifying : Hom Code Code → Set
  SelfVerifying = HasRanzowFixpoint
