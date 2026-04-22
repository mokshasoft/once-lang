------------------------------------------------------------------------
-- Theory.RanzowFixpoint
--
-- The Ranzow Fixpoint: Self-Verification via Fixpoint Property.
--
--   A transformation T has the Ranzow Fixpoint property if applying T
--   to its own encoding yields that encoding:
--
--     T ∘ ⌜T⌝  ⟶*  ⌜T⌝
--
-- This file contains DEFINITIONS ONLY. Zero postulates, zero theorems.
-- The definitions are parameterized over a CCT3 structure (the minimum
-- level that supports self-encoding via μ-types) and an encoding scheme.
--
-- Theorems about the Ranzow Fixpoint (e.g., fixpoint-is-canonical)
-- live in Theory.RanzowFixpoint.Correctness and take Established math
-- hypotheses as explicit arguments.
--
-- TOWER LEVEL: CCT3 (BCC + μ-types).
-- Self-encoding requires μ-types; RF is not meaningful below CCT3.
-- Higher levels (CCT4) extend CCT3 and inherit the same definition.
------------------------------------------------------------------------

module Theory.RanzowFixpoint where

open import Theory.CCTower using (TowerLevel; CCT3)
open import Theory.Systems.CCT3

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
--
-- The encoding function is the key piece of "self-representation":
-- it lets T : Code → Code act on its own encoding ⌜T⌝ : Unit → Code.
--
-- Concrete encoding schemes (e.g., the bootstrap normalizer's encoding
-- for its specific CCC term algebra) instantiate this record.
------------------------------------------------------------------------

record EncodingScheme (S : CCT3Structure) : Set₁ where
  open CCT3Structure S
  field
    Code   : Obj
    encode : ∀ {A B} → Hom A B → Hom Unit Code

------------------------------------------------------------------------
-- The Ranzow Fixpoint property
------------------------------------------------------------------------

module _ (S : CCT3Structure) (E : EncodingScheme S) where
  open CCT3Structure S
  open EncodingScheme E

  -- A transformation T : Code → Code has the Ranzow Fixpoint property
  -- when its composition with its own encoding reduces back to that
  -- encoding.
  HasRanzowFixpoint : Hom Code Code → Set
  HasRanzowFixpoint T = (T ∘ encode T) ⟶* encode T

  -- Alias used in the literature ("self-verifying transformation").
  SelfVerifying : Hom Code Code → Set
  SelfVerifying = HasRanzowFixpoint
