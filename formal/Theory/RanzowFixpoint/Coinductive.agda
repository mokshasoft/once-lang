------------------------------------------------------------------------
-- Theory.RanzowFixpoint.Coinductive
--
-- The coinductive Ranzow Fixpoint: Self-Verification via Bisimilarity.
--
--   A productive corecursive transformation T has the CoFixpoint
--   property if applying T to its own ν-encoding is bisimilar to that
--   encoding:
--
--     T ∘ ⌜T⌝ω  ≈ω  ⌜T⌝ω
--
-- This file contains DEFINITIONS ONLY.
-- The definitions are parameterized over a CCT4 structure (the minimum
-- level that supports ν-types and hence bisimilarity-based
-- self-encoding), a Coreducible carrier on that structure, and a
-- co-encoding scheme.
--
-- Theorems about the CoFixpoint live in
-- Theory.RanzowFixpoint.CoFullCorrectness and consume the
-- Theory.Established.Cotransparency postulate.
--
-- Coinductive sibling of Theory.RanzowFixpoint.
--
-- TOWER LEVEL: CCT4 (BCC + μ + ν).
-- Bisimilarity-based self-encoding requires ν-types; the CoFixpoint is
-- not meaningful below CCT4.
------------------------------------------------------------------------

module Theory.RanzowFixpoint.Coinductive where

open import Theory.CCTower using (TowerLevel; CCT4)
open import Theory.Systems.CCT4
open import Theory.Syntax.Coreducible using (Coreducible)

------------------------------------------------------------------------
-- Tower level annotation
------------------------------------------------------------------------

applies-to : TowerLevel
applies-to = CCT4

------------------------------------------------------------------------
-- CoEncoding Scheme
--
-- A co-encoding scheme for a CCT4 structure S is:
--   - a distinguished CoCode object (typically CoCode ≡ ν TermF for
--     some functor TermF that represents a coinductive view of the
--     term syntax — e.g., a stream of constructors, an observation
--     trace, or a productive trace of behaviors)
--   - a co-encoding function mapping any morphism of S to a closed
--     morphism Unit → CoCode representing its (potentially infinite)
--     coinductive structure.
--
-- Note: The morphisms of S are still finite combinator terms, but the
-- co-encoding may unfold infinitely (e.g., as a stream of behaviors
-- produced step-by-step). This is the analog of the μ-encoding for
-- corecursive self-representation.
------------------------------------------------------------------------

record CoEncodingScheme (S : CCT4Structure) : Set₁ where
  open CCT4Structure S
  field
    CoCode    : Obj
    co-encode : ∀ {A B} → Hom A B → Hom Unit CoCode

------------------------------------------------------------------------
-- The coinductive Ranzow Fixpoint property.
--
-- Stated in terms of bisimilarity: we require an explicit Coreducible
-- carrier on the CCT4 structure.
------------------------------------------------------------------------

module _ (S    : CCT4Structure)
         (CoR  : Coreducible (CCT4Structure.Obj S) (CCT4Structure.Hom S))
         (E    : CoEncodingScheme S) where
  open CCT4Structure S
  open Coreducible CoR
  open CoEncodingScheme E

  -- A transformation T : CoCode → CoCode has the coinductive Ranzow
  -- Fixpoint property when its composition with its own co-encoding
  -- is bisimilar to that co-encoding.
  HasCoFixpoint : Hom CoCode CoCode → Set
  HasCoFixpoint T = (T ∘ co-encode T) ≈ω co-encode T

  -- Alias used by analogy with the μ-side ("self-verifying productive
  -- transformation").
  CoSelfVerifying : Hom CoCode CoCode → Set
  CoSelfVerifying = HasCoFixpoint
