------------------------------------------------------------------------
-- Once.Functor.Translate
--
-- Translation from syntactic Functor (with Type) to semantic SFunctor (with Set).
--
-- This module provides the bridge between:
--   - Once.Type.Functor (K takes Type)
--   - Once.Functor.Base.SFunctor (K takes Set)
--
-- The translation uses a base type interpretation that handles only
-- base types (Unit, Int, etc.), avoiding dependency on ⟦μ⟧.
--
-- OCP-0003 Phase 6: Enables proving μ-coherence by defining ⟦μ⟧ = μS ∘ translate.
------------------------------------------------------------------------

module Once.Functor.Translate where

open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Float using () renaming (Float to AgdaFloat)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Once.Type
open import Once.Functor.Base

------------------------------------------------------------------------
-- Base Type Interpretation
--
-- Interprets base types without depending on ⟦μ⟧.
-- For non-base types (functions, μ-type, ν-type), returns ⊤.
--
-- This is sufficient because practical polynomial functors only use
-- base types in K positions.
------------------------------------------------------------------------

-- | Base type interpretation (parameterized by Int representation)
--
-- Returns ⊤ for complex types (functions, recursive types).
-- This is safe because K positions in practical functors use base types.
--
⟦_⟧-base : Set → Type → Set
⟦ IntRep ⟧-base Unit = ⊤
⟦ IntRep ⟧-base Void = ⊥
⟦ IntRep ⟧-base (A * B) = ⟦ IntRep ⟧-base A × ⟦ IntRep ⟧-base B
⟦ IntRep ⟧-base (A + B) = ⟦ IntRep ⟧-base A ⊎ ⟦ IntRep ⟧-base B
⟦ IntRep ⟧-base (_ ⇒[ _ ] _) = ⊤  -- Functions: return ⊤ (not used in K)
⟦ IntRep ⟧-base (Eff _ _) = ⊤     -- Effects: return ⊤ (not used in K)
⟦ IntRep ⟧-base (μ-type _) = ⊤    -- Recursive: return ⊤ (not used in K)
⟦ IntRep ⟧-base (ν-type _) = ⊤    -- Corecursive: return ⊤ (not used in K)
⟦ IntRep ⟧-base (GuardedT _ _) = ⊤ -- Guarded: return ⊤ (not used in K)
⟦ IntRep ⟧-base Int = IntRep
⟦ IntRep ⟧-base Float = AgdaFloat
⟦ IntRep ⟧-base Str = String
⟦ IntRep ⟧-base Buffer = String
⟦ IntRep ⟧-base (TVar _) = ⊤      -- Type variables: return ⊤

------------------------------------------------------------------------
-- Functor Translation
------------------------------------------------------------------------

-- | Translate syntactic Functor to semantic SFunctor
--
-- Uses the base interpretation for K positions.
--
translateF : Set → Functor → SFunctor
translateF IntRep (K A) = SK (⟦ IntRep ⟧-base A)
translateF IntRep Id = SId
translateF IntRep (F ⊕ G) = translateF IntRep F S⊕ translateF IntRep G
translateF IntRep (F ⊗ G) = translateF IntRep F S⊗ translateF IntRep G

------------------------------------------------------------------------
-- Semantic Fixed Points via Translation
--
-- These give us μ and ν without depending on the full ⟦_⟧.
------------------------------------------------------------------------

-- | Semantic μ via translation
--
-- μ-sem F = μS (translateF F)
--
μ-sem : Set → Functor → Set
μ-sem IntRep F = μS (translateF IntRep F)

-- | Semantic ν via translation
--
-- ν-sem F = νS (translateF F)
--
ν-sem : Set → Functor → Set
ν-sem IntRep F = νS (translateF IntRep F)

------------------------------------------------------------------------
-- Functor Interpretation Coherence
--
-- Show that the base interpretation applied to SFunctor equals
-- the original Functor interpretation (for well-formed functors).
------------------------------------------------------------------------

-- | Interpretation coherence for SFunctor
--
-- ⟦ translateF F ⟧SF X ≡ ⟦ F ⟧F-base X
-- (where ⟦_⟧F-base uses the base interpretation)
--
-- This is definitionally true by construction.
--
⟦_⟧F-base : Set → Functor → Set → Set
⟦ IntRep ⟧F-base (K A) X = ⟦ IntRep ⟧-base A
⟦ IntRep ⟧F-base Id X = X
⟦ IntRep ⟧F-base (F ⊕ G) X = ⟦ IntRep ⟧F-base F X ⊎ ⟦ IntRep ⟧F-base G X
⟦ IntRep ⟧F-base (F ⊗ G) X = ⟦ IntRep ⟧F-base F X × ⟦ IntRep ⟧F-base G X

-- | Translation preserves interpretation
translate-coherence : ∀ IntRep F X → ⟦ translateF IntRep F ⟧SF X ≡ ⟦ IntRep ⟧F-base F X
translate-coherence IntRep (K A) X = refl
translate-coherence IntRep Id X = refl
translate-coherence IntRep (F ⊕ G) X
  rewrite translate-coherence IntRep F X
        | translate-coherence IntRep G X = refl
translate-coherence IntRep (F ⊗ G) X
  rewrite translate-coherence IntRep F X
        | translate-coherence IntRep G X = refl

------------------------------------------------------------------------
-- Standard Functor Codes
--
-- These show how common data types translate.
------------------------------------------------------------------------

-- | Natural numbers: Nat = μ (K Unit ⊕ Id)
-- translateF NatF = SK ⊤ S⊕ SId
-- μS (SK ⊤ S⊕ SId) ≅ ⊤ ⊎ μS (SK ⊤ S⊕ SId) ≅ Nat

-- | List A = μ (K Unit ⊕ (K A ⊗ Id))
-- For base type A, translateF (ListF A) = SK ⊤ S⊕ (SK (⟦A⟧-base) S⊗ SId)
