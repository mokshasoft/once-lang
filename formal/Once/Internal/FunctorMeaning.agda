-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Internal.FunctorMeaning — a functor code, read as a polynomial functor
-- on sets.
--
-- INTERNAL (D333). A code's constant positions hold BASE types (`WellFormedF`), so they
-- are read by `⟦_,_⟧-base` — over the carriers chosen for `Int` and `Float` —
-- without the full meaning of types; `translateF` is the code's polynomial,
-- and `μ-sem`/`ν-sem` its initial algebra and final coalgebra.
------------------------------------------------------------------------

module Once.Internal.FunctorMeaning where

open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)
open import Once.Spec.Type using (var; Type; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; K; Id; _⊕_; _⊗_)
open import Once.Internal.Type using (μ-type; ν-type; Functor)
open import Once.Internal.Polynomial using (SFunctor; SK; SId; _S⊕_; _S⊗_; μS; νS)

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
-- PLAN 0.72 (D112): the THIRD place `Float` was pinned to Agda's double while
-- `Int`'s carrier was a parameter (`Semantics.Value` and `IRTy` are the other
-- two). Same fix, same reason.
⟦_,_⟧-base : Set → Set → Type → Set
⟦ IntRep , FloatRep ⟧-base Unit = ⊤
⟦ IntRep , FloatRep ⟧-base Void = ⊥
⟦ IntRep , FloatRep ⟧-base (A * B) = ⟦ IntRep , FloatRep ⟧-base A × ⟦ IntRep , FloatRep ⟧-base B
⟦ IntRep , FloatRep ⟧-base (A + B) = ⟦ IntRep , FloatRep ⟧-base A ⊎ ⟦ IntRep , FloatRep ⟧-base B
⟦ IntRep , FloatRep ⟧-base (_ ⇒[ _ ] _) = ⊤  -- Functions (all kinds): return ⊤ (not used in K)
⟦ IntRep , FloatRep ⟧-base (μ-type _) = ⊤    -- Recursive: return ⊤ (not used in K)
⟦ IntRep , FloatRep ⟧-base (ν-type _ _) = ⊤    -- Corecursive: return ⊤ (not used in K)
⟦ IntRep , FloatRep ⟧-base Int = IntRep
⟦ IntRep , FloatRep ⟧-base Float = FloatRep
⟦ IntRep , FloatRep ⟧-base (var ())
-- TVar removed from Type; now in PolyType (see Once.Type)

------------------------------------------------------------------------
-- Functor Translation
------------------------------------------------------------------------

-- | Translate syntactic Functor to semantic SFunctor
--
-- Uses the base interpretation for K positions.
--
translateF : Set → Set → Functor → SFunctor
translateF IntRep FloatRep (K A) = SK (⟦ IntRep , FloatRep ⟧-base A)
translateF IntRep FloatRep Id = SId
translateF IntRep FloatRep (F ⊕ G) = translateF IntRep FloatRep F S⊕ translateF IntRep FloatRep G
translateF IntRep FloatRep (F ⊗ G) = translateF IntRep FloatRep F S⊗ translateF IntRep FloatRep G

------------------------------------------------------------------------
-- Semantic Fixed Points via Translation
--
-- These give us μ and ν without depending on the full ⟦_⟧.
------------------------------------------------------------------------

-- | Semantic μ via translation
--
-- μ-sem F = μS (translateF F)
--
μ-sem : Set → Set → Functor → Set
μ-sem IntRep FloatRep F = μS (translateF IntRep FloatRep F)

-- | Semantic ν via translation
--
-- ν-sem F = νS (translateF F)
--
ν-sem : Set → Set → Functor → Set
ν-sem IntRep FloatRep F = νS (translateF IntRep FloatRep F)

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
⟦_,_⟧F-base : Set → Set → Functor → Set → Set
⟦ IntRep , FloatRep ⟧F-base (K A) X = ⟦ IntRep , FloatRep ⟧-base A
⟦ IntRep , FloatRep ⟧F-base Id X = X
⟦ IntRep , FloatRep ⟧F-base (F ⊕ G) X = ⟦ IntRep , FloatRep ⟧F-base F X ⊎ ⟦ IntRep , FloatRep ⟧F-base G X
⟦ IntRep , FloatRep ⟧F-base (F ⊗ G) X = ⟦ IntRep , FloatRep ⟧F-base F X × ⟦ IntRep , FloatRep ⟧F-base G X

