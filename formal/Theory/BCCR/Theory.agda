------------------------------------------------------------------------
-- Theory.BCCR.Theory
--
-- BCCR THEORY: Properties of Bicartesian Closed Categories with Recursion
--
-- BCCR = CCT4 (the top level of the categorical tower)
--
-- This module collects the established properties for the full BCCR
-- structure, referencing the tower levels and established results.
------------------------------------------------------------------------

module Theory.BCCR.Theory where

open import Theory.CCTower using (TowerLevel; CCT4; BCCR)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product using (Σ; _×_; _,_)

------------------------------------------------------------------------
-- BCCR = CCT4
------------------------------------------------------------------------

bccr-level : TowerLevel
bccr-level = BCCR  -- = CCT4

------------------------------------------------------------------------
-- BCCR Properties (from Established modules)
--
-- These are the key properties that hold for full BCCR:
--
-- 1. CONFLUENCE (Church-Rosser)
--    Source: Established/StrongNormalization.cct4-confluence
--    Requires: orthogonality of cata and ana rules
--
-- 2. STRONG NORMALIZATION / PRODUCTIVITY
--    Source: Established/StrongNormalization.cct4-productivity
--    Requires: strict positivity for μ, guardedness for ν
--
-- 3. LAMBEK'S LEMMA (for μ-types)
--    Source: Established/LambekLemma
--    In is an isomorphism, cata is unique
--
-- 4. COALGEBRA THEOREMS (for ν-types)
--    Source: Established/CoalgebraTheorems
--    Out is an isomorphism, ana is unique, coinduction principle
------------------------------------------------------------------------

-- Re-export the tower level
open import Theory.CCTower public using (TowerLevel; CCTB; CCT1; CCT2; CCT3; CCT4; BCCR)

------------------------------------------------------------------------
-- Summary: What BCCR Provides
------------------------------------------------------------------------
--
-- Structure (from CCTower):
--   CCTB: id, ∘, terminal, fst, snd, ⟨_,_⟩
--   CCT1: + curry, apply (exponentials)
--   CCT2: + initial, inl, inr, [_,_] (coproducts)
--   CCT3: + μF, In, Out, cata (initial algebras)
--   CCT4: + νF, In, Out, ana (final coalgebras)
--
-- Properties (from Established):
--   CCT1: Confluence (Lambek & Scott), SN (Tait)
--   CCT2: Confluence, SN (extends CCT1)
--   CCT3: Confluence, SN (Mendler), Lambek's Lemma
--   CCT4: Confluence, Productivity (Abel), Coalgebra theorems
--
-- The tower structure means:
--   - Each level extends the previous
--   - Properties at lower levels lift to higher levels
--   - Proofs are compositional (small, focused)
------------------------------------------------------------------------
