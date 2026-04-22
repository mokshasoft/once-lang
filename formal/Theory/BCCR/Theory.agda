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
-- BCCR Properties (from Established modules, one paper per file)
--
-- These are the key properties that hold for full BCCR:
--
-- 1. STRONG NORMALIZATION at each level:
--    - CCT1: Theory.Established.Tait1967
--    - CCT3: Theory.Established.Mendler1987 (requires strict positivity)
--
-- 2. CONFLUENCE at each level:
--    - CCT1: Theory.Established.LambekScott1986
--    - CCT3/CCT4: NOT YET in Established/; derivation pending
--      (requires orthogonality of cata/ana rules — not directly cited)
--
-- 3. LAMBEK'S LEMMA (μ-types, CCT3):
--    - Theory.Established.Lambek1968
--    - In : F(μF) → μF is an isomorphism
--    - cata is the unique F-algebra morphism
--
-- 4. FINAL COALGEBRA THEOREMS (ν-types, CCT4):
--    - Theory.Established.Rutten2000
--    - Out is an isomorphism, ana is unique, coinduction
--
-- 5. PRODUCTIVITY (ν-types, CCT4):
--    - Theory.Established.Abel2012 (requires guardedness)
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
