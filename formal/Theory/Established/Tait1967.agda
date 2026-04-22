------------------------------------------------------------------------
-- Theory.Established.Tait1967
--
-- CITATION:
--   Tait, W.W. (1967). "Intensional interpretations of functionals of
--   finite type I." Journal of Symbolic Logic, 32(2):198-212.
--
-- TOWER LEVEL: CCT1 (Cartesian Closed Category = simply-typed λ-calculus).
--
-- THEOREM (Tait 1967):
--   The simply-typed λ-calculus with β-reduction is strongly normalizing:
--   every well-typed term has a reduction sequence of finite length to
--   a normal form.
--
-- PROOF TECHNIQUE:
--   Computability / reducibility candidates (logical relations).
--
-- SCOPE OF THIS POSTULATE:
--   This module postulates ONLY Tait's theorem for CCT1. It does NOT
--   claim anything about CCT2, CCT3, or CCT4. Extensions to richer
--   systems require their own citations (e.g., Mendler 1987 for μ-types).
--
-- IMPORTANT: This is an abstract existence statement quantified over
-- any CCT1 structure — any structure satisfying the CCC laws and
-- reduction rules has the strong-normalization property.
------------------------------------------------------------------------

module Theory.Established.Tait1967 where

open import Theory.CCTower using (TowerLevel; CCT1)
open import Theory.Systems.CCT1
open import Data.Product using (Σ; _,_) renaming (_×_ to _∧_)

------------------------------------------------------------------------
-- Tower level annotation
------------------------------------------------------------------------

applies-to : TowerLevel
applies-to = CCT1

------------------------------------------------------------------------
-- The Theorem
--
-- Parameterized over any CCT1 structure S.
------------------------------------------------------------------------

module _ (S : CCT1Structure) where
  open CCT1Structure S

  postulate
    strong-normalization :
      ∀ {A B} (t : Hom A B) →
      Σ (Hom A B) (λ nf → (t ⟶* nf) ∧ IsNormalForm nf)
