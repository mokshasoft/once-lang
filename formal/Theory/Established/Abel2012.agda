------------------------------------------------------------------------
-- Theory.Established.Abel2012
--
-- CITATION:
--   Abel, A. (2012). "Type-based termination, inflationary fixed-points,
--   and mixed inductive-coinductive types." In Proceedings of the 8th
--   Workshop on Fixed Points in Computer Science (FICS 2012), EPTCS 77.
--
-- TOWER LEVEL: CCT4 (BCCR).
--
-- THEOREM (Abel 2012):
--   Guarded corecursion on final coalgebras is productive: every term
--   reduces (in finitely many steps) to weak head normal form (WHNF).
--
-- PREREQUISITE:
--   All coalgebras used in ana must be GUARDED — each corecursive call
--   must be under a constructor of the functor F.
--
-- PROOF TECHNIQUE:
--   Sized types / inflationary fixed points (Mendler-style for ν).
--
-- SCOPE OF THIS POSTULATE:
--   Productivity only. This is a weaker statement than strong
--   normalization: coinductive evaluation need never terminate fully,
--   only produce a next constructor in finite steps. For SN on CCT3
--   (μ-types) see Mendler1987.
--
-- NOTE:
--   Guardedness is a predicate on coalgebras carried abstractly
--   (IsGuarded), discharged by the concrete reduction system that
--   instantiates this structure.
------------------------------------------------------------------------

module Theory.Established.Abel2012 where

open import Theory.CCTower using (TowerLevel; CCT4)
open import Theory.Systems.CCT4
open import Data.Product using (Σ; _,_) renaming (_×_ to _∧_)

------------------------------------------------------------------------
-- Tower level annotation
------------------------------------------------------------------------

applies-to : TowerLevel
applies-to = CCT4

------------------------------------------------------------------------
-- Guardedness and productivity
------------------------------------------------------------------------

module _ (S : CCT4Structure) where
  open CCT4Structure S

  postulate
    -- Guardedness of a coalgebra.
    IsGuarded : ∀ {F : Obj → Obj} {A} → Hom A (F A) → Set

    -- Weak head normal form (constructor at the head).
    IsWHNF : ∀ {A B} → Hom A B → Set

  -- Productivity: under global guardedness, every term reaches WHNF.
  postulate
    productivity :
      (all-coalgebras-guarded :
        ∀ {F : Obj → Obj} {A} (c : Hom A (F A)) → IsGuarded {F} {A} c) →
      ∀ {A B} (t : Hom A B) →
      Σ (Hom A B) (λ whnf → (t ⟶* whnf) ∧ IsWHNF whnf)
