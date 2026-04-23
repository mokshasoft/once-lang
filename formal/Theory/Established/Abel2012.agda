------------------------------------------------------------------------
-- Theory.Established.Abel2012
--
-- CITATION:
--   Abel, A. (2012). "Type-based termination, inflationary fixed-points,
--   and mixed inductive-coinductive types." FICS 2012, EPTCS 77.
--
-- TOWER LEVEL: CCT4 (BCCR).
--
-- THEOREM (Abel 2012):
--   Guarded corecursion on final coalgebras is productive: every term
--   reduces (in finitely many steps) to weak head normal form (WHNF).
--
-- PREREQUISITE:
--   All coalgebras used in ana must be GUARDED.
--
-- PARAMETERIZATION:
--   A CCT4 structure together with a Reducible carrier.
--
-- SCOPE OF THIS POSTULATE:
--   Productivity only. Weaker than SN: coinductive evaluation need
--   never terminate fully, only produce a next constructor.
------------------------------------------------------------------------

module Theory.Established.Abel2012 where

open import Theory.CCTower using (TowerLevel; CCT4)
open import Theory.Systems.CCT4
open import Theory.Syntax.Reducible using (Reducible)
open import Data.Product using (Σ; _,_) renaming (_×_ to _∧_)

------------------------------------------------------------------------
-- Tower level annotation
------------------------------------------------------------------------

applies-to : TowerLevel
applies-to = CCT4

------------------------------------------------------------------------
-- Guardedness and productivity
------------------------------------------------------------------------

module _ (S : CCT4Structure)
         (Red : Reducible (CCT4Structure.Obj S) (CCT4Structure.Hom S))
         where
  open CCT4Structure S
  open Reducible Red

  postulate
    IsGuarded : ∀ {F : Obj → Obj} {A} → Hom A (F A) → Set
    IsWHNF    : ∀ {A B} → Hom A B → Set

  postulate
    productivity :
      (all-coalgebras-guarded :
        ∀ {F : Obj → Obj} {A} (c : Hom A (F A)) → IsGuarded {F} {A} c) →
      ∀ {A B} (t : Hom A B) →
      Σ (Hom A B) (λ whnf → (t ⟶* whnf) ∧ IsWHNF whnf)
