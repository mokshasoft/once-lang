------------------------------------------------------------------------
-- Theory.Established.Mendler1987
--
-- CITATION:
--   Mendler, N.P. (1987). "Recursive types and type constraints in
--   second-order lambda calculus." Proceedings of the Second Annual
--   IEEE Symposium on Logic in Computer Science (LICS '87), pp. 30-36.
--
-- TOWER LEVEL: CCT3 (BCC + μ-types).
--
-- THEOREM (Mendler 1987):
--   System F extended with strictly-positive recursive types is
--   strongly normalizing.
--
-- PREREQUISITE (IMPORTANT):
--   The theorem requires all μ-types to be over STRICTLY POSITIVE
--   functors.
--
-- PARAMETERIZATION:
--   A CCT3 structure together with a Reducible carrier.
--
-- SCOPE OF THIS POSTULATE:
--   SN for CCT3 under the strict-positivity assumption. This is a
--   DIFFERENT theorem from Tait 1967 (which covers CCT1).
------------------------------------------------------------------------

module Theory.Established.Mendler1987 where

open import Theory.CCTower using (TowerLevel; CCT3)
open import Theory.Systems.CCT3
open import Theory.Syntax.Reducible using (Reducible)
open import Data.Product using (Σ; _,_) renaming (_×_ to _∧_)

------------------------------------------------------------------------
-- Tower level annotation
------------------------------------------------------------------------

applies-to : TowerLevel
applies-to = CCT3

------------------------------------------------------------------------
-- Strict positivity + the theorem
------------------------------------------------------------------------

module _ (S : CCT3Structure)
         (Red : Reducible (CCT3Structure.Obj S) (CCT3Structure.Hom S))
         where
  open CCT3Structure S
  open Reducible Red

  postulate
    IsStrictlyPositive : (Obj → Obj) → Set

  postulate
    strong-normalization :
      (all-μ-strictly-positive :
        ∀ (F : Obj → Obj) → IsStrictlyPositive F) →
      ∀ {A B} (t : Hom A B) →
      Σ (Hom A B) (λ nf → (t ⟶* nf) ∧ IsNormalForm nf)
