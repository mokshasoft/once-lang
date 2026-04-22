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
--   functors. A functor F is strictly positive if in its definition
--   the recursive variable appears only in strictly positive positions
--   (not to the left of an arrow, not in a function argument).
--
-- PROOF TECHNIQUE:
--   Extension of Girard's reducibility technique to recursive types,
--   using a notion of "inflationary" type interpretations.
--
-- SCOPE OF THIS POSTULATE:
--   SN for CCT3 under the strict-positivity assumption. This is a
--   DIFFERENT theorem from Tait 1967 (which covers CCT1) — different
--   proof technique, different conditions, different paper. Do not
--   conflate.
--
-- NOTE:
--   Strict positivity is itself a predicate on Obj → Obj maps.
--   We carry it abstractly as IsStrictlyPositive; concrete instances
--   would discharge this by inspecting the functor's definition.
------------------------------------------------------------------------

module Theory.Established.Mendler1987 where

open import Theory.CCTower using (TowerLevel; CCT3)
open import Theory.Systems.CCT3
open import Data.Product using (Σ; _,_) renaming (_×_ to _∧_)

------------------------------------------------------------------------
-- Tower level annotation
------------------------------------------------------------------------

applies-to : TowerLevel
applies-to = CCT3

------------------------------------------------------------------------
-- Strict positivity + the theorem
------------------------------------------------------------------------

module _ (S : CCT3Structure) where
  open CCT3Structure S

  -- Predicate: the functor F used for μF is strictly positive.
  postulate
    IsStrictlyPositive : (Obj → Obj) → Set

  -- Mendler's strong-normalization theorem, conditional on strict
  -- positivity of all μ-types appearing in the term.
  postulate
    strong-normalization :
      (all-μ-strictly-positive :
        ∀ (F : Obj → Obj) → IsStrictlyPositive F) →
      ∀ {A B} (t : Hom A B) →
      Σ (Hom A B) (λ nf → (t ⟶* nf) ∧ IsNormalForm nf)
