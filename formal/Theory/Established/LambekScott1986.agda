------------------------------------------------------------------------
-- Theory.Established.LambekScott1986
--
-- CITATION:
--   Lambek, J. & Scott, P.J. (1986). "Introduction to Higher Order
--   Categorical Logic." Cambridge Studies in Advanced Mathematics 7,
--   Cambridge University Press.
--
-- TOWER LEVEL: CCT1 (CCC).
--
-- THEOREM (Lambek & Scott 1986, Part I):
--   Reduction in the Cartesian Closed Category is confluent
--   (Church-Rosser): if t reduces to both u and v, then u and v have
--   a common reduct w.
--
-- PROOF TECHNIQUE:
--   Parallel reduction + diamond property (Takahashi-style).
--
-- SCOPE OF THIS POSTULATE:
--   CCT1 confluence only. Extending confluence to cata rules (CCT3)
--   or ana rules (CCT4) requires an additional orthogonality argument
--   that is NOT in Lambek & Scott 1986. Such extensions live in a
--   separate (derived or postulated) module, not in this citation.
------------------------------------------------------------------------

module Theory.Established.LambekScott1986 where

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
------------------------------------------------------------------------

module _ (S : CCT1Structure) where
  open CCT1Structure S

  postulate
    confluence :
      ∀ {A B} {t u v : Hom A B} →
      t ⟶* u → t ⟶* v →
      Σ (Hom A B) (λ w → (u ⟶* w) ∧ (v ⟶* w))
