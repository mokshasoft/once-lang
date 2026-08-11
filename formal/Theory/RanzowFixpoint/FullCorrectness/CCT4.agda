------------------------------------------------------------------------
-- Theory.RanzowFixpoint.FullCorrectness.CCT4
--
-- Full RF correctness (fixpoint ⟹ correctness on all inputs) at CCT4.
--
-- PROOF: by projection to CCT3.
--
-- Every CCT4 structure contains a CCT3 structure (the bccμ field with
-- `open public`), so CCT3 full correctness applies directly. The
-- ν-level additions do not affect the argument — the encoding targets
-- μ-data, and the property only uses composition, reduction, and the
-- Code object, all of which are shared with CCT3.
--
-- Rests, via FullCorrectness, on exactly one Established postulate:
-- Transparency.
--
-- TOWER LEVEL: CCT4.
------------------------------------------------------------------------

module Theory.RanzowFixpoint.FullCorrectness.CCT4 where

open import Theory.CCTower using (TowerLevel; CCT4)
open import Theory.Systems.CCT3 using (CCT3Structure)
open import Theory.Systems.CCT4
open import Theory.Syntax.Reducible using (Reducible)
open import Theory.RanzowFixpoint using (EncodingScheme; HasRanzowFixpoint)
open import Theory.Encoding.Inductive using (EncodingInductive)
import Theory.RanzowFixpoint.FullCorrectness as CCT3-FC
open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------
-- Tower level annotation
------------------------------------------------------------------------

applies-to : TowerLevel
applies-to = CCT4

------------------------------------------------------------------------
-- Projection: a CCT4 structure contains a CCT3 structure.
------------------------------------------------------------------------

to-CCT3 : CCT4Structure → CCT3Structure
to-CCT3 S = CCT4Structure.bccμ S

------------------------------------------------------------------------
-- The theorem at CCT4, by delegation to CCT3.
--
-- The Reducible carrier and the EncodingScheme/EncodingInductive are
-- all shared between CCT4 and its underlying CCT3, so we just pass
-- them through.
------------------------------------------------------------------------

module _ (S   : CCT4Structure)
         (Red : Reducible (CCT4Structure.Obj S) (CCT4Structure.Hom S))
         (E   : EncodingScheme (to-CCT3 S))
         (EI  : EncodingInductive (to-CCT3 S) Red E)
         where
  open CCT4Structure S
  open Reducible Red
  open EncodingScheme E

  fixpoint-implies-correctness :
    ∀ (spec : ∀ {A B} → Hom A B → Hom A B)
      (T : Hom Code Code) →
      IsNormalForm T →
      spec T ≡ T →
      HasRanzowFixpoint (to-CCT3 S) Red E T →
      ∀ {A B} (g : Hom A B) →
      (T ∘ encode g) ⟶* encode (spec g)
  fixpoint-implies-correctness =
    CCT3-FC.fixpoint-implies-correctness (to-CCT3 S) Red E EI
