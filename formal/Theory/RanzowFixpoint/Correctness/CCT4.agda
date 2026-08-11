------------------------------------------------------------------------
-- Theory.RanzowFixpoint.Correctness.CCT4
--
-- Ranzow Fixpoint correctness at CCT4 (full BCCR).
--
-- PROOF: by projection to CCT3.
--
-- Every CCT4 structure contains a CCT3 structure (the bccμ field with
-- `open public`), so CCT3 correctness applies directly. The ν-level
-- additions do not affect the fixpoint argument — the encoding targets
-- μ-data, and the RF property only uses composition and reduction,
-- both of which are shared with CCT3.
--
-- TOWER LEVEL: CCT4.
------------------------------------------------------------------------

module Theory.RanzowFixpoint.Correctness.CCT4 where

open import Theory.CCTower using (TowerLevel; CCT4)
open import Theory.Systems.CCT3 using (CCT3Structure)
open import Theory.Systems.CCT4
open import Theory.Syntax.Reducible using (Reducible)
open import Theory.RanzowFixpoint using (EncodingScheme; HasRanzowFixpoint)
import Theory.RanzowFixpoint.Correctness as CCT3-Corr
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product using (Σ; _,_) renaming (_×_ to _∧_)

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
-- The Reducible carrier is shared: the same _⟶_ / _⟶*_ / IsNormalForm
-- apply at every tower level, since _⟶_ is indexed on morphisms of
-- the common Hom. We pass it through from CCT4 directly.
------------------------------------------------------------------------

module _ (S   : CCT4Structure)
         (Red : Reducible (CCT4Structure.Obj S) (CCT4Structure.Hom S))
         (E   : EncodingScheme (to-CCT3 S)) where
  open CCT4Structure S
  open Reducible Red
  open EncodingScheme E

  module _
    (nf-stable :
      ∀ {A B} {t u : Hom A B} →
      IsNormalForm t → t ⟶* u → t ≡ u)
    (confluence :
      ∀ {A B} {t u v : Hom A B} →
      t ⟶* u → t ⟶* v →
      Σ (Hom A B) (λ w → (u ⟶* w) ∧ (v ⟶* w)))
    where

    nf-unique : ∀ {A B} {t u v : Hom A B} →
                t ⟶* u → t ⟶* v →
                IsNormalForm u → IsNormalForm v →
                u ≡ v
    nf-unique = CCT3-Corr.nf-unique (to-CCT3 S) Red E nf-stable confluence

    fixpoint-is-canonical :
      ∀ (T : Hom Code Code) →
      HasRanzowFixpoint (to-CCT3 S) Red E T →
      IsNormalForm (encode T) →
      ∀ {u} → (T ∘ encode T) ⟶* u →
      IsNormalForm u →
      u ≡ encode T
    fixpoint-is-canonical =
      CCT3-Corr.fixpoint-is-canonical (to-CCT3 S) Red E nf-stable confluence

    fixpoint-is-unique :
      ∀ (T : Hom Code Code) →
      HasRanzowFixpoint (to-CCT3 S) Red E T →
      IsNormalForm (encode T) →
      ∀ {u v} →
      (T ∘ encode T) ⟶* u → IsNormalForm u →
      (T ∘ encode T) ⟶* v → IsNormalForm v →
      u ≡ v
    fixpoint-is-unique =
      CCT3-Corr.fixpoint-is-unique (to-CCT3 S) Red E nf-stable confluence
