------------------------------------------------------------------------
-- Theory.RanzowFixpoint.Correctness.CCT4
--
-- Ranzow Fixpoint correctness at CCT4 (full BCCR).
--
-- PROOF: by projection to CCT3.
--
-- Every CCT4 structure contains a CCT3 structure (the bccμ field with
-- `open public`), so CCT3 correctness applies directly. The ν-level
-- additions (ν, νOut, νIn, ana) introduce extra reduction rules in the
-- same _⟶_ relation but do not affect the fixpoint argument — the
-- encoding targets μ-data (which lives at CCT3), and the RF property
-- only uses composition and reduction, both of which are shared with
-- CCT3.
--
-- ZERO POSTULATES in this module, ZERO NEW HYPOTHESES beyond what
-- CCT3 correctness already requires.
--
-- TOWER LEVEL: CCT4 (the IR Once is built on).
------------------------------------------------------------------------

module Theory.RanzowFixpoint.Correctness.CCT4 where

open import Theory.CCTower using (TowerLevel; CCT4)
open import Theory.Systems.CCT3 using (CCT3Structure)
open import Theory.Systems.CCT4
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
-- Note: the EncodingScheme is parameterized by the CCT3 substructure,
-- not the CCT4 structure. This reflects that the encoding targets
-- μ-data: Code = μ TermF for some TermF: Obj → Obj. The ν-types do
-- not appear in the encoding, and concrete instantiations at CCT4
-- reuse CCT3 encodings unchanged.
------------------------------------------------------------------------

module _ (S : CCT4Structure) (E : EncodingScheme (to-CCT3 S)) where
  open CCT4Structure S
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

    -- Derived: NFs reachable from a common term are equal.
    nf-unique : ∀ {A B} {t u v : Hom A B} →
                t ⟶* u → t ⟶* v →
                IsNormalForm u → IsNormalForm v →
                u ≡ v
    nf-unique = CCT3-Corr.nf-unique (to-CCT3 S) E nf-stable confluence

    -- Main theorem at CCT4: the Ranzow Fixpoint is canonical.
    fixpoint-is-canonical :
      ∀ (T : Hom Code Code) →
      HasRanzowFixpoint (to-CCT3 S) E T →
      IsNormalForm (encode T) →
      ∀ {u} → (T ∘ encode T) ⟶* u →
      IsNormalForm u →
      u ≡ encode T
    fixpoint-is-canonical =
      CCT3-Corr.fixpoint-is-canonical (to-CCT3 S) E nf-stable confluence

    -- Corollary: any two NFs reachable from (T ∘ encode T) are equal.
    fixpoint-is-unique :
      ∀ (T : Hom Code Code) →
      HasRanzowFixpoint (to-CCT3 S) E T →
      IsNormalForm (encode T) →
      ∀ {u v} →
      (T ∘ encode T) ⟶* u → IsNormalForm u →
      (T ∘ encode T) ⟶* v → IsNormalForm v →
      u ≡ v
    fixpoint-is-unique =
      CCT3-Corr.fixpoint-is-unique (to-CCT3 S) E nf-stable confluence
