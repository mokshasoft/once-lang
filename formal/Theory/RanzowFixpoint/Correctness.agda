------------------------------------------------------------------------
-- Theory.RanzowFixpoint.Correctness
--
-- Consequences of the Ranzow Fixpoint property.
--
-- This module contains ZERO postulates. Every theorem takes the
-- required Established math facts as explicit hypotheses. At a concrete
-- instantiation, clients discharge these hypotheses using modules in
-- Theory.Established.* (e.g., LambekScott1986.confluence).
--
-- TOWER LEVEL: CCT3.
--
-- KEY RESULT (fixpoint-is-canonical):
--   Given confluence and normal-form stability, if T has the Ranzow
--   Fixpoint property and encode T is in normal form, then any normal
--   form reachable from (T ∘ encode T) is equal to encode T.
--
-- This is a HONEST fragment of the "fixpoint ⟹ correctness" story:
-- it captures the uniqueness-of-the-fixpoint part. The full jump from
-- "fixpoint on ⌜T⌝" to "correctness on arbitrary inputs" additionally
-- requires transparency and encoding-completeness, which are not
-- formalized here.
------------------------------------------------------------------------

module Theory.RanzowFixpoint.Correctness where

open import Theory.CCTower using (TowerLevel; CCT3)
open import Theory.Systems.CCT3
open import Theory.RanzowFixpoint using (EncodingScheme; HasRanzowFixpoint)
open import Relation.Binary.PropositionalEquality
  using (_≡_; sym; trans)
open import Data.Product
  using (Σ; _,_; proj₁; proj₂) renaming (_×_ to _∧_)

------------------------------------------------------------------------
-- Tower level annotation
------------------------------------------------------------------------

applies-to : TowerLevel
applies-to = CCT3

------------------------------------------------------------------------
-- The correctness fragment
--
-- Parameterized over:
--   - S : a CCT3 structure
--   - E : an encoding scheme for S
-- and over hypotheses that concrete instantiations discharge from
-- Established math modules:
--   - nf-stable : normal forms do not reduce
--   - confluence : reduction is Church-Rosser
------------------------------------------------------------------------

module _ (S : CCT3Structure) (E : EncodingScheme S) where
  open CCT3Structure S
  open EncodingScheme E

  module _
    ------------------------------------------------------------------
    -- HYPOTHESIS (nf-stable):
    --   If t is a normal form, then anything reachable from t by
    --   reduction is equal to t. This is a characterization of what
    --   "normal form" means in the reduction system.
    ------------------------------------------------------------------
    (nf-stable :
      ∀ {A B} {t u : Hom A B} →
      IsNormalForm t → t ⟶* u → t ≡ u)

    ------------------------------------------------------------------
    -- HYPOTHESIS (confluence):
    --   Any two reduction paths from a common source can be joined.
    --   Discharged from Established.LambekScott1986.confluence at
    --   CCT1, or an analogous extension at CCT3.
    ------------------------------------------------------------------
    (confluence :
      ∀ {A B} {t u v : Hom A B} →
      t ⟶* u → t ⟶* v →
      Σ (Hom A B) (λ w → (u ⟶* w) ∧ (v ⟶* w)))

    where

    --------------------------------------------------------------------
    -- Derived lemma: normal forms reachable from a common term are
    -- equal. This is the direct constructive content of "confluence +
    -- nf-stable ⟹ unique normal forms."
    --------------------------------------------------------------------

    nf-unique : ∀ {A B} {t u v : Hom A B} →
                t ⟶* u → t ⟶* v →
                IsNormalForm u → IsNormalForm v →
                u ≡ v
    nf-unique tu tv nf-u nf-v with confluence tu tv
    ... | (_ , uw , vw) = trans (nf-stable nf-u uw) (sym (nf-stable nf-v vw))

    --------------------------------------------------------------------
    -- Main theorem: the Ranzow Fixpoint is canonical.
    --
    -- If T has the Ranzow Fixpoint property and encode T is already in
    -- normal form, then any normal form reachable from (T ∘ encode T)
    -- must equal encode T.
    --
    -- In plain words: running T on its own encoding can only yield the
    -- encoding itself (as a normal form).
    --------------------------------------------------------------------

    fixpoint-is-canonical :
      ∀ (T : Hom Code Code) →
      HasRanzowFixpoint S E T →
      IsNormalForm (encode T) →
      ∀ {u} → (T ∘ encode T) ⟶* u →
      IsNormalForm u →
      u ≡ encode T
    fixpoint-is-canonical T rf-T enc-is-nf path u-is-nf =
      nf-unique path rf-T u-is-nf enc-is-nf

    --------------------------------------------------------------------
    -- Corollary: the Ranzow Fixpoint has a UNIQUE normal form.
    --
    -- If T has the Ranzow Fixpoint and encode T is in normal form,
    -- then any two normal forms reachable from (T ∘ encode T) are
    -- equal. Both are equal to encode T.
    --
    -- This is the "fixpoint ⟹ uniqueness" content of the Ranzow
    -- Fixpoint: not only does T ∘ encode T reduce BACK to encode T,
    -- but encode T is the SINGLE normal form that any reduction path
    -- can reach.
    --------------------------------------------------------------------

    fixpoint-is-unique :
      ∀ (T : Hom Code Code) →
      HasRanzowFixpoint S E T →
      IsNormalForm (encode T) →
      ∀ {u v} →
      (T ∘ encode T) ⟶* u → IsNormalForm u →
      (T ∘ encode T) ⟶* v → IsNormalForm v →
      u ≡ v
    fixpoint-is-unique T rf-T enc-is-nf pu nf-u pv nf-v =
      trans (fixpoint-is-canonical T rf-T enc-is-nf pu nf-u)
            (sym (fixpoint-is-canonical T rf-T enc-is-nf pv nf-v))
