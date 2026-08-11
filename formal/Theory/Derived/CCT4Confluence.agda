------------------------------------------------------------------------
-- Theory.Derived.CCT4Confluence
--
-- DERIVED THEOREM: CCT4 confluence, proven from smaller focused
-- hypotheses via the abstract diamond-to-confluence lemma.
--
-- This module reduces the CCT4 confluence obligation to three
-- hypotheses — one technical content-bearing fact plus two structural
-- bridges to the standard rewriting vocabulary:
--
--   (1) par-diamond : The parallel reduction _⟹_ has the DIAMOND
--       PROPERTY.
--   (2) ⟶*-to-par* : Every reduction sequence is a parallel-reduction
--       sequence.
--   (3) par*-to-⟶* : Every parallel-reduction sequence is a reduction
--       sequence.
--
-- From these, cct4-confluence is proven by
-- delegating to the abstract Takahashi lemma in ConfluenceFromDiamond.
--
-- TOWER LEVEL: CCT4.
------------------------------------------------------------------------

module Theory.Derived.CCT4Confluence where

open import Theory.CCTower using (TowerLevel; CCT4)
open import Theory.Systems.CCT4
open import Theory.Syntax.Reducible using (Reducible)
open import Theory.Derived.ConfluenceFromDiamond
  using (Star; done; _∷_; Diamond; confluence)
open import Data.Product
  using (Σ; _,_) renaming (_×_ to _∧_)

------------------------------------------------------------------------
-- Tower level annotation
------------------------------------------------------------------------

applies-to : TowerLevel
applies-to = CCT4

------------------------------------------------------------------------
-- CCT4 confluence, parameterized over a CCT4 structure equipped with
-- a Reducible carrier and a parallel reduction.
------------------------------------------------------------------------

module _ (S   : CCT4Structure)
         (Red : Reducible (CCT4Structure.Obj S) (CCT4Structure.Hom S))
         where
  open CCT4Structure S
  open Reducible Red

  module _
    ------------------------------------------------------------------
    -- Parallel reduction (provided by concrete syntax).
    ------------------------------------------------------------------
    (_⟹_ : ∀ {A B} → Hom A B → Hom A B → Set)

    ------------------------------------------------------------------
    -- HYPOTHESIS (par-diamond): the technical payload.
    ------------------------------------------------------------------
    (par-diamond : ∀ {A B} → Diamond (_⟹_ {A} {B}))

    ------------------------------------------------------------------
    -- HYPOTHESIS (⟶*-to-par*): forward bridge to parallel closure.
    ------------------------------------------------------------------
    (⟶*-to-par* : ∀ {A B} {t u : Hom A B} →
                  t ⟶* u → Star (_⟹_ {A} {B}) t u)

    ------------------------------------------------------------------
    -- HYPOTHESIS (par*-to-⟶*): backward bridge from parallel closure.
    ------------------------------------------------------------------
    (par*-to-⟶* : ∀ {A B} {t u : Hom A B} →
                  Star (_⟹_ {A} {B}) t u → t ⟶* u)

    where

    cct4-confluence :
      ∀ {A B} {t u v : Hom A B} →
      t ⟶* u → t ⟶* v →
      Σ (Hom A B) (λ w → (u ⟶* w) ∧ (v ⟶* w))
    cct4-confluence {A} {B} tu tv =
      let star-tu = ⟶*-to-par* tu
          star-tv = ⟶*-to-par* tv
          (w , star-uw , star-vw) =
            confluence (par-diamond {A} {B}) star-tu star-tv
      in  (w , par*-to-⟶* star-uw , par*-to-⟶* star-vw)
