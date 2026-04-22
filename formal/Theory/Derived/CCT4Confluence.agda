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
--       PROPERTY. This is the Takahashi-style payload — the actual
--       orthogonality of cata/ana/CCC rules. Concrete proofs: this
--       is what Lambek-Scott 1986 establishes for pure CCC, and what
--       Mendler 1987 / Abel 2012 extend for recursion schemes.
--
--   (2) ⟶*-to-par* : Every reduction sequence is a parallel-reduction
--       sequence. Structural — follows from _⟹_ including all single
--       reduction steps.
--
--   (3) par*-to-⟶* : Every parallel-reduction sequence is a reduction
--       sequence. Structural — follows from every parallel step
--       decomposing into finitely many single steps.
--
-- From these, cct4-confluence is proven with zero new postulates by
-- delegating to the abstract Takahashi lemma in ConfluenceFromDiamond.
--
-- TOWER LEVEL: CCT4 (the IR Once is built on).
--
-- REMAINING OBLIGATION:
--   Proving (1), (2), (3) at instantiation time. (1) is the core
--   confluence work; (2) and (3) are bookkeeping the concrete syntax
--   must discharge.
------------------------------------------------------------------------

module Theory.Derived.CCT4Confluence where

open import Theory.CCTower using (TowerLevel; CCT4)
open import Theory.Systems.CCT4
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
-- CCT4 confluence, parameterized over a parallel reduction.
------------------------------------------------------------------------

module _ (S : CCT4Structure) where
  open CCT4Structure S

  module _
    ------------------------------------------------------------------
    -- Parallel reduction (provided by concrete syntax).
    ------------------------------------------------------------------
    (_⟹_ : ∀ {A B} → Hom A B → Hom A B → Set)

    ------------------------------------------------------------------
    -- HYPOTHESIS (par-diamond): the technical payload.
    --
    -- Parallel reduction has the diamond property. This is where the
    -- orthogonality of cata, ana, and CCC β/η rules must be verified
    -- for the concrete reduction system.
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

    ----------------------------------------------------------------------
    -- The main theorem: CCT4 reduction is confluent.
    --
    -- Proof: run the abstract diamond-to-confluence lemma on the
    -- parallel closure, then transport along the bridges.
    ----------------------------------------------------------------------

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
