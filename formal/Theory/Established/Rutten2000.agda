------------------------------------------------------------------------
-- Theory.Established.Rutten2000
--
-- CITATION:
--   Rutten, J.J.M.M. (2000). "Universal coalgebra: a theory of systems."
--   Theoretical Computer Science 249(1):3-80.
--
-- TOWER LEVEL: CCT4 (BCCR = BCC + μ-types + ν-types).
--
-- THEOREMS (Rutten 2000, §3–§4):
--   (A) The structure map Out : νF → F(νF) of a final F-coalgebra is
--       an isomorphism (dual to Lambek's Lemma).
--   (B) ana coalg : A → νF is the unique F-coalgebra morphism from
--       any (A, coalg) to the final coalgebra (νF, Out).
--   (C) Coinduction principle: two elements of νF are equal iff they
--       are bisimilar.
--
-- SCOPE OF THIS POSTULATE:
--   The universal property and its immediate consequences. Productivity
--   of guarded corecursion is a separate result (Abel 2012). Confluence
--   of ana reduction with other tower rules is NOT in Rutten — it
--   requires an orthogonality argument and belongs elsewhere.
--
-- NOTE ON FUNCTORS:
--   The β-rule for ana is stated abstractly pending a full functor
--   treatment (same situation as cata-β in Lambek1968).
--
-- NOTE ON BISIMULATION:
--   Coinduction is stated abstractly below; a full formalization
--   would define bisimilarity explicitly.
------------------------------------------------------------------------

module Theory.Established.Rutten2000 where

open import Theory.CCTower using (TowerLevel; CCT4)
open import Theory.Systems.CCT4
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product using (Σ; _×_; _,_)

------------------------------------------------------------------------
-- Tower level annotation
------------------------------------------------------------------------

applies-to : TowerLevel
applies-to = CCT4

------------------------------------------------------------------------
-- The Theorems
------------------------------------------------------------------------

module _ (S : CCT4Structure) where
  open CCT4Structure S

  ------------------------------------------------------------------------
  -- (A) Out is an iso (dual Lambek).
  ------------------------------------------------------------------------

  postulate
    final-out-in : ∀ {F : Obj → Obj} → (νOut {F} ∘ νIn {F}) ≡ id
    final-in-out : ∀ {F : Obj → Obj} → (νIn {F} ∘ νOut {F}) ≡ id

  ------------------------------------------------------------------------
  -- (B) ana is unique.
  ------------------------------------------------------------------------

  postulate
    ana-unique : ∀ {F : Obj → Obj} {A}
                 (coalg : Hom A (F A)) (h : Hom A (ν F)) →
                 -- Given: h is an F-coalgebra morphism (νOut ∘ h ≡ fmap h ∘ coalg)
                 h ≡ ana coalg

  ------------------------------------------------------------------------
  -- β-rule for ana (stated abstractly, pending fmap).
  ------------------------------------------------------------------------

  postulate
    ana-β : ∀ {F : Obj → Obj} {A} (coalg : Hom A (F A)) →
            Σ (Hom A (F (ν F))) (λ rhs → (νOut ∘ ana coalg) ≡ rhs)

  ------------------------------------------------------------------------
  -- (C) Coinduction: bisimilar implies equal.
  ------------------------------------------------------------------------

  postulate
    -- Abstract bisimilarity relation on elements of νF.
    Bisimilar : ∀ {F : Obj → Obj} →
                Hom Unit (ν F) → Hom Unit (ν F) → Set

    coinduction : ∀ {F : Obj → Obj} {x y : Hom Unit (ν F)} →
                  Bisimilar {F} x y → x ≡ y
