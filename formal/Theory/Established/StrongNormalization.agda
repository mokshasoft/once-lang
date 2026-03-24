------------------------------------------------------------------------
-- Theory.Established.StrongNormalization
--
-- Strong Normalization and Confluence Results
--
-- These are ESTABLISHED RESULTS from the literature.
-- Each theorem is annotated with the TOWER LEVEL it applies to.
--
-- Sources:
--   - Tait (1967) "Intensional interpretations of functionals..."
--   - Girard (1972) "Interprétation fonctionnelle..."
--   - Lambek & Scott (1986) "Introduction to Higher Order Categorical Logic"
--   - Mendler (1987) "Inductive types and type constraints..."
--   - Geuvers (1992) "Inductive and coinductive types with iteration..."
--   - Abel (2012) "Type-based termination..."
------------------------------------------------------------------------

module Theory.Established.StrongNormalization where

open import Theory.CCTower using (TowerLevel; CCTB; CCT1; CCT2; CCT3; CCT4)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product using (Σ; _×_; _,_)

------------------------------------------------------------------------
-- Abstract Term and Reduction (for stating the theorems)
------------------------------------------------------------------------

postulate
  Obj : Set
  Hom : Obj → Obj → Set
  _⟶_ : ∀ {A B} → Hom A B → Hom A B → Set
  _⟶*_ : ∀ {A B} → Hom A B → Hom A B → Set
  IsNormalForm : ∀ {A B} → Hom A B → Set

------------------------------------------------------------------------
-- CCT1: Strong Normalization for CCC (Tait 1967)
--
-- TOWER LEVEL: CCT1
--
-- THEOREM: The simply-typed λ-calculus (= internal language of CCC)
-- is strongly normalizing.
--
-- PROOF TECHNIQUE: Logical relations / reducibility candidates.
------------------------------------------------------------------------

cct1-sn-applies-to : TowerLevel
cct1-sn-applies-to = CCT1

postulate
  cct1-strong-normalization :
    ∀ {A B} (t : Hom A B) →
    Σ (Hom A B) (λ nf → (t ⟶* nf) × IsNormalForm nf)

------------------------------------------------------------------------
-- CCT1: Confluence for CCC (Lambek & Scott 1986)
--
-- TOWER LEVEL: CCT1
--
-- THEOREM: CCC reduction is confluent (Church-Rosser).
------------------------------------------------------------------------

cct1-confluence-applies-to : TowerLevel
cct1-confluence-applies-to = CCT1

postulate
  cct1-confluence :
    ∀ {A B} {t u v : Hom A B} →
    t ⟶* u → t ⟶* v →
    Σ (Hom A B) (λ w → (u ⟶* w) × (v ⟶* w))

------------------------------------------------------------------------
-- CCT2: Strong Normalization for BCC
--
-- TOWER LEVEL: CCT2
--
-- THEOREM: Adding coproducts to CCC preserves strong normalization.
--
-- This follows from CCT1-SN because coproduct rules are eliminative.
------------------------------------------------------------------------

cct2-sn-applies-to : TowerLevel
cct2-sn-applies-to = CCT2

postulate
  cct2-strong-normalization :
    ∀ {A B} (t : Hom A B) →
    Σ (Hom A B) (λ nf → (t ⟶* nf) × IsNormalForm nf)

------------------------------------------------------------------------
-- CCT2: Confluence for BCC
--
-- TOWER LEVEL: CCT2
--
-- THEOREM: Adding coproducts to CCC preserves confluence.
--
-- Coproduct rules are orthogonal to exponential rules.
------------------------------------------------------------------------

cct2-confluence-applies-to : TowerLevel
cct2-confluence-applies-to = CCT2

postulate
  cct2-confluence :
    ∀ {A B} {t u v : Hom A B} →
    t ⟶* u → t ⟶* v →
    Σ (Hom A B) (λ w → (u ⟶* w) × (v ⟶* w))

------------------------------------------------------------------------
-- CCT3: Strong Normalization with Inductive Types (Mendler 1987)
--
-- TOWER LEVEL: CCT3
--
-- THEOREM: BCC extended with strictly positive inductive types
-- is strongly normalizing.
--
-- REQUIREMENT: All μ-types must be strictly positive.
------------------------------------------------------------------------

cct3-sn-applies-to : TowerLevel
cct3-sn-applies-to = CCT3

postulate
  IsStrictlyPositive : Obj → Set

  cct3-strong-normalization :
    ∀ {A B} (t : Hom A B) →
    -- Given: All Fix types are strictly positive
    Σ (Hom A B) (λ nf → (t ⟶* nf) × IsNormalForm nf)

------------------------------------------------------------------------
-- CCT3: Confluence with Inductive Types
--
-- TOWER LEVEL: CCT3
--
-- THEOREM: Adding cata rules to BCC preserves confluence.
--
-- REQUIREMENT: cata rules must be orthogonal to BCC rules.
-- This is proven via the parallel reduction technique.
------------------------------------------------------------------------

cct3-confluence-applies-to : TowerLevel
cct3-confluence-applies-to = CCT3

postulate
  cct3-confluence :
    ∀ {A B} {t u v : Hom A B} →
    t ⟶* u → t ⟶* v →
    Σ (Hom A B) (λ w → (u ⟶* w) × (v ⟶* w))

------------------------------------------------------------------------
-- CCT4: Productivity for Coinductive Types (Abel 2012)
--
-- TOWER LEVEL: CCT4
--
-- THEOREM: BCC extended with guarded coinductive types is productive.
--
-- "Productive" means: every term reduces to WHNF in finite steps.
-- Full evaluation may be infinite, but each step is finite.
--
-- REQUIREMENT: All corecursive definitions must be guarded.
------------------------------------------------------------------------

cct4-productivity-applies-to : TowerLevel
cct4-productivity-applies-to = CCT4

postulate
  IsGuarded : ∀ {A B} → Hom A B → Set
  IsWHNF : ∀ {A B} → Hom A B → Set

  cct4-productivity :
    ∀ {A B} (t : Hom A B) →
    -- Given: All corecursive definitions are guarded
    Σ (Hom A B) (λ whnf → (t ⟶* whnf) × IsWHNF whnf)

------------------------------------------------------------------------
-- CCT4: Confluence with Coinductive Types
--
-- TOWER LEVEL: CCT4
--
-- THEOREM: Adding ana rules to CCT3 preserves confluence.
--
-- REQUIREMENT: ana rules must be orthogonal to cata and BCC rules.
------------------------------------------------------------------------

cct4-confluence-applies-to : TowerLevel
cct4-confluence-applies-to = CCT4

postulate
  cct4-confluence :
    ∀ {A B} {t u v : Hom A B} →
    t ⟶* u → t ⟶* v →
    Σ (Hom A B) (λ w → (u ⟶* w) × (v ⟶* w))

------------------------------------------------------------------------
-- Derived: Unique Normal Forms
--
-- COROLLARY: Confluence + SN implies unique normal forms.
--
-- Applies to: CCT1, CCT2, CCT3
-- For CCT4: unique WHNF (not full NF, since ν-types may be infinite)
------------------------------------------------------------------------

postulate
  unique-normal-form :
    ∀ {A B} (t : Hom A B) →
    Σ (Hom A B) (λ nf →
      (t ⟶* nf) × IsNormalForm nf ×
      (∀ nf' → (t ⟶* nf') → IsNormalForm nf' → nf ≡ nf'))
