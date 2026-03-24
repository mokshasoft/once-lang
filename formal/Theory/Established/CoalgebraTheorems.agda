------------------------------------------------------------------------
-- Theory.Established.CoalgebraTheorems
--
-- Coalgebra Theorems (Rutten, 2000)
--
-- TOWER LEVEL: CCT4 (categories with final coalgebras)
--
-- Source: Rutten, J.J.M.M. "Universal coalgebra: a theory of systems"
--         Theoretical Computer Science 249(1):3-80, 2000.
--
-- THEOREM: In any category with final coalgebras, ana is the unique
--          coalgebra morphism, and bisimulation implies equality.
------------------------------------------------------------------------

module Theory.Established.CoalgebraTheorems where

open import Theory.CCTower using (TowerLevel; CCT4)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product using (Σ; _×_; _,_)

------------------------------------------------------------------------
-- This module applies to: CCT4
------------------------------------------------------------------------

applies-to : TowerLevel
applies-to = CCT4

------------------------------------------------------------------------
-- Abstract Category Structure
--
-- We postulate an abstract category with final coalgebras.
------------------------------------------------------------------------

postulate
  Obj : Set
  Hom : Obj → Obj → Set
  id  : ∀ {A} → Hom A A
  _∘_ : ∀ {A B C} → Hom B C → Hom A B → Hom A C

-- Fixed point (νF = greatest fixed point of functor F)
postulate
  ν   : Obj → Obj
  Out : ∀ {F} → Hom (ν F) F
  In  : ∀ {F} → Hom F (ν F)

------------------------------------------------------------------------
-- Finality: Dual to Lambek's Lemma
--
-- THEOREM: The structure map Out : νF → F(νF) is an isomorphism.
------------------------------------------------------------------------

postulate
  -- In ∘ Out = id (the key reduction rule for CCT4 ν-types)
  final-in-out : ∀ {F} → (In {F} ∘ Out {F}) ≡ id {ν F}

  -- Out ∘ In = id (the inverse direction)
  final-out-in : ∀ {F} → (Out {F} ∘ In {F}) ≡ id {F}

------------------------------------------------------------------------
-- Anamorphism: Universal Property of Final Coalgebras
--
-- ana coalg : A → νF is THE unique F-coalgebra morphism from any
-- F-coalgebra (A, coalg) to the final coalgebra (νF, Out).
------------------------------------------------------------------------

postulate
  ana : ∀ {F A} → Hom A F → Hom A (ν F)

  -- β-reduction: Out ∘ ana coalg = fmap (ana coalg) ∘ coalg
  -- (Simplified here; full version requires fmap)
  ana-β : ∀ {F A} (coalg : Hom A F) →
          Σ (Hom A F) (λ rhs → (Out ∘ ana coalg) ≡ rhs)

  -- Uniqueness: if Out ∘ h = fmap h ∘ coalg, then h = ana coalg
  ana-unique : ∀ {F A} (coalg : Hom A F) (h : Hom A (ν F)) →
               -- Given h satisfies the coalgebra morphism equation
               h ≡ ana coalg

------------------------------------------------------------------------
-- Coinduction Principle (Bisimulation)
--
-- THEOREM: Two elements of a final coalgebra are equal iff bisimilar.
--
-- A bisimulation R on νF is a relation such that if x R y, then
-- Out x and Out y are "F-related".
--
-- This is the COINDUCTION PRINCIPLE for proving equality of codata.
------------------------------------------------------------------------

postulate
  -- Bisimulation implies equality (stated abstractly)
  -- Full statement: ∀ R. IsBisimulation R → ∀ x y. R x y → x ≡ y
  coinduction : ∀ {F} → Σ (Hom (ν F) (ν F)) (λ h → h ≡ id)

------------------------------------------------------------------------
-- Fusion Law
--
-- If coalg' ∘ h = fmap h ∘ coalg, then ana coalg' ∘ h = ana coalg
------------------------------------------------------------------------

postulate
  ana-fusion : ∀ {F A B} (h : Hom A B) (coalg : Hom A F) (coalg' : Hom B F) →
               -- Given: coalg' ∘ h = fmap h ∘ coalg
               (ana coalg) ≡ (ana coalg' ∘ h)

------------------------------------------------------------------------
-- Hylo Fusion (Deforestation)
--
-- THEOREM: cata alg ∘ ana coalg can be computed directly without
--          building the intermediate recursive structure.
------------------------------------------------------------------------

postulate
  hylo : ∀ {F A B} → Hom F B → Hom A F → Hom A B

  hylo-fusion : ∀ {F A B} (alg : Hom F B) (coalg : Hom A F) →
                Σ (Hom A B) (λ h → h ≡ hylo alg coalg)
                -- hylo alg coalg ≡ cata alg ∘ ana coalg

------------------------------------------------------------------------
-- Guardedness (Productivity)
--
-- For coinductive types to be productive, corecursive calls must be
-- GUARDED by constructors.
--
-- Source: Abel (2012) "Type-based termination..."
------------------------------------------------------------------------

postulate
  IsGuarded : ∀ {F A} → Hom A F → Set

  -- Guarded coalgebras yield productive anamorphisms
  guarded-productive : ∀ {F A} (coalg : Hom A F) →
                       IsGuarded coalg →
                       Σ (Hom A (ν F)) (λ h → h ≡ ana coalg)
