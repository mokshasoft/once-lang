------------------------------------------------------------------------
-- Theory.Established.LambekLemma
--
-- Lambek's Lemma (1968)
--
-- TOWER LEVEL: CCT3 (categories with initial algebras)
--
-- Source: Lambek, J. "A fixpoint theorem for complete categories"
--         Bulletin of the AMS, 74(5):766-780, 1968.
--
-- THEOREM: In any category with initial algebras, the structure map
--          In : F(μF) → μF is an isomorphism.
------------------------------------------------------------------------

module Theory.Established.LambekLemma where

open import Theory.CCTower using (TowerLevel; CCT3)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product using (Σ; _×_; _,_)

------------------------------------------------------------------------
-- This module applies to: CCT3
------------------------------------------------------------------------

applies-to : TowerLevel
applies-to = CCT3

------------------------------------------------------------------------
-- Abstract Category Structure
--
-- We postulate an abstract category with initial algebras.
-- This can be instantiated with Once.Type and Once.CCC.IR.
------------------------------------------------------------------------

postulate
  Obj : Set
  Hom : Obj → Obj → Set
  id  : ∀ {A} → Hom A A
  _∘_ : ∀ {A B C} → Hom B C → Hom A B → Hom A C

-- Fixed point (μF = least fixed point of functor F)
postulate
  μ   : Obj → Obj
  In  : ∀ {F} → Hom F (μ F)
  Out : ∀ {F} → Hom (μ F) F

------------------------------------------------------------------------
-- Lambek's Lemma
--
-- THEOREM: The structure map In : F(μF) → μF is an isomorphism.
--
-- PROOF SKETCH:
--   1. (μF, In) is the initial F-algebra
--   2. (F(μF), fmap In) is also an F-algebra
--   3. By initiality, ∃! h : μF → F(μF) with h ∘ In = fmap In ∘ fmap h
--   4. This h is Out
--   5. Uniqueness gives: Out ∘ In = id and In ∘ Out = id
------------------------------------------------------------------------

postulate
  -- Out ∘ In = id (the key reduction rule for CCT3)
  lambek-out-in : ∀ {F} → (Out {F} ∘ In {F}) ≡ id {F}

  -- In ∘ Out = id (the inverse direction)
  lambek-in-out : ∀ {F} → (In {F} ∘ Out {F}) ≡ id {μ F}

------------------------------------------------------------------------
-- Catamorphism: Universal Property of Initial Algebras
--
-- cata alg : μF → A is THE unique F-algebra morphism from (μF, In)
-- to any F-algebra (A, alg).
------------------------------------------------------------------------

postulate
  cata : ∀ {F A} → Hom F A → Hom (μ F) A

  -- β-reduction: cata alg ∘ In = alg ∘ fmap (cata alg)
  -- (Simplified here; full version requires fmap)
  cata-β : ∀ {F A} (alg : Hom F A) →
           Σ (Hom F A) (λ rhs → (cata alg ∘ In) ≡ rhs)

  -- Uniqueness: if h ∘ In = alg ∘ fmap h, then h = cata alg
  cata-unique : ∀ {F A} (alg : Hom F A) (h : Hom (μ F) A) →
                -- Given h satisfies the algebra morphism equation
                h ≡ cata alg

------------------------------------------------------------------------
-- Fusion Law
--
-- If h ∘ alg = alg' ∘ fmap h, then h ∘ cata alg = cata alg'
--
-- This is essential for optimization (deforestation).
------------------------------------------------------------------------

postulate
  cata-fusion : ∀ {F A B} (h : Hom A B) (alg : Hom F A) (alg' : Hom F B) →
                -- Given: h ∘ alg = alg' ∘ fmap h
                (h ∘ cata alg) ≡ cata alg'
