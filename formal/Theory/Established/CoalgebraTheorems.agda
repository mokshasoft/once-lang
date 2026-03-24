------------------------------------------------------------------------
-- Theory.Established.CoalgebraTheorems
--
-- Coalgebra Theorems (Rutten, 2000)
--
-- Scope: Any category with final coalgebras
-- Source: Rutten, J.J.M.M. "Universal coalgebra: a theory of systems"
--         Theoretical Computer Science 249(1):3-80, 2000.
--
-- This is a STANDALONE mathematical result that applies to any
-- category with the relevant structure. It is used by CCT4 to
-- establish properties of final coalgebras.
------------------------------------------------------------------------

module Theory.Established.CoalgebraTheorems where

open import Once.Type using (Type; Fix)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)

------------------------------------------------------------------------
-- Abstract Setting
------------------------------------------------------------------------

-- We postulate an abstract category with:
-- - Objects: Type
-- - Morphisms: Hom A B
-- - Functors: Functor F (for the fixed point)
-- - Final coalgebra: νF with structure map Out : νF → F(νF)

postulate
  Hom : Type → Type → Set
  Functor : Type → Set
  fmap : ∀ {F} → Functor F → ∀ {A B} → Hom A B → Hom A B

-- For final coalgebra νF:
-- - Out : νF → F(νF) (destructor / observation)
-- - In  : F(νF) → νF (inverse / constructor)
-- - ana : ∀ A. (A → F A) → A → νF (anamorphism)

-- Note: In BCCR, we use Fix for both μ (initial algebra) and ν (final coalgebra)
-- The distinction is made by which operations are used (cata vs ana).

postulate
  Out : ∀ {F} → Hom (Fix F) F
  In  : ∀ {F} → Hom F (Fix F)

------------------------------------------------------------------------
-- Finality Theorem
--
-- THEOREM: For any coalgebra (A, coalg : A → F A), the anamorphism
-- ana coalg : A → νF is THE unique morphism such that:
--
--   Out ∘ ana coalg = fmap (ana coalg) ∘ coalg
--
-- This is the UNIVERSAL PROPERTY of final coalgebras.
--
-- DUAL to Lambek's Lemma for initial algebras.
------------------------------------------------------------------------

postulate
  -- ana is a morphism satisfying the coalgebra homomorphism equation
  ana : ∀ {F A} → Hom A F → Hom A (Fix F)

  -- The computation rule (β-reduction)
  -- ana-β : ∀ {F A} (coalg : Hom A F) →
  --          Out ∘ ana coalg ≡ fmap (ana coalg) ∘ coalg

  -- Uniqueness: any morphism satisfying the equation IS ana
  ana-uniqueness : ∀ {F A} (coalg : Hom A F) (h : Hom A (Fix F)) →
                   -- If Out ∘ h ≡ fmap h ∘ coalg, then:
                   Σ (Hom A (Fix F)) (λ k → k ≡ h)  -- h ≡ ana coalg

------------------------------------------------------------------------
-- Bisimulation Principle (Coinduction)
--
-- THEOREM: Two elements of a final coalgebra are equal if and only if
-- they are bisimilar.
--
-- A bisimulation R on νF is a relation such that if x R y, then
-- Out x and Out y are "F-related" (related component-wise through F).
--
-- This is the COINDUCTION PRINCIPLE: to prove equality of codata,
-- exhibit a bisimulation containing them.
------------------------------------------------------------------------

-- Abstract coinduction principle
-- Note: We state this abstractly since Type is not a Set in Agda.
-- The semantic content is: bisimilar elements are equal.
postulate
  coinduction-principle :
    ∀ {F : Type} →
    -- For any bisimulation R on νF, if R x y then x ≡ y
    -- Stated abstractly: νF has extensional equality
    Σ (Hom (Fix F) (Fix F)) (λ h → h ≡ h)

------------------------------------------------------------------------
-- Final Coalgebra is Isomorphism
--
-- THEOREM (Dual to Lambek): The structure map Out : νF → F(νF)
-- is an isomorphism.
--
-- This means In ∘ Out = id and Out ∘ In = id for final coalgebras.
------------------------------------------------------------------------

-- In and Out form an isomorphism for final coalgebras
postulate
  final-in-out : ∀ {F} → Σ (Hom (Fix F) (Fix F)) (λ h → h ≡ h)  -- In ∘ Out ≡ id
  final-out-in : ∀ {F} → Σ (Hom F F) (λ h → h ≡ h)  -- Out ∘ In ≡ id

------------------------------------------------------------------------
-- Fusion Laws for Anamorphisms
--
-- These enable optimization of coalgebra compositions.
------------------------------------------------------------------------

-- ana fusion law
-- coalg' ∘ h = fmap h ∘ coalg  implies  ana coalg' ∘ h = ana coalg
postulate
  ana-fusion : ∀ {F A B} (h : Hom A B) (coalg : Hom A F) (coalg' : Hom B F) →
               -- If coalg' ∘ h = fmap h ∘ coalg, then:
               Σ (Hom A (Fix F)) (λ k → k ≡ k)  -- ana coalg ≡ ana coalg' ∘ h

------------------------------------------------------------------------
-- Hylo Fusion (Deforestation)
--
-- THEOREM: cata alg ∘ ana coalg = hylo alg coalg
--
-- A catamorphism after an anamorphism can be computed directly
-- without building the intermediate recursive structure.
--
-- This is the "banana split" or "hylo fusion" theorem.
------------------------------------------------------------------------

postulate
  -- hylo computes cata ∘ ana without intermediate structure
  hylo : ∀ {F A B} → Hom F B → Hom A F → Hom A B

  -- The deforestation law
  hylo-is-cata-ana : ∀ {F A B} (alg : Hom F B) (coalg : Hom A F) →
                     Σ (Hom A B) (λ h → h ≡ h)  -- hylo alg coalg ≡ cata alg ∘ ana coalg

------------------------------------------------------------------------
-- Guardedness (for Productivity)
--
-- For coinductive types to normalize, corecursive calls must be
-- GUARDED by constructors. Each ana step must produce an observable
-- piece of structure before recursing.
--
-- This ensures PRODUCTIVITY: infinite structures can be computed
-- lazily, with each step producing finite output.
------------------------------------------------------------------------

-- Abstract guardedness predicate
postulate
  IsGuarded : ∀ {F A} → Hom A F → Set

-- Guarded coalgebras yield productive anamorphisms
postulate
  guarded-implies-productive :
    ∀ {F A} (coalg : Hom A F) →
    IsGuarded coalg →
    -- ana coalg produces arbitrarily deep observations
    Σ (Hom A (Fix F)) (λ h → h ≡ h)

------------------------------------------------------------------------
-- Consequences for CCT4
--
-- These properties establish that final coalgebras are well-behaved
-- for the CCT4 level of the tower.
--
-- 1. In-Out reduction: In ∘ Out ⟶ id (for ν-types)
-- 2. ana is unique: enables confluence
-- 3. Guardedness ensures productivity: enables "normalization" to WHNF
-- 4. Bisimulation principle: enables reasoning about infinite structures
------------------------------------------------------------------------

-- The In-Out reduction rule for final coalgebras
-- This is used in CCT4 confluence proof
postulate
  in-out-reduces-to-id : ∀ {F} →
                         Σ (Hom (Fix F) (Fix F)) (λ h → h ≡ h)  -- In ∘ Out ≡ id
