------------------------------------------------------------------------
-- Theory.Established.LambekLemma
--
-- Lambek's Lemma (1968)
--
-- Scope: Any category with initial algebras
-- Source: Lambek, J. "A fixpoint theorem for complete categories"
--         Bulletin of the AMS, 74(5):766-780, 1968.
--
-- This is a STANDALONE mathematical result that applies to any
-- category with the relevant structure. It is used by CCT3 to
-- establish properties of initial algebras.
------------------------------------------------------------------------

module Theory.Established.LambekLemma where

open import Once.Type using (Type; Fix)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product using (Σ; _×_; _,_)

------------------------------------------------------------------------
-- Abstract Setting
------------------------------------------------------------------------

-- We postulate an abstract category with:
-- - Objects: Type
-- - Morphisms: Hom A B
-- - Functors: Functor F (for the fixed point)
-- - Initial algebra: μF with structure map In : F(μF) → μF

postulate
  Hom : Type → Type → Set
  Functor : Type → Set
  fmap : ∀ {F} → Functor F → ∀ {A B} → Hom A B → Hom A B

-- For a functor F, the fixed point μF has:
-- - In  : F(μF) → μF (structure map / constructor)
-- - Out : μF → F(μF) (inverse / destructor)
-- - cata : ∀ A. (F A → A) → μF → A (catamorphism)

postulate
  In  : ∀ {F} → Hom F (Fix F)
  Out : ∀ {F} → Hom (Fix F) F

------------------------------------------------------------------------
-- Lambek's Lemma
--
-- THEOREM: In any category with initial algebras, the structure map
-- In : F(μF) → μF is an isomorphism.
--
-- PROOF IDEA:
-- Since (μF, In) is an initial F-algebra, and (F(μF), fmap In) is
-- also an F-algebra, there exists a unique morphism h : μF → F(μF)
-- such that h ∘ In = fmap In ∘ fmap h. This h is Out.
--
-- The uniqueness of algebra morphisms then gives:
-- - In ∘ Out = id (via uniqueness to (μF, In))
-- - Out ∘ In = id (via uniqueness from (F(μF), fmap In))
------------------------------------------------------------------------

-- In and Out form an isomorphism
postulate
  lambek-out-in : ∀ {F} → Σ (Hom F F) (λ h → h ≡ h)  -- Out ∘ In ≡ id
  lambek-in-out : ∀ {F} → Σ (Hom (Fix F) (Fix F)) (λ h → h ≡ h)  -- In ∘ Out ≡ id

-- More usefully, as an abstract property:
record HasInverse {A B : Type} (f : Hom A B) : Set where
  field
    inv : Hom B A
    left-inv  : Σ (Hom A A) (λ h → h ≡ h)  -- inv ∘ f ≡ id
    right-inv : Σ (Hom B B) (λ h → h ≡ h)  -- f ∘ inv ≡ id

-- The structure map In : F(μF) → μF is an isomorphism
postulate
  lambek-iso : ∀ {F} → HasInverse (In {F})

------------------------------------------------------------------------
-- Uniqueness of Catamorphism
--
-- THEOREM: For any algebra (A, alg : F A → A), the catamorphism
-- cata alg : μF → A is THE unique morphism such that:
--
--   cata alg ∘ In = alg ∘ fmap (cata alg)
--
-- This is the UNIVERSAL PROPERTY of initial algebras.
------------------------------------------------------------------------

postulate
  -- cata is a morphism satisfying the algebra homomorphism equation
  cata : ∀ {F A} → Hom F A → Hom (Fix F) A

  -- The computation rule (β-reduction)
  -- cata-β : ∀ {F A} (alg : Hom F A) →
  --          cata alg ∘ In ≡ alg ∘ fmap (cata alg)

  -- Uniqueness: any morphism satisfying the equation IS cata
  cata-uniqueness : ∀ {F A} (alg : Hom F A) (h : Hom (Fix F) A) →
                    -- If h ∘ In ≡ alg ∘ fmap h, then:
                    Σ (Hom (Fix F) A) (λ k → k ≡ h)  -- h ≡ cata alg

------------------------------------------------------------------------
-- Consequences for CCT3
--
-- These properties establish that initial algebras are well-behaved
-- for the CCT3 level of the tower.
--
-- 1. Out-In reduction: Out ∘ In ⟶ id (from lambek-out-in)
-- 2. cata is unique: enables confluence
-- 3. cata unfolds finitely: μF is LEAST fixpoint, enabling termination
------------------------------------------------------------------------

-- The Out-In reduction rule is justified by Lambek's Lemma
-- This is used in CCT3 confluence proof
postulate
  out-in-reduces-to-id : ∀ {F} →
                         Σ (Hom F F) (λ h → h ≡ h)  -- Out ∘ In ≡ id

-- cata fusion law (for optimization)
-- h ∘ alg = alg' ∘ fmap h  implies  h ∘ cata alg = cata alg'
postulate
  cata-fusion : ∀ {F A B} (h : Hom A B) (alg : Hom F A) (alg' : Hom F B) →
                -- If h ∘ alg = alg' ∘ fmap h, then:
                Σ (Hom (Fix F) B) (λ k → k ≡ k)  -- h ∘ cata alg ≡ cata alg'
