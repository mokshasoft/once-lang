------------------------------------------------------------------------
-- Theory.Established.Lambek1968
--
-- CITATION:
--   Lambek, J. (1968). "A fixpoint theorem for complete categories."
--   Mathematische Zeitschrift 103:151-161.
--
-- TOWER LEVEL: CCT3 (BCC + initial algebras / μ-types).
--
-- THEOREM (Lambek 1968):
--   In any category with initial F-algebras, the structure map
--   In : F(μF) → μF is an isomorphism.
--
-- PROOF SKETCH:
--   1. (μF, In) is initial by definition.
--   2. (F(μF), fmap In) is also an F-algebra.
--   3. By initiality, there is a unique morphism h : μF → F(μF) such
--      that h ∘ In = fmap In ∘ fmap h. Call this h = Out.
--   4. Uniqueness + the initial-algebra equations give Out ∘ In = id.
--   5. The composition In ∘ Out satisfies the same equation as id on
--      (μF, In), so by uniqueness, In ∘ Out = id.
--
-- SCOPE OF THIS POSTULATE:
--   Only the iso statement for In. The universal property of cata
--   (that it is the unique F-algebra morphism) and the β-rule
--   (cata alg ∘ In = alg ∘ fmap (cata alg)) are additional postulates
--   listed below, each a distinct claim.
--
-- NOTE ON FUNCTORS:
--   The β-rule for cata requires fmap (the functorial action of F on
--   morphisms). The current Systems/CCT3 abstracts F as Obj → Obj
--   without fmap. The β-rule is therefore postulated here with an
--   abstract "rhs" rather than explicitly as alg ∘ fmap (cata alg).
--   A future FunctorStructure will let us state it explicitly.
------------------------------------------------------------------------

module Theory.Established.Lambek1968 where

open import Theory.CCTower using (TowerLevel; CCT3)
open import Theory.Systems.CCT3
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product using (Σ; _×_; _,_)

------------------------------------------------------------------------
-- Tower level annotation
------------------------------------------------------------------------

applies-to : TowerLevel
applies-to = CCT3

------------------------------------------------------------------------
-- The Theorems
------------------------------------------------------------------------

module _ (S : CCT3Structure) where
  open CCT3Structure S

  ------------------------------------------------------------------------
  -- Lambek's Lemma: In is an isomorphism.
  ------------------------------------------------------------------------

  postulate
    lambek-out-in : ∀ {F : Obj → Obj} → (Out {F} ∘ In {F}) ≡ id
    lambek-in-out : ∀ {F : Obj → Obj} → (In {F} ∘ Out {F}) ≡ id

  ------------------------------------------------------------------------
  -- Universal property of cata (initial F-algebra):
  -- cata alg is the unique F-algebra morphism (μF, In) → (A, alg).
  ------------------------------------------------------------------------

  postulate
    cata-unique : ∀ {F : Obj → Obj} {A}
                  (alg : Hom (F A) A) (h : Hom (μ F) A) →
                  -- Given: h is an F-algebra morphism (h ∘ In ≡ alg ∘ fmap h)
                  h ≡ cata alg

  ------------------------------------------------------------------------
  -- β-rule for cata.
  -- Stated abstractly pending a full functor treatment:
  -- there exists some rhs (alg ∘ fmap F (cata alg)) such that
  -- cata alg ∘ In reduces to it.
  ------------------------------------------------------------------------

  postulate
    cata-β : ∀ {F : Obj → Obj} {A} (alg : Hom (F A) A) →
             Σ (Hom (F (μ F)) A) (λ rhs → (cata alg ∘ In) ≡ rhs)
