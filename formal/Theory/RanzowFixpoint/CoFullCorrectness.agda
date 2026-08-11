------------------------------------------------------------------------
-- Theory.RanzowFixpoint.CoFullCorrectness
--
-- The full "cofixpoint ⟹ correctness" theorem.
--
-- Coinductive sibling of Theory.RanzowFixpoint.FullCorrectness.
--
-- Whereas FullCorrectness handles cata-form normalizers in CCT3+,
-- this module handles ana-form productive corecursive transformations
-- in CCT4:
--
--   If T : CoCode → CoCode is productive, satisfies the coinductive
--   Ranzow Fixpoint property (T ∘ ⌜T⌝ω ≈ω ⌜T⌝ω), and agrees with an
--   intended cospec at its own co-encoding (cospec T ≡ T), then T
--   computes cospec on every co-encoded input:
--
--     ∀ g.  T ∘ ⌜g⌝ω  ≈ω  ⌜cospec g⌝ω
--
-- The deep mathematical content (cotransparency / productive
-- uniformity) is discharged into the Established postulate
-- Theory.Established.Cotransparency.productive-cofixpoint-implies-correctness.
-- This module is just a structured wrapper that exposes the theorem
-- in terms of HasCoFixpoint instead of the bare bisimilarity.
--
-- Its whole mathematical content is one Established postulate,
-- Cotransparency, re-exposed.
--
-- TOWER LEVEL: CCT4 (no CCT3 base — ν-types only exist at CCT4).
------------------------------------------------------------------------

module Theory.RanzowFixpoint.CoFullCorrectness where

open import Theory.CCTower using (TowerLevel; CCT4)
open import Theory.Systems.CCT4
open import Theory.Syntax.Coreducible using (Coreducible)
open import Theory.RanzowFixpoint.Coinductive
  using (CoEncodingScheme; HasCoFixpoint)
open import Theory.Encoding.Coinductive using (CoEncodingInductive)
import Theory.Established.Cotransparency as CoT
open import Relation.Binary.PropositionalEquality
  using (_≡_; sym; subst)

------------------------------------------------------------------------
-- Tower level annotation
------------------------------------------------------------------------

applies-to : TowerLevel
applies-to = CCT4

------------------------------------------------------------------------
-- The theorem, parameterized over:
--   S    : a CCT4 structure
--   CoR  : a Coreducible carrier on S
--   E    : a co-encoding scheme
--   CoEI : structural co-encoding laws (productive, faithful,
--          ana-decomposes)
------------------------------------------------------------------------

module _ (S    : CCT4Structure)
         (CoR  : Coreducible (CCT4Structure.Obj S) (CCT4Structure.Hom S))
         (E    : CoEncodingScheme S)
         (CoEI : CoEncodingInductive S CoR E)
         where
  open CCT4Structure S
  open Coreducible CoR
  open CoEncodingScheme E

  --------------------------------------------------------------------
  -- The main theorem.
  --
  --   cospec     : the intended interpretation (cospec g = what T
  --                should produce when applied to ⌜g⌝ω).
  --   T          : the candidate corecursive transformation.
  --   prod-T     : T is productive.
  --   cospec-T≡T : cospec agrees with T on T's own encoding.
  --                For the productive-corecursor case, this is
  --                automatic when T is productive (productive
  --                morphisms are fixed points of "evaluate to
  --                productive form" up to bisim).
  --   cf-T       : T satisfies the coinductive Ranzow Fixpoint.
  --
  -- Conclusion: T computes cospec on every co-encoded input.
  --------------------------------------------------------------------

  cofixpoint-implies-correctness :
    ∀ (cospec : ∀ {A B} → Hom A B → Hom A B)
      (T : Hom CoCode CoCode) →
      IsProductive T →
      cospec T ≡ T →
      HasCoFixpoint S CoR E T →
      ∀ {A B} (g : Hom A B) →
      (T ∘ co-encode g) ≈ω co-encode (cospec g)
  cofixpoint-implies-correctness cospec T prod-T cospec-T≡T cf-T =
    CoT.productive-cofixpoint-implies-correctness S CoR E CoEI cospec T prod-T
      (subst (λ x → (T ∘ co-encode T) ≈ω co-encode x) (sym cospec-T≡T) cf-T)

  --------------------------------------------------------------------
  -- Specialization: the "corecursor self-test" reading.
  --
  -- If T is intended as a productive corecursive transformation, then
  -- "cospec g" is the bisim-class of g's productive output. For T
  -- itself productive, cospec T ≈ T trivially, so the cospec-T≡T
  -- hypothesis reduces to a propositional-equality witness (typically
  -- refl when cospec is defined as identity-on-productive).
  --
  -- The remaining hypothesis is just the coinductive Ranzow Fixpoint
  -- — the bisimilarity-checkable test "run T on its own co-encoding
  -- and observe bisimilarity".
  --
  -- This is the dual OCP-4: a verified corecursor is one that reaches
  -- the coinductive Ranzow Fixpoint on its own co-encoding.
  --------------------------------------------------------------------
