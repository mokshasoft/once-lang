------------------------------------------------------------------------
-- Once.Functor.Translate — the laws of reading a functor code as a set
-- functor (`Once.Lang.FunctorMeaning`), and the irrelevance of the
-- well-formedness witnesses.
--
-- Translation from syntactic Functor (with Type) to semantic SFunctor (with Set).
--
-- This module provides the bridge between:
--   - Once.Lang.Type.Functor (K takes Type)
--   - Once.Lang.Polynomial.SFunctor (K takes Set)
--
-- The translation uses a base type interpretation that handles only
-- base types (Unit, Int, etc.), avoiding dependency on ⟦μ⟧.
--
-- OCP-0003 Phase 6: Enables proving μ-coherence by defining ⟦μ⟧ = μS ∘ translate.
------------------------------------------------------------------------

module Once.Functor.Translate where

open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Once.Lang.Type.Grade
open import Once.Lang.Type
open import Once.Lang.Type.Poly
open import Once.Type
open import Once.Lang.Polynomial
open import Once.Semantics.Functor
open import Once.Lang.Type.WellFormed
open import Once.Lang.FunctorMeaning
-- | Translation preserves interpretation
translate-coherence : ∀ IntRep FloatRep F X → ⟦ translateF IntRep FloatRep F ⟧SF X ≡ ⟦ IntRep , FloatRep ⟧F-base F X
translate-coherence IntRep FloatRep (K A) X = refl
translate-coherence IntRep FloatRep Id X = refl
translate-coherence IntRep FloatRep (F ⊕ G) X
  rewrite translate-coherence IntRep FloatRep F X
        | translate-coherence IntRep FloatRep G X = refl
translate-coherence IntRep FloatRep (F ⊗ G) X
  rewrite translate-coherence IntRep FloatRep F X
        | translate-coherence IntRep FloatRep G X = refl

------------------------------------------------------------------------
-- Proof Irrelevance for IsBaseType and WellFormedF
--
-- These proofs show that any two proofs of IsBaseType or WellFormedF
-- for the same type/functor are equal. This enables pattern matching
-- on validity proofs without worrying about which proof was used.
------------------------------------------------------------------------

-- | IsBaseType is proof-irrelevant
IsBaseType-irrelevant : ∀ {A} (ib₁ ib₂ : IsBaseType A) → ib₁ ≡ ib₂
IsBaseType-irrelevant base-Unit base-Unit = refl
IsBaseType-irrelevant base-Void base-Void = refl
IsBaseType-irrelevant base-Int base-Int = refl
IsBaseType-irrelevant base-Float base-Float = refl
IsBaseType-irrelevant (base-Prod ibA₁ ibB₁) (base-Prod ibA₂ ibB₂) =
  cong₂ base-Prod (IsBaseType-irrelevant ibA₁ ibA₂) (IsBaseType-irrelevant ibB₁ ibB₂)
IsBaseType-irrelevant (base-Sum ibA₁ ibB₁) (base-Sum ibA₂ ibB₂) =
  cong₂ base-Sum (IsBaseType-irrelevant ibA₁ ibA₂) (IsBaseType-irrelevant ibB₁ ibB₂)
IsBaseType-irrelevant base-rigid base-rigid = refl

-- | IsConcrete is proof-irrelevant
--
-- At an arrow type only `con-fun` is inhabited (an arrow is not a base type,
-- so `con-base` would need `IsBaseType (A ⇒[ k ] B)`, which is empty); at any
-- other type only `con-base`. Hence the mixed cases are absurd.
IsConcrete-irrelevant : ∀ {A} (c₁ c₂ : IsConcrete A) → c₁ ≡ c₂
IsConcrete-irrelevant (con-base ib₁) (con-base ib₂) =
  cong con-base (IsBaseType-irrelevant ib₁ ib₂)
IsConcrete-irrelevant (con-fun bA₁ cB₁) (con-fun bA₂ cB₂) =
  cong₂ (λ b c → con-fun b c) (IsBaseType-irrelevant bA₁ bA₂) (IsBaseType-irrelevant cB₁ cB₂)
IsConcrete-irrelevant (con-base ()) (con-fun bA cB)
IsConcrete-irrelevant (con-fun bA cB) (con-base ())

-- | WellFormedF is proof-irrelevant
WellFormedF-irrelevant : ∀ {F} (wf₁ wf₂ : WellFormedF F) → wf₁ ≡ wf₂
WellFormedF-irrelevant (wf-K ib₁) (wf-K ib₂) = cong wf-K (IsBaseType-irrelevant ib₁ ib₂)
WellFormedF-irrelevant wf-Id wf-Id = refl
WellFormedF-irrelevant (wf-Sum wfF₁ wfG₁) (wf-Sum wfF₂ wfG₂) =
  cong₂ wf-Sum (WellFormedF-irrelevant wfF₁ wfF₂) (WellFormedF-irrelevant wfG₁ wfG₂)
WellFormedF-irrelevant (wf-Prod wfF₁ wfG₁) (wf-Prod wfF₂ wfG₂) =
  cong₂ wf-Prod (WellFormedF-irrelevant wfF₁ wfF₂) (WellFormedF-irrelevant wfG₁ wfG₂)

------------------------------------------------------------------------
-- Standard Functor Codes
--
-- These show how common data types translate.
------------------------------------------------------------------------

-- | Natural numbers: Nat = μ (K Unit ⊕ Id)
-- translateF NatF = SK ⊤ S⊕ SId
-- μS (SK ⊤ S⊕ SId) ≅ ⊤ ⊎ μS (SK ⊤ S⊕ SId) ≅ Nat

-- | List A = μ (K Unit ⊕ (K A ⊗ Id))
-- For base type A, translateF (ListF A) = SK ⊤ S⊕ (SK (⟦A⟧-base) S⊗ SId)

-- | Well-formedness of standard functors
wf-NatF : WellFormedF NatF
wf-NatF = wf-Sum (wf-K base-Unit) wf-Id
