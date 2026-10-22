------------------------------------------------------------------------
-- Once.Functor.Translate — the laws of reading a functor code as a set
-- functor (`Once.Internal.FunctorMeaning`), and the irrelevance of the
-- well-formedness witnesses.
--
-- Translation from syntactic Functor (with Type) to semantic SFunctor (with Set).
--
-- This module provides the bridge between:
--   - Once.Internal.Type.Functor (K takes Type)
--   - Once.Internal.Polynomial.SFunctor (K takes Set)
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

open import Once.Spec.Grade
open import Once.Type.Grade
open import Once.Internal.Type
open import Once.Spec.Type using (Ty; Fun; Type; Unit; Void; _*_; _+_; _⇒[_]_; Int; Float; K; Id; _⊕_; _⊗_)
open import Once.Internal.Type.Poly
open import Once.Type
open import Once.Internal.Polynomial
open import Once.Semantics.Functor
open import Once.Internal.Type.WellFormed
open import Once.Spec.Type using (KCtx; Base; WFFun; b-var; b-Unit; b-Void; b-Int; b-Float; b-*; b-+; wf-K; wf-Id; wf-⊕; wf-⊗)
open import Once.Internal.FunctorMeaning
-- | Translation preserves interpretation
translate-coherence : ∀ {m} IntRep FloatRep (F : Fun m) X → ⟦ translateF IntRep FloatRep F ⟧SF X ≡ ⟦ IntRep , FloatRep ⟧F-base F X
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

-- | A base type's witness is proof-irrelevant, over type variables of any kinds.
Base-irrelevant : ∀ {m} {Δ : KCtx m} {A} (b₁ b₂ : Base Δ A) → b₁ ≡ b₂
Base-irrelevant (b-var e) (b-var e′) = cong b-var (uip e e′)
  where
    uip : ∀ {A : Set} {x y : A} (p q : x ≡ y) → p ≡ q
    uip refl refl = refl
Base-irrelevant b-Unit b-Unit = refl
Base-irrelevant b-Void b-Void = refl
Base-irrelevant b-Int b-Int = refl
Base-irrelevant b-Float b-Float = refl
Base-irrelevant (b-* a b) (b-* a′ b′) = cong₂ b-* (Base-irrelevant a a′) (Base-irrelevant b b′)
Base-irrelevant (b-+ a b) (b-+ a′ b′) = cong₂ b-+ (Base-irrelevant a a′) (Base-irrelevant b b′)

-- | IsConcrete is proof-irrelevant
--
-- At an arrow type only `con-fun` is inhabited (an arrow is not a base type,
-- so `con-base` would need `IsBaseType (A ⇒[ k ] B)`, which is empty); at any
-- other type only `con-base`. Hence the mixed cases are absurd.
IsConcrete-irrelevant : ∀ {A} (c₁ c₂ : IsConcrete A) → c₁ ≡ c₂
IsConcrete-irrelevant (con-base ib₁) (con-base ib₂) =
  cong con-base (Base-irrelevant ib₁ ib₂)
IsConcrete-irrelevant (con-fun bA₁ cB₁) (con-fun bA₂ cB₂) =
  cong₂ (λ b c → con-fun b c) (Base-irrelevant bA₁ bA₂) (Base-irrelevant cB₁ cB₂)
IsConcrete-irrelevant (con-base ()) (con-fun bA cB)
IsConcrete-irrelevant (con-fun bA cB) (con-base ())

-- | A functor's well-formedness is proof-irrelevant, over any kinds.
WFFun-irrelevant : ∀ {m} {Δ : KCtx m} {F} (w₁ w₂ : WFFun Δ F) → w₁ ≡ w₂
WFFun-irrelevant (wf-K a) (wf-K a′) = cong wf-K (Base-irrelevant a a′)
WFFun-irrelevant wf-Id wf-Id = refl
WFFun-irrelevant (wf-⊕ f g) (wf-⊕ f′ g′) = cong₂ wf-⊕ (WFFun-irrelevant f f′) (WFFun-irrelevant g g′)
WFFun-irrelevant (wf-⊗ f g) (wf-⊗ f′ g′) = cong₂ wf-⊗ (WFFun-irrelevant f f′) (WFFun-irrelevant g g′)

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
