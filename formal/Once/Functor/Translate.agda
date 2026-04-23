------------------------------------------------------------------------
-- Once.Functor.Translate
--
-- Translation from syntactic Functor (with Type) to semantic SFunctor (with Set).
--
-- This module provides the bridge between:
--   - Once.Type.Functor (K takes Type)
--   - Once.Functor.Base.SFunctor (K takes Set)
--
-- The translation uses a base type interpretation that handles only
-- base types (Unit, Int, etc.), avoiding dependency on ⟦μ⟧.
--
-- OCP-0003 Phase 6: Enables proving μ-coherence by defining ⟦μ⟧ = μS ∘ translate.
------------------------------------------------------------------------

module Once.Functor.Translate where

open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Float using () renaming (Float to AgdaFloat)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Once.Type
open import Once.Functor.Base

------------------------------------------------------------------------
-- Base Type Interpretation
--
-- Interprets base types without depending on ⟦μ⟧.
-- For non-base types (functions, μ-type, ν-type), returns ⊤.
--
-- This is sufficient because practical polynomial functors only use
-- base types in K positions.
------------------------------------------------------------------------

-- | Base type interpretation (parameterized by Int representation)
--
-- Returns ⊤ for complex types (functions, recursive types).
-- This is safe because K positions in practical functors use base types.
--
⟦_⟧-base : Set → Type → Set
⟦ IntRep ⟧-base Unit = ⊤
⟦ IntRep ⟧-base Void = ⊥
⟦ IntRep ⟧-base (A * B) = ⟦ IntRep ⟧-base A × ⟦ IntRep ⟧-base B
⟦ IntRep ⟧-base (A + B) = ⟦ IntRep ⟧-base A ⊎ ⟦ IntRep ⟧-base B
⟦ IntRep ⟧-base (_ ⇒[ _ ] _) = ⊤  -- Functions (all kinds): return ⊤ (not used in K)
⟦ IntRep ⟧-base (μ-type _) = ⊤    -- Recursive: return ⊤ (not used in K)
⟦ IntRep ⟧-base (ν-type _) = ⊤    -- Corecursive: return ⊤ (not used in K)
⟦ IntRep ⟧-base Int = IntRep
⟦ IntRep ⟧-base Float = AgdaFloat
⟦ IntRep ⟧-base Str = String
⟦ IntRep ⟧-base Buffer = String
-- TVar removed from Type; now in PolyType (see Once.Type)

------------------------------------------------------------------------
-- Functor Translation
------------------------------------------------------------------------

-- | Translate syntactic Functor to semantic SFunctor
--
-- Uses the base interpretation for K positions.
--
translateF : Set → Functor → SFunctor
translateF IntRep (K A) = SK (⟦ IntRep ⟧-base A)
translateF IntRep Id = SId
translateF IntRep (F ⊕ G) = translateF IntRep F S⊕ translateF IntRep G
translateF IntRep (F ⊗ G) = translateF IntRep F S⊗ translateF IntRep G

------------------------------------------------------------------------
-- Semantic Fixed Points via Translation
--
-- These give us μ and ν without depending on the full ⟦_⟧.
------------------------------------------------------------------------

-- | Semantic μ via translation
--
-- μ-sem F = μS (translateF F)
--
μ-sem : Set → Functor → Set
μ-sem IntRep F = μS (translateF IntRep F)

-- | Semantic ν via translation
--
-- ν-sem F = νS (translateF F)
--
ν-sem : Set → Functor → Set
ν-sem IntRep F = νS (translateF IntRep F)

------------------------------------------------------------------------
-- Functor Interpretation Coherence
--
-- Show that the base interpretation applied to SFunctor equals
-- the original Functor interpretation (for well-formed functors).
------------------------------------------------------------------------

-- | Interpretation coherence for SFunctor
--
-- ⟦ translateF F ⟧SF X ≡ ⟦ F ⟧F-base X
-- (where ⟦_⟧F-base uses the base interpretation)
--
-- This is definitionally true by construction.
--
⟦_⟧F-base : Set → Functor → Set → Set
⟦ IntRep ⟧F-base (K A) X = ⟦ IntRep ⟧-base A
⟦ IntRep ⟧F-base Id X = X
⟦ IntRep ⟧F-base (F ⊕ G) X = ⟦ IntRep ⟧F-base F X ⊎ ⟦ IntRep ⟧F-base G X
⟦ IntRep ⟧F-base (F ⊗ G) X = ⟦ IntRep ⟧F-base F X × ⟦ IntRep ⟧F-base G X

-- | Translation preserves interpretation
translate-coherence : ∀ IntRep F X → ⟦ translateF IntRep F ⟧SF X ≡ ⟦ IntRep ⟧F-base F X
translate-coherence IntRep (K A) X = refl
translate-coherence IntRep Id X = refl
translate-coherence IntRep (F ⊕ G) X
  rewrite translate-coherence IntRep F X
        | translate-coherence IntRep G X = refl
translate-coherence IntRep (F ⊗ G) X
  rewrite translate-coherence IntRep F X
        | translate-coherence IntRep G X = refl

------------------------------------------------------------------------
-- Well-Formed Functors
--
-- A functor is well-formed if K positions only contain base types.
-- For well-formed functors, ⟦_⟧-base equals ⟦_⟧.
--
-- Note: Coherence proofs are in Once.Semantics.Coherence to avoid
-- circular imports (Core imports Translate, so Translate can't import Core).
------------------------------------------------------------------------

-- | Base type predicate
--
-- A type is a base type if it doesn't contain functions, μ-types, or ν-types.
--
data IsBaseType : Type → Set where
  base-Unit   : IsBaseType Unit
  base-Void   : IsBaseType Void
  base-Int    : IsBaseType Int
  base-Float  : IsBaseType Float
  base-Str    : IsBaseType Str
  base-Buffer : IsBaseType Buffer
  base-Prod   : ∀ {A B} → IsBaseType A → IsBaseType B → IsBaseType (A * B)
  base-Sum    : ∀ {A B} → IsBaseType A → IsBaseType B → IsBaseType (A + B)

-- | Well-formed functor predicate
--
-- K positions only contain base types.
--
data WellFormedF : Functor → Set where
  wf-K   : ∀ {A} → IsBaseType A → WellFormedF (K A)
  wf-Id  : WellFormedF Id
  wf-Sum : ∀ {F G} → WellFormedF F → WellFormedF G → WellFormedF (F ⊕ G)
  wf-Prod : ∀ {F G} → WellFormedF F → WellFormedF G → WellFormedF (F ⊗ G)

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
IsBaseType-irrelevant base-Str base-Str = refl
IsBaseType-irrelevant base-Buffer base-Buffer = refl
IsBaseType-irrelevant (base-Prod ibA₁ ibB₁) (base-Prod ibA₂ ibB₂) =
  cong₂ base-Prod (IsBaseType-irrelevant ibA₁ ibA₂) (IsBaseType-irrelevant ibB₁ ibB₂)
IsBaseType-irrelevant (base-Sum ibA₁ ibB₁) (base-Sum ibA₂ ibB₂) =
  cong₂ base-Sum (IsBaseType-irrelevant ibA₁ ibA₂) (IsBaseType-irrelevant ibB₁ ibB₂)

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
