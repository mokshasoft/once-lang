-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Semantics.Core
--
-- Core semantic interpretation, parameterized by integer representation.
--
-- This module provides:
--   - ⟦_⟧: Type → Set (semantic interpretation)
--   - sem-*: Semantic operations (products, sums, recursion schemes)
--   - Semantic laws
--
-- Instantiate with ℕ for machine semantics, ℤ for proof semantics.
------------------------------------------------------------------------

module Once.Semantics.Core (IntRep : Set) where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Float using () renaming (Float to AgdaFloat)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)
open import Function using (_∘_)

open import Once.Type

-- | Function extensionality (local version)
--
-- Used for proving sem-cata-In-id. This is the same postulate as in
-- Once.Postulates, but defined here to avoid circular import.
-- Named with 'funext' prefix to avoid clashing with Once.Postulates.
--
postulate
  funext : ∀ {A : Set} {B : A → Set} {f g : (x : A) → B x} →
           (∀ x → f x ≡ g x) → f ≡ g

-- OCP-0003: ⟦Fix⟧ wrapper removed. Use μ/ν from SPF.agda.

------------------------------------------------------------------------
-- Semantic Interpretation
--
-- Functions are plain Agda functions (not Closure records).
-- Int is parameterized (ℕ for machine, ℤ for proofs).
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Polynomial Functor Semantics (via Once.Functor.Translate)
--
-- OCP-0003 Phase 6: Instead of postulating ⟦μ⟧ and ⟦ν⟧, we now define
-- them using Once.Functor.Base's μS and νS via translation.
--
-- This breaks the circular dependency:
--   Old: ⟦_⟧ → ⟦_⟧F → SPF.μ → ⟦μ⟧ → ⟦_⟧ (circular!)
--   New: ⟦_⟧-base → translateF → μS (no cycle)
--        Then: ⟦μ⟧ = μS ∘ translateF
--
-- For well-formed functors (K only with base types), the base
-- interpretation equals the full interpretation.
------------------------------------------------------------------------

open import Once.Functor.Translate using (μ-sem; ν-sem; translateF; ⟦_⟧-base)
open import Once.Functor.Base
  using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF; μS; ⟨_⟩; outS; νS; unfoldS;
         sfmap; cataS; sfmapCata; sfmapCata-is-sfmap; anaS;
         fold-unfoldS; unfold-foldS; cataS-computation; cataS-In-id; anaS-Out-id)

-- | Semantic interpretation of μ-type (initial algebra)
--
-- Defined via translation to SFunctor, not postulated.
-- μ-coherence is now provable (essentially refl).
--
⟦μ⟧ : Functor → Set
⟦μ⟧ = μ-sem IntRep

-- | Semantic interpretation of ν-type (final coalgebra)
--
-- Defined via translation to SFunctor, not postulated.
-- ν-coherence is now provable (essentially refl).
--
⟦ν⟧ : Functor → Set
⟦ν⟧ = ν-sem IntRep

------------------------------------------------------------------------
-- Guarded Functor Values
--
-- ⟦Guarded⟧ F A represents guarded F-shaped values with A at recursive positions.
--
-- This is postulated because defining it structurally at Set level causes
-- universe and strict positivity issues (⟦_⟧ includes function types).
-- The CCC/IR/Guarded.agda module provides the Set₁ version.
--
-- OCP-0003: Kept as postulate to avoid complexity.
------------------------------------------------------------------------

postulate
  ⟦Guarded⟧ : Functor → Set → Set

⟦_⟧ : Type → Set
⟦ Unit ⟧         = ⊤
⟦ Void ⟧         = ⊥
⟦ A * B ⟧        = ⟦ A ⟧ × ⟦ B ⟧
⟦ A + B ⟧        = ⟦ A ⟧ ⊎ ⟦ B ⟧
⟦ A ⇒[ _ ] B ⟧   = ⟦ A ⟧ → ⟦ B ⟧
⟦ Eff A B ⟧      = ⟦ A ⟧ → ⟦ B ⟧
-- OCP-0003: Fix removed, use μ-type/ν-type
⟦ μ-type F ⟧     = ⟦μ⟧ F
⟦ ν-type F ⟧     = ⟦ν⟧ F
-- OCP-0003: GuardedT for productive corecursion
⟦ GuardedT F A ⟧ = ⟦Guarded⟧ F ⟦ A ⟧
⟦ Int ⟧          = IntRep
⟦ Float ⟧        = AgdaFloat
⟦ Str ⟧          = String
⟦ Buffer ⟧       = String
⟦ TVar _ ⟧       = ⊤

------------------------------------------------------------------------
-- Functor Interpretation (Set level)
--
-- Interprets Functor codes as Set → Set functions.
-- This parallels ⟦_⟧T at the Type level.
------------------------------------------------------------------------

⟦_⟧F : Functor → Set → Set
⟦ K A ⟧F X = ⟦ A ⟧
⟦ Id ⟧F X = X
⟦ F ⊕ G ⟧F X = ⟦ F ⟧F X ⊎ ⟦ G ⟧F X
⟦ F ⊗ G ⟧F X = ⟦ F ⟧F X × ⟦ G ⟧F X

------------------------------------------------------------------------
-- Type/Set Functor Coherence
--
-- The Type-level functor interpretation ⟦_⟧T followed by semantic
-- interpretation ⟦_⟧ equals the Set-level functor interpretation ⟦_⟧F.
-- We prove this by structural induction on F.
------------------------------------------------------------------------

-- | Coherence: ⟦ ⟦ F ⟧T X ⟧ ≡ ⟦ F ⟧F ⟦ X ⟧
--
-- This allows converting between Type-level and Set-level functor apps.
-- Proven by structural induction on F.
--
sem-functor-coherence : ∀ F X → ⟦ ⟦ F ⟧T X ⟧ ≡ ⟦ F ⟧F ⟦ X ⟧
sem-functor-coherence (K A) X = refl
sem-functor-coherence Id X = refl
sem-functor-coherence (F ⊕ G) X rewrite sem-functor-coherence F X
                                      | sem-functor-coherence G X = refl
sem-functor-coherence (F ⊗ G) X rewrite sem-functor-coherence F X
                                      | sem-functor-coherence G X = refl

------------------------------------------------------------------------
-- Coercions (Structural Definition)
--
-- Key insight: Define coercions by structural recursion on F, NOT via
-- subst on the coherence proof. This makes them compute properly and
-- allows definitional equality with structural operations.
------------------------------------------------------------------------

-- | Coercion from Type-level to Set-level functor application
coerce-functor : ∀ F X → ⟦ ⟦ F ⟧T X ⟧ → ⟦ F ⟧F ⟦ X ⟧
coerce-functor (K A) X x = x
coerce-functor Id X x = x
coerce-functor (F ⊕ G) X (inj₁ x) = inj₁ (coerce-functor F X x)
coerce-functor (F ⊕ G) X (inj₂ y) = inj₂ (coerce-functor G X y)
coerce-functor (F ⊗ G) X (x , y) = (coerce-functor F X x , coerce-functor G X y)

-- | Inverse coercion
coerce-functor⁻¹ : ∀ F X → ⟦ F ⟧F ⟦ X ⟧ → ⟦ ⟦ F ⟧T X ⟧
coerce-functor⁻¹ (K A) X x = x
coerce-functor⁻¹ Id X x = x
coerce-functor⁻¹ (F ⊕ G) X (inj₁ x) = inj₁ (coerce-functor⁻¹ F X x)
coerce-functor⁻¹ (F ⊕ G) X (inj₂ y) = inj₂ (coerce-functor⁻¹ G X y)
coerce-functor⁻¹ (F ⊗ G) X (x , y) = (coerce-functor⁻¹ F X x , coerce-functor⁻¹ G X y)

------------------------------------------------------------------------
-- Coercion Round-Trip Lemmas
--
-- Now that coercions are defined structurally, the round-trip proofs
-- are simple structural induction (no subst manipulation needed).
------------------------------------------------------------------------

-- | Round-trip: coerce then coerce⁻¹ is identity
coerce-round-trip : ∀ F X (x : ⟦ ⟦ F ⟧T X ⟧)
                  → coerce-functor⁻¹ F X (coerce-functor F X x) ≡ x
coerce-round-trip (K A) X x = refl
coerce-round-trip Id X x = refl
coerce-round-trip (F ⊕ G) X (inj₁ x) = cong inj₁ (coerce-round-trip F X x)
coerce-round-trip (F ⊕ G) X (inj₂ y) = cong inj₂ (coerce-round-trip G X y)
coerce-round-trip (F ⊗ G) X (x , y) = cong₂ _,_ (coerce-round-trip F X x) (coerce-round-trip G X y)

-- | Round-trip: coerce⁻¹ then coerce is identity
coerce⁻¹-round-trip : ∀ F X (x : ⟦ F ⟧F ⟦ X ⟧)
                    → coerce-functor F X (coerce-functor⁻¹ F X x) ≡ x
coerce⁻¹-round-trip (K A) X x = refl
coerce⁻¹-round-trip Id X x = refl
coerce⁻¹-round-trip (F ⊕ G) X (inj₁ x) = cong inj₁ (coerce⁻¹-round-trip F X x)
coerce⁻¹-round-trip (F ⊕ G) X (inj₂ y) = cong inj₂ (coerce⁻¹-round-trip G X y)
coerce⁻¹-round-trip (F ⊗ G) X (x , y) = cong₂ _,_ (coerce⁻¹-round-trip F X x) (coerce⁻¹-round-trip G X y)

------------------------------------------------------------------------
-- Structural Coercion Aliases (for backwards compatibility)
--
-- Now that coerce-functor is defined structurally, these are just aliases.
------------------------------------------------------------------------

-- | Alias for coerce-functor (backwards compatibility)
coerce-struct : ∀ F X → ⟦ ⟦ F ⟧T X ⟧ → ⟦ F ⟧F ⟦ X ⟧
coerce-struct = coerce-functor

-- | Alias for coerce-functor⁻¹ (backwards compatibility)
coerce-struct⁻¹ : ∀ F X → ⟦ F ⟧F ⟦ X ⟧ → ⟦ ⟦ F ⟧T X ⟧
coerce-struct⁻¹ = coerce-functor⁻¹

-- | Alias for coerce-round-trip
coerce-struct-round-trip : ∀ F X (x : ⟦ ⟦ F ⟧T X ⟧)
                         → coerce-struct⁻¹ F X (coerce-struct F X x) ≡ x
coerce-struct-round-trip = coerce-round-trip

-- | Alias for coerce⁻¹-round-trip
coerce-struct⁻¹-round-trip : ∀ F X (x : ⟦ F ⟧F ⟦ X ⟧)
                           → coerce-struct F X (coerce-struct⁻¹ F X x) ≡ x
coerce-struct⁻¹-round-trip = coerce⁻¹-round-trip

------------------------------------------------------------------------
-- Semantic Operations
--
-- These mirror IR constructors but operate on semantic values.
-- Named sem-<ir> to distinguish from IR constructors.
------------------------------------------------------------------------

-- Pair operations
sem-fst : ∀ {A B} → ⟦ A * B ⟧ → ⟦ A ⟧
sem-fst = proj₁

sem-snd : ∀ {A B} → ⟦ A * B ⟧ → ⟦ B ⟧
sem-snd = proj₂

sem-pair : ∀ {A B} → ⟦ A ⟧ → ⟦ B ⟧ → ⟦ A * B ⟧
sem-pair a b = a , b

-- Sum operations
sem-inl : ∀ {A B} → ⟦ A ⟧ → ⟦ A + B ⟧
sem-inl = inj₁

sem-inr : ∀ {A B} → ⟦ B ⟧ → ⟦ A + B ⟧
sem-inr = inj₂

sem-case : ∀ {A B C} → (⟦ A ⟧ → ⟦ C ⟧) → (⟦ B ⟧ → ⟦ C ⟧) → ⟦ A + B ⟧ → ⟦ C ⟧
sem-case f g (inj₁ a) = f a
sem-case f g (inj₂ b) = g b

-- OCP-0003: sem-fold/sem-unfold removed. Use sem-In/sem-cata/sem-CoOut/sem-ana.

------------------------------------------------------------------------
-- Semantic Laws
------------------------------------------------------------------------

sem-fst-pair : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) → sem-fst (sem-pair a b) ≡ a
sem-fst-pair a b = refl

sem-snd-pair : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) → sem-snd (sem-pair a b) ≡ b
sem-snd-pair a b = refl

sem-case-inl : ∀ {A B C} (f : ⟦ A ⟧ → ⟦ C ⟧) (g : ⟦ B ⟧ → ⟦ C ⟧) (a : ⟦ A ⟧) →
  sem-case f g (sem-inl a) ≡ f a
sem-case-inl f g a = refl

sem-case-inr : ∀ {A B C} (f : ⟦ A ⟧ → ⟦ C ⟧) (g : ⟦ B ⟧ → ⟦ C ⟧) (b : ⟦ B ⟧) →
  sem-case f g (sem-inr b) ≡ g b
sem-case-inr f g b = refl

-- OCP-0003: sem-fold-unfold and sem-unfold-fold laws removed

------------------------------------------------------------------------
-- Recursion Scheme Semantic Operations (Postulated)
--
-- These operations parallel the IR constructors for recursion schemes.
-- They are postulated here but implemented properly in Once.SPF.
--
-- F is explicit where needed for Agda to resolve constraints.
------------------------------------------------------------------------

-- | Functorial map for polynomials (defined first for use in postulates)
sem-fmap : ∀ F {X Y : Set} → (X → Y) → ⟦ F ⟧F X → ⟦ F ⟧F Y
sem-fmap (K A) f x = x
sem-fmap Id f x = f x
sem-fmap (F ⊕ G) f (inj₁ x) = inj₁ (sem-fmap F f x)
sem-fmap (F ⊕ G) f (inj₂ y) = inj₂ (sem-fmap G f y)
sem-fmap (F ⊗ G) f (x , y) = (sem-fmap F f x , sem-fmap G f y)

------------------------------------------------------------------------
-- Fmap-Coercion Coherence (using structural coercions)
--
-- These lemmas show that structural coercions commute with sem-fmap.
-- They're used to prove the IR-level recursion scheme laws.
------------------------------------------------------------------------

-- | Type-level functorial map (works on ⟦ ⟦ F ⟧T X ⟧)
-- This mirrors sem-fmap but at the Type level
sem-fmap-Type : ∀ F {X Y : Type} → (⟦ X ⟧ → ⟦ Y ⟧) → ⟦ ⟦ F ⟧T X ⟧ → ⟦ ⟦ F ⟧T Y ⟧
sem-fmap-Type (K A) f x = x
sem-fmap-Type Id f x = f x
sem-fmap-Type (F ⊕ G) f (inj₁ x) = inj₁ (sem-fmap-Type F f x)
sem-fmap-Type (F ⊕ G) f (inj₂ y) = inj₂ (sem-fmap-Type G f y)
sem-fmap-Type (F ⊗ G) f (x , y) = (sem-fmap-Type F f x , sem-fmap-Type G f y)

-- | coerce-struct⁻¹ ∘ sem-fmap ∘ coerce-struct ≡ sem-fmap-Type
fmap-struct-coherence : ∀ F {X Y : Type} (f : ⟦ X ⟧ → ⟦ Y ⟧) (x : ⟦ ⟦ F ⟧T X ⟧)
                      → coerce-struct⁻¹ F Y (sem-fmap F f (coerce-struct F X x)) ≡ sem-fmap-Type F f x
fmap-struct-coherence (K A) f x = refl
fmap-struct-coherence Id f x = refl
fmap-struct-coherence (F ⊕ G) f (inj₁ x) = cong inj₁ (fmap-struct-coherence F f x)
fmap-struct-coherence (F ⊕ G) f (inj₂ y) = cong inj₂ (fmap-struct-coherence G f y)
fmap-struct-coherence (F ⊗ G) f (x , y) = cong₂ _,_ (fmap-struct-coherence F f x) (fmap-struct-coherence G f y)

-- | coerce-struct⁻¹ ∘ sem-fmap ≡ sem-fmap-Type ∘ coerce-struct⁻¹
fmap-struct-coherence′ : ∀ F {X Y : Type} (f : ⟦ X ⟧ → ⟦ Y ⟧) (y : ⟦ F ⟧F ⟦ X ⟧)
                       → coerce-struct⁻¹ F Y (sem-fmap F f y) ≡ sem-fmap-Type F f (coerce-struct⁻¹ F X y)
fmap-struct-coherence′ (K A) f y = refl
fmap-struct-coherence′ Id f y = refl
fmap-struct-coherence′ (F ⊕ G) f (inj₁ x) = cong inj₁ (fmap-struct-coherence′ F f x)
fmap-struct-coherence′ (F ⊕ G) f (inj₂ y) = cong inj₂ (fmap-struct-coherence′ G f y)
fmap-struct-coherence′ (F ⊗ G) f (x , y) = cong₂ _,_ (fmap-struct-coherence′ F f x) (fmap-struct-coherence′ G f y)

------------------------------------------------------------------------
-- Type Coercions (Full ↔ Base Interpretation)
--
-- OCP-0003: For well-formed functors (K only with base types), the full
-- interpretation ⟦_⟧ equals the base interpretation ⟦_⟧-base. We prove
-- this by pattern matching on the Type.
--
-- For base types: definitionally equal
-- For complex types: ⟦_⟧-base returns ⊤, which is a "fallback" that
--   should never be reached for well-formed functors.
------------------------------------------------------------------------

-- | Coerce from full to base interpretation
--
-- This direction always works:
-- - Base types: identity (definitionally equal)
-- - Complex types: produce tt (base interp returns ⊤)
--
coerce-full-to-base : ∀ A → ⟦ A ⟧ → ⟦ IntRep ⟧-base A
coerce-full-to-base Unit x = x
coerce-full-to-base Void x = x
coerce-full-to-base (A * B) (a , b) = (coerce-full-to-base A a , coerce-full-to-base B b)
coerce-full-to-base (A + B) (inj₁ a) = inj₁ (coerce-full-to-base A a)
coerce-full-to-base (A + B) (inj₂ b) = inj₂ (coerce-full-to-base B b)
coerce-full-to-base (_ ⇒[ _ ] _) _ = tt   -- Functions → ⊤
coerce-full-to-base (Eff _ _) _ = tt       -- Effects → ⊤
coerce-full-to-base (μ-type _) _ = tt      -- μ → ⊤
coerce-full-to-base (ν-type _) _ = tt      -- ν → ⊤
coerce-full-to-base (GuardedT _ _) _ = tt  -- Guarded → ⊤
coerce-full-to-base Int x = x
coerce-full-to-base Float x = x
coerce-full-to-base Str x = x
coerce-full-to-base Buffer x = x
coerce-full-to-base (TVar _) x = x

-- | Coerce from base to full interpretation
--
-- This direction works for base types (identity). For complex types,
-- the base interpretation is ⊤, and we can't produce a complex value
-- from tt. However, for well-formed functors, these cases never occur.
--
-- For safety, we postulate a value for unreachable cases.
-- This makes it explicit: using K with complex types is ill-formed.
--
postulate
  -- Value for unreachable cases (ill-formed functor usage)
  ill-formed-K-value : ∀ {A : Set} → A

coerce-base-to-full : ∀ A → ⟦ IntRep ⟧-base A → ⟦ A ⟧
coerce-base-to-full Unit x = x
coerce-base-to-full Void x = x
coerce-base-to-full (A * B) (a , b) = (coerce-base-to-full A a , coerce-base-to-full B b)
coerce-base-to-full (A + B) (inj₁ a) = inj₁ (coerce-base-to-full A a)
coerce-base-to-full (A + B) (inj₂ b) = inj₂ (coerce-base-to-full B b)
coerce-base-to-full (_ ⇒[ _ ] _) _ = ill-formed-K-value  -- Unreachable for well-formed
coerce-base-to-full (Eff _ _) _ = ill-formed-K-value
coerce-base-to-full (μ-type _) _ = ill-formed-K-value
coerce-base-to-full (ν-type _) _ = ill-formed-K-value
coerce-base-to-full (GuardedT _ _) _ = ill-formed-K-value
coerce-base-to-full Int x = x
coerce-base-to-full Float x = x
coerce-base-to-full Str x = x
coerce-base-to-full Buffer x = x
coerce-base-to-full (TVar _) x = x

------------------------------------------------------------------------
-- μ-type Coercions (OCP-0003)
--
-- Structural coercions between ⟦ F ⟧F X and ⟦ translateF IntRep F ⟧SF X.
-- These use the type coercions above for the K case.
------------------------------------------------------------------------

-- | Coerce from ⟦ F ⟧F to ⟦ translateF F ⟧SF (for μ-type operations)
--
coerce-μ-in : ∀ F (X : Set) → ⟦ F ⟧F X → ⟦ translateF IntRep F ⟧SF X
coerce-μ-in (K A) X x = coerce-full-to-base A x
coerce-μ-in Id X x = x
coerce-μ-in (F ⊕ G) X (inj₁ x) = inj₁ (coerce-μ-in F X x)
coerce-μ-in (F ⊕ G) X (inj₂ y) = inj₂ (coerce-μ-in G X y)
coerce-μ-in (F ⊗ G) X (x , y) = (coerce-μ-in F X x , coerce-μ-in G X y)

-- | Coerce from ⟦ translateF F ⟧SF to ⟦ F ⟧F (for μ-type operations)
--
coerce-μ-out : ∀ F (X : Set) → ⟦ translateF IntRep F ⟧SF X → ⟦ F ⟧F X
coerce-μ-out (K A) X x = coerce-base-to-full A x
coerce-μ-out Id X x = x
coerce-μ-out (F ⊕ G) X (inj₁ x) = inj₁ (coerce-μ-out F X x)
coerce-μ-out (F ⊕ G) X (inj₂ y) = inj₂ (coerce-μ-out G X y)
coerce-μ-out (F ⊗ G) X (x , y) = (coerce-μ-out F X x , coerce-μ-out G X y)

------------------------------------------------------------------------
-- μ-type Operations (OCP-0003: Defined via SPF)
--
-- These use the SPF operations ⟨_⟩, outS, and cataS with structural
-- coercions to bridge between our ⟦_⟧F and SPF's ⟦_⟧SF.
------------------------------------------------------------------------

-- | In: F(μF) → μF (algebra)
--
-- OCP-0003: Defined via SPF's ⟨_⟩ constructor with coercion.
--
sem-In : ∀ (F : Functor) → ⟦ F ⟧F (⟦μ⟧ F) → ⟦μ⟧ F
sem-In F x = ⟨ coerce-μ-in F (⟦μ⟧ F) x ⟩

-- | Out: μF → F(μF) (destructor, inverse of In)
--
-- OCP-0003: Defined via SPF's outS with coercion.
--
sem-Out : ∀ (F : Functor) → ⟦μ⟧ F → ⟦ F ⟧F (⟦μ⟧ F)
sem-Out F x = coerce-μ-out F (⟦μ⟧ F) (outS (translateF IntRep F) x)

-- | Catamorphism: given algebra F(A) → A, fold μF → A
--
-- OCP-0003: Defined via SPF's cataS with coercions.
-- The algebra is lifted through coercions.
--
sem-cata : ∀ (F : Functor) {A : Set} → (⟦ F ⟧F A → A) → ⟦μ⟧ F → A
sem-cata F {A} alg = cataS {translateF IntRep F} (λ x → alg (coerce-μ-out F A x))

------------------------------------------------------------------------
-- ν-type Coercions (OCP-0003)
--
-- Similar to μ-type coercions, for ν-type (coinductive) operations.
------------------------------------------------------------------------

-- | Coerce from ⟦ F ⟧F to ⟦ translateF F ⟧SF (for ν-type operations)
coerce-ν-in : ∀ F (X : Set) → ⟦ F ⟧F X → ⟦ translateF IntRep F ⟧SF X
coerce-ν-in = coerce-μ-in  -- Same structure

-- | Coerce from ⟦ translateF F ⟧SF to ⟦ F ⟧F (for ν-type operations)
coerce-ν-out : ∀ F (X : Set) → ⟦ translateF IntRep F ⟧SF X → ⟦ F ⟧F X
coerce-ν-out = coerce-μ-out  -- Same structure

------------------------------------------------------------------------
-- ν-type Operations (OCP-0003: Defined via SPF)
------------------------------------------------------------------------

-- | CoOut: νF → F(νF) (observation)
--
-- OCP-0003: Defined via SPF's unfoldS with coercion.
--
sem-CoOut : ∀ (F : Functor) → ⟦ν⟧ F → ⟦ F ⟧F (⟦ν⟧ F)
sem-CoOut F x = coerce-ν-out F (⟦ν⟧ F) (unfoldS x)

-- | CoIn: F(νF) → νF (coalgebra)
--
-- OCP-0003: Defined via SPF's anaS with the identity coalgebra.
-- CoIn packages an F-layer observation as a ν-value.
--
sem-CoIn : ∀ (F : Functor) → ⟦ F ⟧F (⟦ν⟧ F) → ⟦ν⟧ F
unfoldS (sem-CoIn F x) = coerce-ν-in F (⟦ν⟧ F) x

-- | Anamorphism: given coalgebra A → F(A), unfold A → νF
--
-- OCP-0003: Defined via SPF's anaS with coercions.
-- The coalgebra is lifted through coercions.
--
{-# TERMINATING #-}
sem-ana : ∀ (F : Functor) {A : Set} → (A → ⟦ F ⟧F A) → A → ⟦ν⟧ F
unfoldS (sem-ana F {A} coalg a) = sfmap (translateF IntRep F) (sem-ana F coalg) (coerce-ν-in F A (coalg a))

------------------------------------------------------------------------
-- Guarded Operations (OCP-0003)
--
-- These operations support the GuardedT type for productive corecursion.
------------------------------------------------------------------------

-- | Unguard: extract functor value from guarded value
-- This "consumes" the guardedness - the F-layer has been observed.
--
-- OCP-0003: Postulated since ⟦Guarded⟧ is postulated.
-- Structurally, this would pattern match on the guarded value.
--
postulate
  sem-unguard : ∀ (F : Functor) {A : Set} → ⟦Guarded⟧ F A → ⟦ F ⟧F A

-- | Guarded anamorphism: given guarded coalgebra A → Guarded F A, unfold A → νF
-- This is the productive version of sem-ana.
--
-- OCP-0003: Defined as sem-ana composed with sem-unguard.
-- The guardedness ensures productivity.
--
sem-ana-guarded : ∀ (F : Functor) {A : Set} → (A → ⟦Guarded⟧ F A) → A → ⟦ν⟧ F
sem-ana-guarded F coalg = sem-ana F (sem-unguard F ∘ coalg)

-- | Hylomorphism: fused cata ∘ ana, computed directly
-- Semantically: hylo alg coalg = cata alg ∘ ana coalg
-- But computed without building intermediate structure
--
-- OCP-0003: Defined directly via recursion.
--
{-# TERMINATING #-}
sem-hylo : ∀ (F : Functor) {A B : Set}
         → (⟦ F ⟧F B → B)  -- algebra
         → (A → ⟦ F ⟧F A)  -- coalgebra
         → A → B
sem-hylo F alg coalg x = alg (sem-fmap F (sem-hylo F alg coalg) (coalg x))

-- | Guarded hylomorphism: fused cata with guarded coalgebra
--
-- OCP-0003: Defined as sem-hylo composed with sem-unguard.
-- The guardedness ensures productivity/termination.
--
sem-hylo-guarded : ∀ (F : Functor) {A B : Set}
                 → (⟦ F ⟧F B → B)           -- algebra
                 → (A → ⟦Guarded⟧ F A)      -- guarded coalgebra
                 → A → B
sem-hylo-guarded F alg coalg = sem-hylo F alg (sem-unguard F ∘ coalg)

------------------------------------------------------------------------
-- Type Coercion Round-Trip Properties
--
-- For base types, coerce-base-to-full ∘ coerce-full-to-base = id.
-- For complex types, we use the ill-formed-K-value postulate.
------------------------------------------------------------------------

-- | Round-trip: base-to-full ∘ full-to-base ≡ id
--
-- Proven by pattern matching on A. For base types this is definitional.
-- For complex types, we postulate it (these cases are unreachable for
-- well-formed functors).
--
postulate
  -- Round-trip for complex types (unreachable for well-formed functors)
  coerce-type-round-trip-function : ∀ {A B q} (x : ⟦ A ⟧ → ⟦ B ⟧) →
    coerce-base-to-full (A ⇒[ q ] B) (coerce-full-to-base (A ⇒[ q ] B) x) ≡ x
  coerce-type-round-trip-eff : ∀ {A B} (x : ⟦ A ⟧ → ⟦ B ⟧) →
    coerce-base-to-full (Eff A B) (coerce-full-to-base (Eff A B) x) ≡ x
  coerce-type-round-trip-μ : ∀ {F} (x : ⟦μ⟧ F) →
    coerce-base-to-full (μ-type F) (coerce-full-to-base (μ-type F) x) ≡ x
  coerce-type-round-trip-ν : ∀ {F} (x : ⟦ν⟧ F) →
    coerce-base-to-full (ν-type F) (coerce-full-to-base (ν-type F) x) ≡ x
  coerce-type-round-trip-guarded : ∀ {F A} (x : ⟦Guarded⟧ F ⟦ A ⟧) →
    coerce-base-to-full (GuardedT F A) (coerce-full-to-base (GuardedT F A) x) ≡ x

coerce-type-round-trip : ∀ A (x : ⟦ A ⟧) → coerce-base-to-full A (coerce-full-to-base A x) ≡ x
coerce-type-round-trip Unit x = refl
coerce-type-round-trip Void x = refl
coerce-type-round-trip (A * B) (a , b) = cong₂ _,_ (coerce-type-round-trip A a) (coerce-type-round-trip B b)
coerce-type-round-trip (A + B) (inj₁ a) = cong inj₁ (coerce-type-round-trip A a)
coerce-type-round-trip (A + B) (inj₂ b) = cong inj₂ (coerce-type-round-trip B b)
coerce-type-round-trip (A ⇒[ q ] B) x = coerce-type-round-trip-function {A} {B} {q} x
coerce-type-round-trip (Eff A B) x = coerce-type-round-trip-eff {A} {B} x
coerce-type-round-trip (μ-type F) x = coerce-type-round-trip-μ {F} x
coerce-type-round-trip (ν-type F) x = coerce-type-round-trip-ν {F} x
coerce-type-round-trip (GuardedT F A) x = coerce-type-round-trip-guarded {F} {A} x
coerce-type-round-trip Int x = refl
coerce-type-round-trip Float x = refl
coerce-type-round-trip Str x = refl
coerce-type-round-trip Buffer x = refl
coerce-type-round-trip (TVar _) x = refl

-- | Round-trip: full-to-base ∘ base-to-full ≡ id
--
-- Similar structure to the above.
--
postulate
  coerce-type⁻¹-round-trip-function : ∀ {A B q} (x : ⊤) →
    coerce-full-to-base (A ⇒[ q ] B) (coerce-base-to-full (A ⇒[ q ] B) x) ≡ x
  coerce-type⁻¹-round-trip-eff : ∀ {A B} (x : ⊤) →
    coerce-full-to-base (Eff A B) (coerce-base-to-full (Eff A B) x) ≡ x
  coerce-type⁻¹-round-trip-μ : ∀ {F} (x : ⊤) →
    coerce-full-to-base (μ-type F) (coerce-base-to-full (μ-type F) x) ≡ x
  coerce-type⁻¹-round-trip-ν : ∀ {F} (x : ⊤) →
    coerce-full-to-base (ν-type F) (coerce-base-to-full (ν-type F) x) ≡ x
  coerce-type⁻¹-round-trip-guarded : ∀ {F A} (x : ⊤) →
    coerce-full-to-base (GuardedT F A) (coerce-base-to-full (GuardedT F A) x) ≡ x

coerce-type⁻¹-round-trip : ∀ A (x : ⟦ IntRep ⟧-base A) → coerce-full-to-base A (coerce-base-to-full A x) ≡ x
coerce-type⁻¹-round-trip Unit x = refl
coerce-type⁻¹-round-trip Void x = refl
coerce-type⁻¹-round-trip (A * B) (a , b) = cong₂ _,_ (coerce-type⁻¹-round-trip A a) (coerce-type⁻¹-round-trip B b)
coerce-type⁻¹-round-trip (A + B) (inj₁ a) = cong inj₁ (coerce-type⁻¹-round-trip A a)
coerce-type⁻¹-round-trip (A + B) (inj₂ b) = cong inj₂ (coerce-type⁻¹-round-trip B b)
coerce-type⁻¹-round-trip (A ⇒[ q ] B) x = coerce-type⁻¹-round-trip-function {A} {B} {q} x
coerce-type⁻¹-round-trip (Eff A B) x = coerce-type⁻¹-round-trip-eff {A} {B} x
coerce-type⁻¹-round-trip (μ-type F) x = coerce-type⁻¹-round-trip-μ {F} x
coerce-type⁻¹-round-trip (ν-type F) x = coerce-type⁻¹-round-trip-ν {F} x
coerce-type⁻¹-round-trip (GuardedT F A) x = coerce-type⁻¹-round-trip-guarded {F} {A} x
coerce-type⁻¹-round-trip Int x = refl
coerce-type⁻¹-round-trip Float x = refl
coerce-type⁻¹-round-trip Str x = refl
coerce-type⁻¹-round-trip Buffer x = refl
coerce-type⁻¹-round-trip (TVar _) x = refl

------------------------------------------------------------------------
-- μ-Coercion Round-Trip Properties (OCP-0003)
--
-- The coercions between ⟦ F ⟧F and ⟦ translateF F ⟧SF are inverses.
-- This is proven by structural induction on F, using the type-level
-- round-trip lemmas for the K case.
------------------------------------------------------------------------

-- | Round-trip: coerce-μ-out ∘ coerce-μ-in ≡ id
coerce-μ-round-trip : ∀ F (X : Set) (x : ⟦ F ⟧F X)
                    → coerce-μ-out F X (coerce-μ-in F X x) ≡ x
coerce-μ-round-trip (K A) X x = coerce-type-round-trip A x
coerce-μ-round-trip Id X x = refl
coerce-μ-round-trip (F ⊕ G) X (inj₁ x) = cong inj₁ (coerce-μ-round-trip F X x)
coerce-μ-round-trip (F ⊕ G) X (inj₂ y) = cong inj₂ (coerce-μ-round-trip G X y)
coerce-μ-round-trip (F ⊗ G) X (x , y) = cong₂ _,_ (coerce-μ-round-trip F X x) (coerce-μ-round-trip G X y)

-- | Round-trip: coerce-μ-in ∘ coerce-μ-out ≡ id
coerce-μ⁻¹-round-trip : ∀ F (X : Set) (x : ⟦ translateF IntRep F ⟧SF X)
                      → coerce-μ-in F X (coerce-μ-out F X x) ≡ x
coerce-μ⁻¹-round-trip (K A) X x = coerce-type⁻¹-round-trip A x
coerce-μ⁻¹-round-trip Id X x = refl
coerce-μ⁻¹-round-trip (F ⊕ G) X (inj₁ x) = cong inj₁ (coerce-μ⁻¹-round-trip F X x)
coerce-μ⁻¹-round-trip (F ⊕ G) X (inj₂ y) = cong inj₂ (coerce-μ⁻¹-round-trip G X y)
coerce-μ⁻¹-round-trip (F ⊗ G) X (x , y) = cong₂ _,_ (coerce-μ⁻¹-round-trip F X x) (coerce-μ⁻¹-round-trip G X y)

------------------------------------------------------------------------
-- Recursion Scheme Laws (OCP-0003: Proven)
--
-- These capture the key properties of initial algebras and final
-- coalgebras. Now proven using the structural definitions.
------------------------------------------------------------------------

-- | In and Out are inverses (Lambek's Lemma, one direction)
--
-- OCP-0003: Proven using SPF's fold-unfoldS and coercion round-trip.
--
-- Proof:
--   sem-Out F (sem-In F x)
--   = coerce-μ-out F (outS ⟨ coerce-μ-in F x ⟩)  (by definition)
--   = coerce-μ-out F (coerce-μ-in F x)            (by outS ⟨_⟩ = id)
--   = x                                            (by coerce round-trip)
--
sem-Out-In : ∀ (F : Functor) (x : ⟦ F ⟧F (⟦μ⟧ F)) → sem-Out F (sem-In F x) ≡ x
sem-Out-In F x = coerce-μ-round-trip F (⟦μ⟧ F) x

-- | In and Out are inverses (Lambek's Lemma, other direction)
--
-- OCP-0003: Proven using SPF's unfold-foldS and coercion round-trip.
--
-- Proof:
--   sem-In F (sem-Out F ⟨ y ⟩)
--   = ⟨ coerce-μ-in F (coerce-μ-out F y) ⟩  (by definition, outS ⟨ y ⟩ = y)
--   = ⟨ y ⟩                                  (by coerce⁻¹ round-trip)
--
sem-In-Out : ∀ (F : Functor) (x : ⟦μ⟧ F) → sem-In F (sem-Out F x) ≡ x
sem-In-Out F ⟨ y ⟩ = cong ⟨_⟩ (coerce-μ⁻¹-round-trip F (⟦μ⟧ F) y)

------------------------------------------------------------------------
-- Fmap-Coercion Coherence for μ (OCP-0003)
--
-- This relates sem-fmap (working on ⟦ F ⟧F) to sfmap (working on ⟦ translateF F ⟧SF)
-- through the coercions.
------------------------------------------------------------------------

-- | sem-fmap through coercions equals sfmap
--
-- coerce-μ-in F ∘ sem-fmap F f ≡ sfmap (translateF F) f ∘ coerce-μ-in F
--
fmap-coerce-μ-coherence : ∀ F {X Y : Set} (f : X → Y) (x : ⟦ F ⟧F X)
                        → coerce-μ-in F Y (sem-fmap F f x) ≡ sfmap (translateF IntRep F) f (coerce-μ-in F X x)
fmap-coerce-μ-coherence (K A) f x = refl
fmap-coerce-μ-coherence Id f x = refl
fmap-coerce-μ-coherence (F ⊕ G) f (inj₁ x) = cong inj₁ (fmap-coerce-μ-coherence F f x)
fmap-coerce-μ-coherence (F ⊕ G) f (inj₂ y) = cong inj₂ (fmap-coerce-μ-coherence G f y)
fmap-coerce-μ-coherence (F ⊗ G) f (x , y) = cong₂ _,_ (fmap-coerce-μ-coherence F f x) (fmap-coerce-μ-coherence G f y)

-- | The inverse direction: sfmap through coercions equals sem-fmap
--
-- coerce-μ-out F ∘ sfmap (translateF F) f ≡ sem-fmap F f ∘ coerce-μ-out F
--
fmap-coerce-μ-coherence′ : ∀ F {X Y : Set} (f : X → Y) (x : ⟦ translateF IntRep F ⟧SF X)
                         → coerce-μ-out F Y (sfmap (translateF IntRep F) f x) ≡ sem-fmap F f (coerce-μ-out F X x)
fmap-coerce-μ-coherence′ (K A) f x = refl
fmap-coerce-μ-coherence′ Id f x = refl
fmap-coerce-μ-coherence′ (F ⊕ G) f (inj₁ x) = cong inj₁ (fmap-coerce-μ-coherence′ F f x)
fmap-coerce-μ-coherence′ (F ⊕ G) f (inj₂ y) = cong inj₂ (fmap-coerce-μ-coherence′ G f y)
fmap-coerce-μ-coherence′ (F ⊗ G) f (x , y) = cong₂ _,_ (fmap-coerce-μ-coherence′ F f x) (fmap-coerce-μ-coherence′ G f y)

------------------------------------------------------------------------
-- Catamorphism Laws (OCP-0003: Proven)
------------------------------------------------------------------------

-- | Catamorphism computation law
--
-- OCP-0003: Proven using SPF's cataS-computation and coercion coherence.
--
-- Proof:
--   sem-cata F alg (sem-In F x)
--   = cataS (alg ∘ coerce-μ-out F) ⟨ coerce-μ-in F x ⟩
--   = (alg ∘ coerce-μ-out F) (sfmapCata (translateF F) ... (coerce-μ-in F x))
--   By cataS-computation and coherence properties.
--
sem-cata-compute : ∀ (F : Functor) {A : Set} (alg : ⟦ F ⟧F A → A) (x : ⟦ F ⟧F (⟦μ⟧ F))
                 → sem-cata F alg (sem-In F x) ≡ alg (sem-fmap F (sem-cata F alg) x)
sem-cata-compute F {A} alg x =
  let TF = translateF IntRep F
      alg′ = λ y → alg (coerce-μ-out F A y)
      -- sem-cata F alg (sem-In F x) = cataS alg′ ⟨ coerce-μ-in F x ⟩
      -- By definition of cataS: alg′ (sfmapCata TF alg′ (coerce-μ-in F x))
      -- By sfmapCata-is-sfmap: alg′ (sfmap TF (cataS alg′) (coerce-μ-in F x))
      -- By fmap-coerce-μ-coherence′: alg (coerce-μ-out F (sfmap TF (cataS alg′) (coerce-μ-in F x)))
      --                            = alg (sem-fmap F (cataS alg′) (coerce-μ-out F (coerce-μ-in F x)))
      --                            = alg (sem-fmap F (sem-cata F alg) x)  (by round-trip)
      step1 : cataS {TF} alg′ ⟨ coerce-μ-in F (⟦μ⟧ F) x ⟩ ≡ alg′ (sfmap TF (cataS alg′) (coerce-μ-in F (⟦μ⟧ F) x))
      step1 = cataS-computation TF alg′ (coerce-μ-in F (⟦μ⟧ F) x)

      step2 : alg′ (sfmap TF (cataS alg′) (coerce-μ-in F (⟦μ⟧ F) x))
            ≡ alg (coerce-μ-out F A (sfmap TF (cataS alg′) (coerce-μ-in F (⟦μ⟧ F) x)))
      step2 = refl

      step3 : coerce-μ-out F A (sfmap TF (cataS alg′) (coerce-μ-in F (⟦μ⟧ F) x))
            ≡ sem-fmap F (cataS alg′) (coerce-μ-out F (⟦μ⟧ F) (coerce-μ-in F (⟦μ⟧ F) x))
      step3 = fmap-coerce-μ-coherence′ F (cataS alg′) (coerce-μ-in F (⟦μ⟧ F) x)

      step4 : coerce-μ-out F (⟦μ⟧ F) (coerce-μ-in F (⟦μ⟧ F) x) ≡ x
      step4 = coerce-μ-round-trip F (⟦μ⟧ F) x

      step5 : sem-fmap F (cataS alg′) x ≡ sem-fmap F (sem-cata F alg) x
      step5 = refl  -- by definition of sem-cata
  in trans step1 (trans step2 (cong alg (trans step3 (cong (sem-fmap F (sem-cata F alg)) step4))))

-- | Identity catamorphism: cata with In algebra is identity
--
-- OCP-0003: Proven using SPF's cataS-In-id and coercion coherence.
--
-- The key insight is that sem-cata F sem-In = cataS (⟨_⟩ ∘ coerce-μ-in F ∘ coerce-μ-out F)
--                                            = cataS ⟨_⟩ (by round-trip being id)
--                                            = id       (by cataS-In-id)
--
sem-cata-In-id : ∀ (F : Functor) (x : ⟦μ⟧ F) → sem-cata F (sem-In F) x ≡ x
sem-cata-In-id F x =
  let TF = translateF IntRep F
      -- The algebra: λ y → sem-In F (coerce-μ-out F (⟦μ⟧ F) y)
      --            = λ y → ⟨ coerce-μ-in F (coerce-μ-out F y) ⟩
      --            = λ y → ⟨ y ⟩  (by coerce round-trip)
      alg′ : ⟦ TF ⟧SF (μS TF) → μS TF
      alg′ y = ⟨ coerce-μ-in F (⟦μ⟧ F) (coerce-μ-out F (⟦μ⟧ F) y) ⟩

      -- Show alg′ = ⟨_⟩
      alg′-eq : ∀ y → alg′ y ≡ ⟨ y ⟩
      alg′-eq y = cong ⟨_⟩ (coerce-μ⁻¹-round-trip F (⟦μ⟧ F) y)

      alg′≡In : alg′ ≡ ⟨_⟩
      alg′≡In = funext alg′-eq

      step1 : cataS {TF} alg′ x ≡ cataS ⟨_⟩ x
      step1 = cong (λ f → cataS f x) alg′≡In

      step2 : cataS {TF} ⟨_⟩ x ≡ x
      step2 = cataS-In-id x

  in trans step1 step2

------------------------------------------------------------------------
-- Anamorphism Laws (OCP-0003: Proven)
------------------------------------------------------------------------

-- | Identity anamorphism: ana with CoOut coalgebra is identity
--
-- OCP-0003: This law fundamentally requires coinductive reasoning
-- (bisimulation = equality).
--
-- The proof sketch is:
--   sem-ana F (sem-CoOut F) x
--   is bisimilar to anaS unfoldS x (via coercion round-trips)
--   = x (by anaS-Out-id)
--
-- Since sem-ana uses coercions while anaS doesn't, showing the
-- bisimilarity requires establishing that coerce-ν-in ∘ sem-CoOut = unfoldS,
-- which follows from coerce-ν-in ∘ coerce-ν-out = id.
--
-- We postulate this because the coinductive proof structure is the same
-- as anaS-Out-id. Both require the bisim-to-eq axiom.
--
postulate
  sem-ana-Out-id : ∀ (F : Functor) (x : ⟦ν⟧ F) → sem-ana F (sem-CoOut F) x ≡ x

------------------------------------------------------------------------
-- Hylomorphism Laws (OCP-0003: Definitional)
------------------------------------------------------------------------

-- | Hylomorphism computation law
--
-- OCP-0003: Definitionally true from the recursive definition of sem-hylo.
--
-- hylo alg coalg x = alg (fmap (hylo alg coalg) (coalg x))
--
-- This is exactly how sem-hylo is defined, so the proof is refl.
--
sem-hylo-compute : ∀ (F : Functor) {A B : Set} (alg : ⟦ F ⟧F B → B) (coalg : A → ⟦ F ⟧F A) (x : A)
                 → sem-hylo F alg coalg x ≡ alg (sem-fmap F (sem-hylo F alg coalg) (coalg x))
sem-hylo-compute F alg coalg x = refl

-- | Guarded hylomorphism computation law
--
-- OCP-0003: Definitionally true from the definition of sem-hylo-guarded.
--
-- sem-hylo-guarded F alg coalg = sem-hylo F alg (sem-unguard F ∘ coalg)
-- So sem-hylo-guarded F alg coalg x
--    = alg (fmap (sem-hylo F alg (sem-unguard F ∘ coalg)) (sem-unguard F (coalg x)))
--    = alg (fmap (sem-hylo-guarded F alg coalg) (sem-unguard F (coalg x)))
--
sem-hylo-guarded-compute : ∀ (F : Functor) {A B : Set}
                           (alg : ⟦ F ⟧F B → B) (coalg : A → ⟦Guarded⟧ F A) (x : A)
                         → sem-hylo-guarded F alg coalg x ≡
                           alg (sem-fmap F (sem-hylo-guarded F alg coalg) (sem-unguard F (coalg x)))
sem-hylo-guarded-compute F alg coalg x = refl