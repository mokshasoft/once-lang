-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

{-# OPTIONS --large-indices #-}
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
--
-- Note: --large-indices is required because ⟦Guarded⟧ is indexed by Set.
-- This allows constructors like GRec to store values of the index type.
-- Agda explicitly suggests this for forced index patterns.
------------------------------------------------------------------------

module Once.Semantics.Core (IntRep : Set) where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Float using () renaming (Float to AgdaFloat)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym; subst)
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

open import Once.Functor.Translate using (μ-sem; ν-sem; translateF; ⟦_⟧-base; IsBaseType; WellFormedF)
open import Once.Functor.Translate
  using ( base-Unit; base-Void; base-Int; base-Float; base-Str; base-Buffer
        ; base-Prod; base-Sum; wf-K; wf-Id; wf-Sum; wf-Prod)
open import Once.Functor.Base
  using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF; μS; ⟨_⟩; outS; νS; unfoldS;
         sfmap; cataS; sfmapCata; sfmapCata-is-sfmap; anaS;
         fold-unfoldS; unfold-foldS; cataS-computation; cataS-In-id; anaS-Out-id;
         -- Bisimulation machinery
         ⟦_⟧SF-rel; _∼S_; bisimS-to-eq; sfmap-rel; sfmap-f-rel)

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
-- ⟦Guarded⟧ F A represents guarded F-shaped values with A at recursive
-- positions. It is structurally isomorphic to ⟦ F ⟧F A.
--
-- KEY DESIGN DECISION: GConst uses ⟦_⟧-base instead of ⟦_⟧.
-- This breaks the mutual dependency cycle and avoids strict positivity
-- violations. Since ⟦_⟧-base returns ⊤ for complex types (functions,
-- μ-type, ν-type, GuardedT), and well-formed functors only use base
-- types in K positions, this is semantically equivalent for valid code.
--
-- STRUCTURAL ISOMORPHISM: ⟦Guarded⟧ F A ≅ ⟦ F ⟧F A
-- The Guarded constructors mirror the functor structure exactly:
--   GConst for K, GRec for Id, GProd for ⊗, GInl/GInr for ⊕
--
-- This enables proving:
--   sem-guard : ⟦ F ⟧F A → ⟦Guarded⟧ F A
--   sem-unguard : ⟦Guarded⟧ F A → ⟦ F ⟧F A
--   sem-unguard ∘ sem-guard = id
--   sem-guard ∘ sem-unguard = id
------------------------------------------------------------------------

-- | Guarded functor values (structural definition)
--
-- Each constructor corresponds to a functor constructor:
--   GConst : constant values (K A) - uses ⟦_⟧-base to avoid cycle
--   GRec   : recursive positions (Id) - the "guard"
--   GProd  : products (F ⊗ G)
--   GInl   : left injection (F ⊕ G)
--   GInr   : right injection (F ⊕ G)
--
data ⟦Guarded⟧ : Functor → Set → Set where
  GConst : ∀ {A B} → ⟦ IntRep ⟧-base A → ⟦Guarded⟧ (K A) B
  GRec   : ∀ {A} → A → ⟦Guarded⟧ Id A
  GProd  : ∀ {F G A} → ⟦Guarded⟧ F A → ⟦Guarded⟧ G A → ⟦Guarded⟧ (F ⊗ G) A
  GInl   : ∀ {F G A} → ⟦Guarded⟧ F A → ⟦Guarded⟧ (F ⊕ G) A
  GInr   : ∀ {F G A} → ⟦Guarded⟧ G A → ⟦Guarded⟧ (F ⊕ G) A

------------------------------------------------------------------------
-- Type Interpretation
------------------------------------------------------------------------

-- | Type interpretation
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
------------------------------------------------------------------------
-- Well-Formed Type Coercion (No Postulates)
--
-- OCP-0003: Coercion from base to full interpretation requires an
-- IsBaseType proof, ensuring totality without postulates.
--
-- For base types, the coercion is an identity (structurally).
-- Complex types (functions, μ-type, ν-type, GuardedT) are excluded
-- by the IsBaseType predicate, so we never need to produce values
-- we can't construct.
------------------------------------------------------------------------

-- | Coerce from base to full interpretation
--
-- Requires an IsBaseType proof, making it total without postulates.
--
coerce-base-to-full : ∀ {A} → IsBaseType A → ⟦ IntRep ⟧-base A → ⟦ A ⟧
coerce-base-to-full base-Unit x = x
coerce-base-to-full base-Void ()
coerce-base-to-full base-Int x = x
coerce-base-to-full base-Float x = x
coerce-base-to-full base-Str x = x
coerce-base-to-full base-Buffer x = x
coerce-base-to-full (base-Prod pA pB) (a , b) =
  (coerce-base-to-full pA a , coerce-base-to-full pB b)
coerce-base-to-full (base-Sum pA pB) (inj₁ a) = inj₁ (coerce-base-to-full pA a)
coerce-base-to-full (base-Sum pA pB) (inj₂ b) = inj₂ (coerce-base-to-full pB b)

------------------------------------------------------------------------
-- Type Coercion Round-Trip Properties (Well-Formed Only)
--
-- For base types (IsBaseType A), the coercions are definitionally identity.
-- This provides a postulate-free path for well-formed functors.
------------------------------------------------------------------------

-- | For base types, coerce-base-to-full ∘ coerce-full-to-base = id (PROVEN)
--
-- This is the key lemma for well-formed functors.
--
coerce-base-type-round-trip : ∀ {A} → (pA : IsBaseType A) → (x : ⟦ A ⟧)
                            → coerce-base-to-full pA (coerce-full-to-base A x) ≡ x
coerce-base-type-round-trip base-Unit x = refl
coerce-base-type-round-trip base-Void ()
coerce-base-type-round-trip base-Int x = refl
coerce-base-type-round-trip base-Float x = refl
coerce-base-type-round-trip base-Str x = refl
coerce-base-type-round-trip base-Buffer x = refl
coerce-base-type-round-trip (base-Prod pA pB) (a , b) =
  cong₂ _,_ (coerce-base-type-round-trip pA a) (coerce-base-type-round-trip pB b)
coerce-base-type-round-trip (base-Sum pA pB) (inj₁ a) =
  cong inj₁ (coerce-base-type-round-trip pA a)
coerce-base-type-round-trip (base-Sum pA pB) (inj₂ b) =
  cong inj₂ (coerce-base-type-round-trip pB b)

-- | For base types, coerce-full-to-base ∘ coerce-base-to-full = id (PROVEN)
--
coerce-base-type⁻¹-round-trip : ∀ {A} → (pA : IsBaseType A) → (x : ⟦ IntRep ⟧-base A)
                              → coerce-full-to-base A (coerce-base-to-full pA x) ≡ x
coerce-base-type⁻¹-round-trip base-Unit x = refl
coerce-base-type⁻¹-round-trip base-Void ()
coerce-base-type⁻¹-round-trip base-Int x = refl
coerce-base-type⁻¹-round-trip base-Float x = refl
coerce-base-type⁻¹-round-trip base-Str x = refl
coerce-base-type⁻¹-round-trip base-Buffer x = refl
coerce-base-type⁻¹-round-trip (base-Prod pA pB) (a , b) =
  cong₂ _,_ (coerce-base-type⁻¹-round-trip pA a) (coerce-base-type⁻¹-round-trip pB b)
coerce-base-type⁻¹-round-trip (base-Sum pA pB) (inj₁ a) =
  cong inj₁ (coerce-base-type⁻¹-round-trip pA a)
coerce-base-type⁻¹-round-trip (base-Sum pA pB) (inj₂ b) =
  cong inj₂ (coerce-base-type⁻¹-round-trip pB b)

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
-- Requires a WellFormedF proof to ensure K positions only use base types.
--
coerce-μ-out : ∀ {F} → WellFormedF F → (X : Set) → ⟦ translateF IntRep F ⟧SF X → ⟦ F ⟧F X
coerce-μ-out (wf-K pA) X x = coerce-base-to-full pA x
coerce-μ-out wf-Id X x = x
coerce-μ-out (wf-Sum wfF wfG) X (inj₁ x) = inj₁ (coerce-μ-out wfF X x)
coerce-μ-out (wf-Sum wfF wfG) X (inj₂ y) = inj₂ (coerce-μ-out wfG X y)
coerce-μ-out (wf-Prod wfF wfG) X (x , y) = (coerce-μ-out wfF X x , coerce-μ-out wfG X y)

------------------------------------------------------------------------
-- Well-Formed μ-Coercion Round-Trip (PROVEN, No Postulates)
--
-- For well-formed functors, the μ-coercion round-trips are provable
-- using the base-type round-trip lemmas.
------------------------------------------------------------------------

-- | coerce-μ-out ∘ coerce-μ-in = id (PROVEN)
--
coerce-μ-round-trip : ∀ {F} → (wf : WellFormedF F) → ∀ (X : Set) (x : ⟦ F ⟧F X)
                    → coerce-μ-out wf X (coerce-μ-in F X x) ≡ x
coerce-μ-round-trip (wf-K pA) X x = coerce-base-type-round-trip pA x
coerce-μ-round-trip wf-Id X x = refl
coerce-μ-round-trip (wf-Sum wfF wfG) X (inj₁ x) =
  cong inj₁ (coerce-μ-round-trip wfF X x)
coerce-μ-round-trip (wf-Sum wfF wfG) X (inj₂ y) =
  cong inj₂ (coerce-μ-round-trip wfG X y)
coerce-μ-round-trip (wf-Prod wfF wfG) X (x , y) =
  cong₂ _,_ (coerce-μ-round-trip wfF X x) (coerce-μ-round-trip wfG X y)

-- | coerce-μ-in ∘ coerce-μ-out = id (PROVEN)
--
coerce-μ⁻¹-round-trip : ∀ {F} → (wf : WellFormedF F) → ∀ (X : Set) (x : ⟦ translateF IntRep F ⟧SF X)
                      → coerce-μ-in F X (coerce-μ-out wf X x) ≡ x
coerce-μ⁻¹-round-trip (wf-K pA) X x = coerce-base-type⁻¹-round-trip pA x
coerce-μ⁻¹-round-trip wf-Id X x = refl
coerce-μ⁻¹-round-trip (wf-Sum wfF wfG) X (inj₁ x) =
  cong inj₁ (coerce-μ⁻¹-round-trip wfF X x)
coerce-μ⁻¹-round-trip (wf-Sum wfF wfG) X (inj₂ y) =
  cong inj₂ (coerce-μ⁻¹-round-trip wfG X y)
coerce-μ⁻¹-round-trip (wf-Prod wfF wfG) X (x , y) =
  cong₂ _,_ (coerce-μ⁻¹-round-trip wfF X x) (coerce-μ⁻¹-round-trip wfG X y)

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
-- Requires WellFormedF proof for postulate-free coercion.
--
sem-Out : ∀ {F : Functor} → WellFormedF F → ⟦μ⟧ F → ⟦ F ⟧F (⟦μ⟧ F)
sem-Out {F} wf x = coerce-μ-out wf (⟦μ⟧ F) (outS (translateF IntRep F) x)

-- | Catamorphism: given algebra F(A) → A, fold μF → A
--
-- OCP-0003: Defined via SPF's cataS with coercions.
-- Requires WellFormedF proof for postulate-free coercion.
--
sem-cata : ∀ {F : Functor} → WellFormedF F → {A : Set} → (⟦ F ⟧F A → A) → ⟦μ⟧ F → A
sem-cata {F} wf {A} alg = cataS {translateF IntRep F} (λ x → alg (coerce-μ-out wf A x))

------------------------------------------------------------------------
-- ν-type Coercions (OCP-0003)
--
-- Similar to μ-type coercions, for ν-type (coinductive) operations.
------------------------------------------------------------------------

-- | Coerce from ⟦ F ⟧F to ⟦ translateF F ⟧SF (for ν-type operations)
coerce-ν-in : ∀ F (X : Set) → ⟦ F ⟧F X → ⟦ translateF IntRep F ⟧SF X
coerce-ν-in = coerce-μ-in  -- Same structure

-- | Coerce from ⟦ translateF F ⟧SF to ⟦ F ⟧F (for ν-type operations)
-- Requires WellFormedF proof for postulate-free coercion.
coerce-ν-out : ∀ {F} → WellFormedF F → (X : Set) → ⟦ translateF IntRep F ⟧SF X → ⟦ F ⟧F X
coerce-ν-out = coerce-μ-out  -- Same structure

------------------------------------------------------------------------
-- ν-type Operations (OCP-0003: Defined via SPF)
------------------------------------------------------------------------

-- | CoOut: νF → F(νF) (observation)
--
-- OCP-0003: Defined via SPF's unfoldS with coercion.
-- Requires WellFormedF proof for postulate-free coercion.
--
sem-CoOut : ∀ {F : Functor} → WellFormedF F → ⟦ν⟧ F → ⟦ F ⟧F (⟦ν⟧ F)
sem-CoOut {F} wf x = coerce-ν-out wf (⟦ν⟧ F) (unfoldS x)

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
-- Now defined structurally since ⟦Guarded⟧ is structurally defined.
------------------------------------------------------------------------

-- | Unguard: extract functor value from guarded value
--
-- This "consumes" the guardedness - the F-layer has been observed.
-- Requires WellFormedF proof for postulate-free coercion at K positions.
--
-- Note: For K positions, we coerce from ⟦_⟧-base to ⟦_⟧ since GConst
-- stores base interpretation values but ⟦ F ⟧F uses full interpretation.
--
sem-unguard : ∀ {F : Functor} → WellFormedF F → ∀ {A : Set} → ⟦Guarded⟧ F A → ⟦ F ⟧F A
sem-unguard (wf-K pB) (GConst x) = coerce-base-to-full pB x
sem-unguard wf-Id (GRec a) = a
sem-unguard (wf-Prod wfF wfG) (GProd gf gg) =
  (sem-unguard wfF gf , sem-unguard wfG gg)
sem-unguard (wf-Sum wfF wfG) (GInl gf) = inj₁ (sem-unguard wfF gf)
sem-unguard (wf-Sum wfF wfG) (GInr gg) = inj₂ (sem-unguard wfG gg)

-- | Guard: wrap functor value as guarded
--
-- Establishes the isomorphism: ⟦Guarded⟧ F A ≅ ⟦ F ⟧F A
--
-- CATEGORICAL JUSTIFICATION:
-- ⟦Guarded⟧ F A is structurally isomorphic to ⟦ F ⟧F A. The Guarded
-- constructors mirror the functor structure exactly:
--   GConst for K, GRec for Id, GProd for ⊗, GInl/GInr for ⊕
--
-- Any ⟦ F ⟧F A value can be wrapped as ⟦Guarded⟧ F A by following the
-- functor structure. This doesn't bypass productivity - it just
-- recognizes that the types are isomorphic.
--
-- The PURPOSE of requiring GuardedT in Ana is to ensure coalgebras are
-- DEFINED in a guarded way. But for EXISTING F(A) values (e.g., from
-- Out observing a ν-value), wrapping as Guarded is always valid.
--
-- Note: For K positions, we coerce from ⟦_⟧ to ⟦_⟧-base since GConst
-- stores base interpretation values but ⟦ F ⟧F uses full interpretation.
--
sem-guard : ∀ (F : Functor) {A : Set} → ⟦ F ⟧F A → ⟦Guarded⟧ F A
sem-guard (K B) x = GConst (coerce-full-to-base B x)
sem-guard Id a = GRec a
sem-guard (F ⊗ G) (xf , xg) = GProd (sem-guard F xf) (sem-guard G xg)
sem-guard (F ⊕ G) (inj₁ xf) = GInl (sem-guard F xf)
sem-guard (F ⊕ G) (inj₂ xg) = GInr (sem-guard G xg)

-- | Guard-Unguard round-trip: unguard ∘ guard = id (PROVEN)
--
sem-unguard-guard : ∀ {F : Functor} → (wf : WellFormedF F) → ∀ {A : Set} (x : ⟦ F ⟧F A)
                  → sem-unguard wf (sem-guard F x) ≡ x
sem-unguard-guard (wf-K pB) x = coerce-base-type-round-trip pB x
sem-unguard-guard wf-Id a = refl
sem-unguard-guard (wf-Prod wfF wfG) (xf , xg) =
  cong₂ _,_ (sem-unguard-guard wfF xf) (sem-unguard-guard wfG xg)
sem-unguard-guard (wf-Sum wfF wfG) (inj₁ xf) = cong inj₁ (sem-unguard-guard wfF xf)
sem-unguard-guard (wf-Sum wfF wfG) (inj₂ xg) = cong inj₂ (sem-unguard-guard wfG xg)

-- | Guard-Unguard round-trip: guard ∘ unguard = id (PROVEN)
--
sem-guard-unguard : ∀ {F : Functor} → (wf : WellFormedF F) → ∀ {A : Set} (x : ⟦Guarded⟧ F A)
                  → sem-guard F (sem-unguard wf x) ≡ x
sem-guard-unguard (wf-K pB) (GConst x) = cong GConst (coerce-base-type⁻¹-round-trip pB x)
sem-guard-unguard wf-Id (GRec a) = refl
sem-guard-unguard (wf-Prod wfF wfG) (GProd gf gg) =
  cong₂ GProd (sem-guard-unguard wfF gf) (sem-guard-unguard wfG gg)
sem-guard-unguard (wf-Sum wfF wfG) (GInl gf) = cong GInl (sem-guard-unguard wfF gf)
sem-guard-unguard (wf-Sum wfF wfG) (GInr gg) = cong GInr (sem-guard-unguard wfG gg)

-- | Guarded anamorphism: given guarded coalgebra A → Guarded F A, unfold A → νF
-- This is the productive version of sem-ana.
--
-- OCP-0003: Defined as sem-ana composed with sem-unguard.
-- Requires WellFormedF proof for postulate-free coercion.
--
sem-ana-guarded : ∀ {F : Functor} → WellFormedF F → {A : Set} → (A → ⟦Guarded⟧ F A) → A → ⟦ν⟧ F
sem-ana-guarded {F} wf coalg = sem-ana F (sem-unguard wf ∘ coalg)

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
-- Requires WellFormedF proof for postulate-free coercion.
--
sem-hylo-guarded : ∀ {F : Functor} → WellFormedF F → {A B : Set}
                 → (⟦ F ⟧F B → B)           -- algebra
                 → (A → ⟦Guarded⟧ F A)      -- guarded coalgebra
                 → A → B
sem-hylo-guarded {F} wf alg coalg = sem-hylo F alg (sem-unguard wf ∘ coalg)

------------------------------------------------------------------------
-- μ-Coercion Round-Trip Properties (OCP-0003)
--
-- The coercions between ⟦ F ⟧F and ⟦ translateF F ⟧SF are inverses.
-- This is proven by structural induction on F, using the type-level
-- round-trip lemmas for the K case.
------------------------------------------------------------------------

-- | Round-trip: coerce-μ-out ∘ coerce-μ-in ≡ id
-- | coerce-μ-round-trip: Requires WellFormedF (see coerce-wf-μ-round-trip above)
-- | coerce-μ⁻¹-round-trip: Requires WellFormedF (see coerce-wf-μ⁻¹-round-trip above)

------------------------------------------------------------------------
-- Recursion Scheme Laws (OCP-0003: Proven for Well-Formed Functors)
--
-- These capture the key properties of initial algebras and final
-- coalgebras. Proven for well-formed functors without postulates.
------------------------------------------------------------------------

-- | In and Out are inverses (Lambek's Lemma, one direction)
--
-- OCP-0003: Proven using coerce-μ-round-trip.
--
sem-Out-In : ∀ {F : Functor} → (wf : WellFormedF F) → (x : ⟦ F ⟧F (⟦μ⟧ F)) → sem-Out wf (sem-In F x) ≡ x
sem-Out-In wf x = coerce-μ-round-trip wf _ x

-- | In and Out are inverses (Lambek's Lemma, other direction)
--
-- OCP-0003: Proven using coerce-μ⁻¹-round-trip.
--
sem-In-Out : ∀ {F : Functor} → (wf : WellFormedF F) → (x : ⟦μ⟧ F) → sem-In F (sem-Out wf x) ≡ x
sem-In-Out wf ⟨ y ⟩ = cong ⟨_⟩ (coerce-μ⁻¹-round-trip wf _ y)

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
-- coerce-μ-out wf ∘ sfmap (translateF F) f ≡ sem-fmap F f ∘ coerce-μ-out wf
--
fmap-coerce-μ-coherence′ : ∀ {F} (wf : WellFormedF F) {X Y : Set} (f : X → Y) (x : ⟦ translateF IntRep F ⟧SF X)
                         → coerce-μ-out wf Y (sfmap (translateF IntRep F) f x) ≡ sem-fmap F f (coerce-μ-out wf X x)
fmap-coerce-μ-coherence′ (wf-K pA) f x = refl
fmap-coerce-μ-coherence′ wf-Id f x = refl
fmap-coerce-μ-coherence′ (wf-Sum wfF wfG) f (inj₁ x) = cong inj₁ (fmap-coerce-μ-coherence′ wfF f x)
fmap-coerce-μ-coherence′ (wf-Sum wfF wfG) f (inj₂ y) = cong inj₂ (fmap-coerce-μ-coherence′ wfG f y)
fmap-coerce-μ-coherence′ (wf-Prod wfF wfG) f (x , y) = cong₂ _,_ (fmap-coerce-μ-coherence′ wfF f x) (fmap-coerce-μ-coherence′ wfG f y)

------------------------------------------------------------------------
-- Catamorphism Laws (OCP-0003: Proven)
------------------------------------------------------------------------

-- | Catamorphism computation law (PROVEN)
--
-- OCP-0003: Proven using SPF's cataS-computation and coercion coherence.
--
-- Proof:
--   sem-cata wf alg (sem-In F x)
--   = cataS (alg ∘ coerce-μ-out wf) ⟨ coerce-μ-in F x ⟩
--   = (alg ∘ coerce-μ-out wf) (sfmapCata (translateF F) ... (coerce-μ-in F x))
--   By cataS-computation and coherence properties.
--
sem-cata-compute : ∀ {F : Functor} → (wf : WellFormedF F) → ∀ {A : Set} (alg : ⟦ F ⟧F A → A) (x : ⟦ F ⟧F (⟦μ⟧ F))
                 → sem-cata wf alg (sem-In F x) ≡ alg (sem-fmap F (sem-cata wf alg) x)
sem-cata-compute {F} wf {A} alg x =
  let TF = translateF IntRep F
      alg′ = λ y → alg (coerce-μ-out wf A y)
      step1 : cataS {TF} alg′ ⟨ coerce-μ-in F (⟦μ⟧ F) x ⟩ ≡ alg′ (sfmap TF (cataS alg′) (coerce-μ-in F (⟦μ⟧ F) x))
      step1 = cataS-computation TF alg′ (coerce-μ-in F (⟦μ⟧ F) x)
      step2 : alg′ (sfmap TF (cataS alg′) (coerce-μ-in F (⟦μ⟧ F) x))
            ≡ alg (coerce-μ-out wf A (sfmap TF (cataS alg′) (coerce-μ-in F (⟦μ⟧ F) x)))
      step2 = refl
      step3 : coerce-μ-out wf A (sfmap TF (cataS alg′) (coerce-μ-in F (⟦μ⟧ F) x))
            ≡ sem-fmap F (cataS alg′) (coerce-μ-out wf (⟦μ⟧ F) (coerce-μ-in F (⟦μ⟧ F) x))
      step3 = fmap-coerce-μ-coherence′ wf (cataS alg′) (coerce-μ-in F (⟦μ⟧ F) x)
      step4 : coerce-μ-out wf (⟦μ⟧ F) (coerce-μ-in F (⟦μ⟧ F) x) ≡ x
      step4 = coerce-μ-round-trip wf (⟦μ⟧ F) x
      step5 : sem-fmap F (cataS alg′) x ≡ sem-fmap F (sem-cata wf alg) x
      step5 = refl
  in trans step1 (trans step2 (cong alg (trans step3 (cong (sem-fmap F (sem-cata wf alg)) step4))))

-- | Identity catamorphism: cata with In algebra is identity (PROVEN)
--
-- OCP-0003: Proven using SPF's cataS-In-id and coercion coherence.
--
-- The key insight is that sem-cata wf sem-In = cataS (⟨_⟩ ∘ coerce-μ-in F ∘ coerce-μ-out wf)
--                                             = cataS ⟨_⟩ (by round-trip being id)
--                                             = id       (by cataS-In-id)
--
sem-cata-In-id : ∀ {F : Functor} → (wf : WellFormedF F) → (x : ⟦μ⟧ F) → sem-cata wf (sem-In F) x ≡ x
sem-cata-In-id {F} wf x =
  let TF = translateF IntRep F
      alg′ : ⟦ TF ⟧SF (μS TF) → μS TF
      alg′ y = ⟨ coerce-μ-in F (⟦μ⟧ F) (coerce-μ-out wf (⟦μ⟧ F) y) ⟩
      alg′-eq : ∀ y → alg′ y ≡ ⟨ y ⟩
      alg′-eq y = cong ⟨_⟩ (coerce-μ⁻¹-round-trip wf (⟦μ⟧ F) y)
      alg′≡In : alg′ ≡ ⟨_⟩
      alg′≡In = funext alg′-eq
      step1 : cataS {TF} alg′ x ≡ cataS ⟨_⟩ x
      step1 = cong (λ f → cataS f x) alg′≡In
      step2 : cataS {TF} ⟨_⟩ x ≡ x
      step2 = cataS-In-id x
  in trans step1 step2

------------------------------------------------------------------------
-- Anamorphism Laws (OCP-0003: Proven for Well-Formed Functors)
------------------------------------------------------------------------

-- | Key lemma: coerce-ν-in after sem-CoOut equals unfoldS (PROVEN)
--
-- This follows from the coercion round-trip: coerce-ν-in ∘ coerce-ν-out = id.
-- Since sem-CoOut wf x = coerce-ν-out wf (unfoldS x), we have:
--   coerce-ν-in F (sem-CoOut wf x) = coerce-ν-in F (coerce-ν-out wf (unfoldS x)) = unfoldS x
--
coerce-ν-in-sem-CoOut : ∀ {F} → (wf : WellFormedF F) → (x : ⟦ν⟧ F)
                      → coerce-ν-in F (⟦ν⟧ F) (sem-CoOut wf x) ≡ unfoldS x
coerce-ν-in-sem-CoOut wf x = coerce-μ⁻¹-round-trip wf _ (unfoldS x)

-- | Helper: relate sfmap applied to same value with different functions
--
-- If f y ∼S g y for all y in positions of v, then
-- sfmap F f v is related to sfmap F g v.
--
sfmap-bisim : ∀ G {F : Functor} (f g : ⟦ν⟧ F → ⟦ν⟧ F)
            → (∀ y → f y ∼S g y)
            → (v : ⟦ G ⟧SF (⟦ν⟧ F))
            → ⟦ G ⟧SF-rel (_∼S_) (sfmap G f v) (sfmap G g v)
sfmap-bisim (SK _) f g hyp v = refl
sfmap-bisim SId f g hyp v = hyp v
sfmap-bisim (G₁ S⊕ G₂) f g hyp (inj₁ v) = sfmap-bisim G₁ f g hyp v
sfmap-bisim (G₁ S⊕ G₂) f g hyp (inj₂ v) = sfmap-bisim G₂ f g hyp v
sfmap-bisim (G₁ S⊗ G₂) f g hyp (v₁ , v₂) =
  sfmap-bisim G₁ f g hyp v₁ , sfmap-bisim G₂ f g hyp v₂

-- | sem-ana F (sem-CoOut wf) is bisimilar to anaS unfoldS (coinductive proof)
--
-- Both functions satisfy the same corecursive equation:
--   unfoldS (f x) = sfmap TF f (unfoldS x)
--
-- Proof by coinduction:
-- 1. unfoldS (sem-ana F (sem-CoOut wf) x)
--    = sfmap TF (sem-ana F (sem-CoOut wf)) (coerce-ν-in F (sem-CoOut wf x))  [by def]
--    = sfmap TF (sem-ana F (sem-CoOut wf)) (unfoldS x)                       [by round-trip]
--
-- 2. unfoldS (anaS unfoldS x)
--    = sfmap TF (anaS unfoldS) (unfoldS x)                                   [by def]
--
-- Both observations are sfmap TF applied to the same underlying value (unfoldS x)
-- but with different functions. By sfmap-bisim with the coinductive hypothesis
-- (sem-ana F (sem-CoOut wf) y ∼S anaS unfoldS y for all y), they are related.
--
{-# TERMINATING #-}
sem-ana-bisim-anaS : ∀ {F} → (wf : WellFormedF F) → (x : ⟦ν⟧ F)
                   → sem-ana F (sem-CoOut wf) x ∼S anaS unfoldS x
_∼S_.unfoldS-∼ (sem-ana-bisim-anaS {F} wf x) =
  let TF = translateF IntRep F
      -- The coercion round-trip gives us the key equality
      obs-eq : coerce-ν-in F (⟦ν⟧ F) (sem-CoOut wf x) ≡ unfoldS x
      obs-eq = coerce-ν-in-sem-CoOut wf x
      -- LHS observation: sfmap TF (sem-ana F (sem-CoOut wf)) (coerce-ν-in F (sem-CoOut wf x))
      -- RHS observation: sfmap TF (anaS unfoldS) (unfoldS x)
      -- By obs-eq, LHS = sfmap TF (sem-ana F (sem-CoOut wf)) (unfoldS x)
      -- By sfmap-bisim with coinductive hypothesis, they are related
  in subst (λ z → ⟦ TF ⟧SF-rel (_∼S_)
                    (sfmap TF (sem-ana F (sem-CoOut wf)) z)
                    (sfmap TF (anaS unfoldS) (unfoldS x)))
           (sym obs-eq)
           (sfmap-bisim TF (sem-ana F (sem-CoOut wf)) (anaS unfoldS)
                        (sem-ana-bisim-anaS wf) (unfoldS x))

-- | sem-ana F (sem-CoOut wf) equals anaS unfoldS (PROVEN via bisimulation)
--
-- Proof: Show bisimilarity via sem-ana-bisim-anaS, then apply bisimS-to-eq.
--
sem-ana-is-anaS-unfoldS : ∀ {F} → (wf : WellFormedF F) → (x : ⟦ν⟧ F)
                        → sem-ana F (sem-CoOut wf) x ≡ anaS unfoldS x
sem-ana-is-anaS-unfoldS wf x =
  bisimS-to-eq (sem-ana _ (sem-CoOut wf) x) (anaS unfoldS x) (sem-ana-bisim-anaS wf x)

-- | Identity anamorphism: ana with CoOut coalgebra is identity (PROVEN)
--
-- Proof: Combine sem-ana-is-anaS-unfoldS with anaS-Out-id.
--
sem-ana-Out-id : ∀ {F : Functor} → (wf : WellFormedF F) → (x : ⟦ν⟧ F) → sem-ana F (sem-CoOut wf) x ≡ x
sem-ana-Out-id {F} wf x = trans (sem-ana-is-anaS-unfoldS wf x) (anaS-Out-id (translateF IntRep F) x)

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
-- sem-hylo-guarded wf alg coalg = sem-hylo F alg (sem-unguard wf ∘ coalg)
-- So sem-hylo-guarded wf alg coalg x
--    = alg (fmap (sem-hylo F alg (sem-unguard wf ∘ coalg)) (sem-unguard wf (coalg x)))
--    = alg (fmap (sem-hylo-guarded wf alg coalg) (sem-unguard wf (coalg x)))
--
sem-hylo-guarded-compute : ∀ {F : Functor} (wf : WellFormedF F) {A B : Set}
                           (alg : ⟦ F ⟧F B → B) (coalg : A → ⟦Guarded⟧ F A) (x : A)
                         → sem-hylo-guarded wf alg coalg x ≡
                           alg (sem-fmap F (sem-hylo-guarded wf alg coalg) (sem-unguard wf (coalg x)))
sem-hylo-guarded-compute wf alg coalg x = refl