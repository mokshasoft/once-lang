-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Semantics.Core
--
-- Core semantic interpretation, parameterized by integer representation.
--
-- This module provides:
--   - ⟦_⟧: Type → Set (semantic interpretation)
--   - ⟦Fix⟧: Fixed point wrapper
--   - sem-*: Semantic operations (products, sums, fixed points)
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
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type

------------------------------------------------------------------------
-- Fixed Point Wrapper
------------------------------------------------------------------------

record ⟦Fix⟧ (A : Set) : Set where
  constructor wrap
  field unwrap : A

open ⟦Fix⟧ public

------------------------------------------------------------------------
-- Semantic Interpretation
--
-- Functions are plain Agda functions (not Closure records).
-- Int is parameterized (ℕ for machine, ℤ for proofs).
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Polynomial Functor Semantics (Postulated)
--
-- We use postulates to avoid strict positivity issues that arise from
-- mutual definition with ⟦_⟧ (which contains function types).
--
-- These postulates are instantiated properly in Once.SPF which provides
-- the actual μ and ν fixed points with proven laws.
------------------------------------------------------------------------

-- | Semantic interpretation of μ-type (initial algebra)
postulate
  ⟦μ⟧ : Functor → Set

-- | Semantic interpretation of ν-type (final coalgebra)
postulate
  ⟦ν⟧ : Functor → Set

⟦_⟧ : Type → Set
⟦ Unit ⟧         = ⊤
⟦ Void ⟧         = ⊥
⟦ A * B ⟧        = ⟦ A ⟧ × ⟦ B ⟧
⟦ A + B ⟧        = ⟦ A ⟧ ⊎ ⟦ B ⟧
⟦ A ⇒[ _ ] B ⟧   = ⟦ A ⟧ → ⟦ B ⟧
⟦ Eff A B ⟧      = ⟦ A ⟧ → ⟦ B ⟧
⟦ Fix F ⟧        = ⟦Fix⟧ ⟦ F ⟧
⟦ μ-type F ⟧     = ⟦μ⟧ F
⟦ ν-type F ⟧     = ⟦ν⟧ F
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
--
sem-functor-coherence : ∀ F X → ⟦ ⟦ F ⟧T X ⟧ ≡ ⟦ F ⟧F ⟦ X ⟧
sem-functor-coherence (K A) X = refl
sem-functor-coherence Id X = refl
sem-functor-coherence (F ⊕ G) X rewrite sem-functor-coherence F X
                                      | sem-functor-coherence G X = refl
sem-functor-coherence (F ⊗ G) X rewrite sem-functor-coherence F X
                                      | sem-functor-coherence G X = refl

-- | Coercion from Type-level to Set-level functor application
--
-- Uses the coherence proof via subst.
--
coerce-functor : ∀ F X → ⟦ ⟦ F ⟧T X ⟧ → ⟦ F ⟧F ⟦ X ⟧
coerce-functor F X = subst (λ z → z) (sem-functor-coherence F X)
  where
    open import Relation.Binary.PropositionalEquality using (subst)

-- | Inverse coercion
coerce-functor⁻¹ : ∀ F X → ⟦ F ⟧F ⟦ X ⟧ → ⟦ ⟦ F ⟧T X ⟧
coerce-functor⁻¹ F X = subst (λ z → z) (sym (sem-functor-coherence F X))
  where
    open import Relation.Binary.PropositionalEquality using (subst; sym)

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

-- Fixed point operations
sem-fold : ∀ {F} → ⟦ F ⟧ → ⟦ Fix F ⟧
sem-fold x = wrap x

sem-unfold : ∀ {F} → ⟦ Fix F ⟧ → ⟦ F ⟧
sem-unfold (wrap x) = x

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

sem-unfold-fold : ∀ {F} (x : ⟦ F ⟧) → sem-unfold (sem-fold x) ≡ x
sem-unfold-fold x = refl

sem-fold-unfold : ∀ {F} (x : ⟦ Fix F ⟧) → sem-fold (sem-unfold x) ≡ x
sem-fold-unfold (wrap x) = refl

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

-- | In: F(μF) → μF (algebra)
postulate
  sem-In : ∀ (F : Functor) → ⟦ F ⟧F (⟦μ⟧ F) → ⟦μ⟧ F

-- | Out: μF → F(μF) (destructor, inverse of In)
postulate
  sem-Out : ∀ (F : Functor) → ⟦μ⟧ F → ⟦ F ⟧F (⟦μ⟧ F)

-- | Catamorphism: given algebra F(A) → A, fold μF → A
postulate
  sem-cata : ∀ (F : Functor) {A : Set} → (⟦ F ⟧F A → A) → ⟦μ⟧ F → A

-- | CoOut: νF → F(νF) (observation)
postulate
  sem-CoOut : ∀ (F : Functor) → ⟦ν⟧ F → ⟦ F ⟧F (⟦ν⟧ F)

-- | CoIn: F(νF) → νF (coalgebra)
postulate
  sem-CoIn : ∀ (F : Functor) → ⟦ F ⟧F (⟦ν⟧ F) → ⟦ν⟧ F

-- | Anamorphism: given coalgebra A → F(A), unfold A → νF
postulate
  sem-ana : ∀ (F : Functor) {A : Set} → (A → ⟦ F ⟧F A) → A → ⟦ν⟧ F

-- | Hylomorphism: fused cata ∘ ana, computed directly
-- Semantically: hylo alg coalg = cata alg ∘ ana coalg
-- But computed without building intermediate structure
postulate
  sem-hylo : ∀ (F : Functor) {A B : Set}
           → (⟦ F ⟧F B → B)  -- algebra
           → (A → ⟦ F ⟧F A)  -- coalgebra
           → A → B

------------------------------------------------------------------------
-- Recursion Scheme Laws (Postulated)
--
-- These capture the key properties of initial algebras and final
-- coalgebras. They are implemented properly in Once.SPF.
------------------------------------------------------------------------

-- | In and Out are inverses (Lambek's Lemma, one direction)
postulate
  sem-Out-In : ∀ (F : Functor) (x : ⟦ F ⟧F (⟦μ⟧ F)) → sem-Out F (sem-In F x) ≡ x

-- | In and Out are inverses (Lambek's Lemma, other direction)
postulate
  sem-In-Out : ∀ (F : Functor) (x : ⟦μ⟧ F) → sem-In F (sem-Out F x) ≡ x

-- | Catamorphism computation law
postulate
  sem-cata-compute : ∀ (F : Functor) {A : Set} (alg : ⟦ F ⟧F A → A) (x : ⟦ F ⟧F (⟦μ⟧ F))
                   → sem-cata F alg (sem-In F x) ≡ alg (sem-fmap F (sem-cata F alg) x)