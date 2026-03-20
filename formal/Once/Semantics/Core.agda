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

⟦_⟧ : Type → Set
⟦ Unit ⟧         = ⊤
⟦ Void ⟧         = ⊥
⟦ A * B ⟧        = ⟦ A ⟧ × ⟦ B ⟧
⟦ A + B ⟧        = ⟦ A ⟧ ⊎ ⟦ B ⟧
⟦ A ⇒[ _ ] B ⟧   = ⟦ A ⟧ → ⟦ B ⟧
⟦ Eff A B ⟧      = ⟦ A ⟧ → ⟦ B ⟧
⟦ Fix F ⟧        = ⟦Fix⟧ ⟦ F ⟧
⟦ Int ⟧          = IntRep
⟦ Float ⟧        = AgdaFloat
⟦ Str ⟧          = String
⟦ Buffer ⟧       = String
⟦ TVar _ ⟧       = ⊤

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
