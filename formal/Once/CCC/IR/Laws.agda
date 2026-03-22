-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.IR.Laws
--
-- Evaluation laws and semantic properties for IR.
------------------------------------------------------------------------

module Once.CCC.IR.Laws where

open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.CCC.IR
open import Once.CCC.Eval using (PrimSem; eval)
open import Once.Semantics.Machine using (⟦_⟧; sem-fst; sem-snd; sem-pair)

------------------------------------------------------------------------
-- Basic Evaluation Laws
------------------------------------------------------------------------

eval-id : ∀ (ps : PrimSem) {A} (x : ⟦ A ⟧) → eval ps id x ≡ x
eval-id ps x = refl

eval-fst : ∀ (ps : PrimSem) {A B} (x : ⟦ A * B ⟧) → eval ps fst x ≡ sem-fst x
eval-fst ps x = refl

eval-snd : ∀ (ps : PrimSem) {A B} (x : ⟦ A * B ⟧) → eval ps snd x ≡ sem-snd x
eval-snd ps x = refl

eval-compose : ∀ (ps : PrimSem) {A B C} (f : IR A B) (g : IR B C) (x : ⟦ A ⟧) →
  eval ps (g ∘ f) x ≡ eval ps g (eval ps f x)
eval-compose ps f g x = refl

eval-pair : ∀ (ps : PrimSem) {A B C} (f : IR A B) (g : IR A C) (m : AllocMode) (x : ⟦ A ⟧) →
  eval ps (⟨ f , g ⟩ m) x ≡ sem-pair (eval ps f x) (eval ps g x)
eval-pair ps f g m x = refl

eval-terminal : ∀ (ps : PrimSem) {A} (x : ⟦ A ⟧) → eval ps terminal x ≡ tt
eval-terminal ps x = refl

------------------------------------------------------------------------
-- AllocMode Independence
------------------------------------------------------------------------

alloc-mode-independent-pair : ∀ (ps : PrimSem) {A B C} (f : IR A B) (g : IR A C) (m₁ m₂ : AllocMode) (x : ⟦ A ⟧) →
  eval ps (⟨ f , g ⟩ m₁) x ≡ eval ps (⟨ f , g ⟩ m₂) x
alloc-mode-independent-pair ps f g m₁ m₂ x = refl

alloc-mode-independent-inl : ∀ (ps : PrimSem) {A B} (m₁ m₂ : AllocMode) (x : ⟦ A ⟧) →
  eval ps (inl {A} {B} m₁) x ≡ eval ps (inl {A} {B} m₂) x
alloc-mode-independent-inl ps m₁ m₂ x = refl

alloc-mode-independent-inr : ∀ (ps : PrimSem) {A B} (m₁ m₂ : AllocMode) (x : ⟦ B ⟧) →
  eval ps (inr {A} {B} m₁) x ≡ eval ps (inr {A} {B} m₂) x
alloc-mode-independent-inr ps m₁ m₂ x = refl

alloc-mode-independent-curry : ∀ (ps : PrimSem) {A B C q} (f : IR (A * B) C) (m₁ m₂ : AllocMode) (x : ⟦ A ⟧) →
  eval ps (curry {q = q} f m₁) x ≡ eval ps (curry {q = q} f m₂) x
alloc-mode-independent-curry ps f m₁ m₂ x = refl

------------------------------------------------------------------------
-- OCP-0003: Recursion Scheme Evaluation Laws
------------------------------------------------------------------------

-- Import recursion scheme semantic operations
open import Once.Semantics.Machine
  using (sem-In; sem-cata; sem-CoOut; sem-ana; sem-hylo;
         coerce-functor; coerce-functor⁻¹)
open import Once.Type using (Functor; μ-type; ν-type; ⟦_⟧T)

-- | In evaluation: wraps into μ-type
eval-In : ∀ (ps : PrimSem) {F} (m : AllocMode) (x : ⟦ ⟦ F ⟧T (μ-type F) ⟧) →
  eval ps (In {F} m) x ≡ sem-In F (coerce-functor F (μ-type F) x)
eval-In ps m x = refl

-- | Cata evaluation: folds with algebra
eval-Cata : ∀ (ps : PrimSem) {F A} (alg : IR (⟦ F ⟧T A) A) (x : ⟦ μ-type F ⟧) →
  eval ps (Cata {F} {A} alg) x ≡ sem-cata F (λ fa → eval ps alg (coerce-functor⁻¹ F A fa)) x
eval-Cata ps alg x = refl

-- | Out evaluation: observes ν-type
eval-Out : ∀ (ps : PrimSem) {F} (x : ⟦ ν-type F ⟧) →
  eval ps (Out {F}) x ≡ coerce-functor⁻¹ F (ν-type F) (sem-CoOut F x)
eval-Out ps x = refl

-- | Ana evaluation: unfolds with coalgebra
eval-Ana : ∀ (ps : PrimSem) {F A} (coalg : IR A (⟦ F ⟧T A)) (x : ⟦ A ⟧) →
  eval ps (Ana {F} {A} coalg) x ≡ sem-ana F (λ a → coerce-functor F A (eval ps coalg a)) x
eval-Ana ps coalg x = refl

-- | Hylo evaluation: fused cata ∘ ana
eval-Hylo : ∀ (ps : PrimSem) {F A B} (alg : IR (⟦ F ⟧T B) B) (coalg : IR A (⟦ F ⟧T A)) (x : ⟦ A ⟧) →
  eval ps (Hylo {F} {A} {B} alg coalg) x ≡
    sem-hylo F (λ fb → eval ps alg (coerce-functor⁻¹ F B fb))
              (λ a → coerce-functor F A (eval ps coalg a)) x
eval-Hylo ps alg coalg x = refl

-- | AllocMode independence for In
alloc-mode-independent-In : ∀ (ps : PrimSem) {F} (m₁ m₂ : AllocMode) (x : ⟦ ⟦ F ⟧T (μ-type F) ⟧) →
  eval ps (In {F} m₁) x ≡ eval ps (In {F} m₂) x
alloc-mode-independent-In ps m₁ m₂ x = refl