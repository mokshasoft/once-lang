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
open import Once.CCC.Eval using (eval)
open import Once.Semantics.Machine using (⟦_⟧; sem-fst; sem-snd; sem-pair)

------------------------------------------------------------------------
-- Basic Evaluation Laws
------------------------------------------------------------------------

eval-id : ∀ {A} (x : ⟦ A ⟧) → eval id x ≡ x
eval-id ps x = refl

eval-fst : ∀ {A B} (x : ⟦ A * B ⟧) → eval fst x ≡ sem-fst x
eval-fst ps x = refl

eval-snd : ∀ {A B} (x : ⟦ A * B ⟧) → eval snd x ≡ sem-snd x
eval-snd ps x = refl

eval-compose : ∀ {A B C} (f : IR A B) (g : IR B C) (x : ⟦ A ⟧) →
  eval (g ∘ f) x ≡ eval g (eval f x)
eval-compose ps f g x = refl

eval-pair : ∀ {A B C} (f : IR A B) (g : IR A C) (m : AllocMode) (x : ⟦ A ⟧) →
  eval (⟨ f , g ⟩ m) x ≡ sem-pair (eval f x) (eval g x)
eval-pair ps f g m x = refl

eval-terminal : ∀ {A} (x : ⟦ A ⟧) → eval terminal x ≡ tt
eval-terminal ps x = refl

------------------------------------------------------------------------
-- AllocMode Independence
------------------------------------------------------------------------

alloc-mode-independent-pair : ∀ {A B C} (f : IR A B) (g : IR A C) (m₁ m₂ : AllocMode) (x : ⟦ A ⟧) →
  eval (⟨ f , g ⟩ m₁) x ≡ eval (⟨ f , g ⟩ m₂) x
alloc-mode-independent-pair ps f g m₁ m₂ x = refl

alloc-mode-independent-inl : ∀ {A B} (m₁ m₂ : AllocMode) (x : ⟦ A ⟧) →
  eval (inl {A} {B} m₁) x ≡ eval (inl {A} {B} m₂) x
alloc-mode-independent-inl ps m₁ m₂ x = refl

alloc-mode-independent-inr : ∀ {A B} (m₁ m₂ : AllocMode) (x : ⟦ B ⟧) →
  eval (inr {A} {B} m₁) x ≡ eval (inr {A} {B} m₂) x
alloc-mode-independent-inr ps m₁ m₂ x = refl

alloc-mode-independent-curry : ∀ {A B C q} (f : IR (A * B) C) (m₁ m₂ : AllocMode) (x : ⟦ A ⟧) →
  eval (curry {k = k} f m₁) x ≡ eval (curry {k = k} f m₂) x
alloc-mode-independent-curry ps f m₁ m₂ x = refl

------------------------------------------------------------------------
-- OCP-0003: Recursion Scheme Evaluation Laws
------------------------------------------------------------------------

-- Import recursion scheme semantic operations
open import Once.Semantics.Machine
  using (sem-In; sem-cata; sem-para; sem-CoOut; sem-ana; sem-hylo;
         coerce-functor; coerce-functor⁻¹)
open import Once.Type using (Functor; μ-type; ν-type; ⟦_⟧T)
open import Once.Functor.Translate using (WellFormedF)

-- | In evaluation: wraps into μ-type
eval-In : ∀ {F} (wf : WellFormedF F) (m : AllocMode) (x : ⟦ ⟦ F ⟧T (μ-type F) ⟧) →
  eval (In {F} wf m) x ≡ sem-In F (coerce-functor F (μ-type F) x)
eval-In ps wf m x = refl

-- | Cata evaluation: folds with algebra
eval-Cata : ∀ {F A} (wf : WellFormedF F) (alg : IR (⟦ F ⟧T A) A) (x : ⟦ μ-type F ⟧) →
  eval (Cata {F} wf alg) x ≡ sem-cata wf (λ fa → eval alg (coerce-functor⁻¹ F A fa)) x
eval-Cata ps wf alg x = refl

-- | Para evaluation: paramorphism - fold with access to original substructure
eval-Para : ∀ {F A} (wf : WellFormedF F) (alg : IR (⟦ F ⟧T (μ-type F * A)) A) (x : ⟦ μ-type F ⟧) →
  eval (Para {F} wf alg) x ≡ sem-para wf (λ fx → eval alg (coerce-functor⁻¹ F (μ-type F * A) fx)) x
eval-Para ps wf alg x = refl

-- | Out evaluation: observes ν-type
eval-Out : ∀ {F} (wf : WellFormedF F) (x : ⟦ ν-type F ⟧) →
  eval (Out {F} wf) x ≡ coerce-functor⁻¹ F (ν-type F) (sem-CoOut wf x)
eval-Out ps wf x = refl

-- | Ana evaluation: unfolds with coalgebra
-- OCP-0003: productivity follows from IR totality, no GuardedT needed
eval-Ana : ∀ {F A} (wf : WellFormedF F) (coalg : IR A (⟦ F ⟧T A)) (x : ⟦ A ⟧) →
  eval (Ana {F} wf coalg) x ≡ sem-ana F (λ a → coerce-functor F A (eval coalg a)) x
eval-Ana ps wf coalg x = refl

-- | Hylo evaluation law
--
-- OCP-0003: Hylo is now based on Fuse, removing the need for TerminatesOn.
-- Termination is guaranteed by requiring μG as input - structural recursion
-- on the well-founded μG type ensures termination.
--
-- sem-hylo alg coalg = sem-fuse alg (coalg ∘ sem-In)
--
-- No TERMINATING pragma needed on sem-hylo - it delegates to sem-fuse.

-- | AllocMode independence for In
alloc-mode-independent-In : ∀ {F} (wf : WellFormedF F) (m₁ m₂ : AllocMode) (x : ⟦ ⟦ F ⟧T (μ-type F) ⟧) →
  eval (In {F} wf m₁) x ≡ eval (In {F} wf m₂) x
alloc-mode-independent-In ps wf m₁ m₂ x = refl

------------------------------------------------------------------------
-- OCP-0003: Lambek Isomorphism Laws
--
-- By Lambek's Lemma:
--   - In and out-μ are inverses (μ-type)
--   - Out and in-ν are inverses (ν-type)
------------------------------------------------------------------------

-- Import semantic Lambek laws
open import Once.Semantics.Machine
  using (sem-Out-In; sem-In-Out; sem-CoOut-CoIn; sem-CoIn-CoOut;
         coerce-round-trip; coerce⁻¹-round-trip; sem-Out; sem-CoIn)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

-- | out-μ ∘ In = id (Lambek, μ-type, one direction)
--
-- Proof: eval (out-μ ∘ In) x
--      = coerce-functor⁻¹ (sem-Out (sem-In (coerce-functor x)))
--      = coerce-functor⁻¹ (coerce-functor x)   [by sem-Out-In]
--      = x                                      [by coerce-round-trip]
--
eval-out-μ-In : ∀ {F} (wf : WellFormedF F) (m : AllocMode) (x : ⟦ ⟦ F ⟧T (μ-type F) ⟧) →
  eval (out-μ wf ∘ In wf m) x ≡ x
eval-out-μ-In ps {F} wf m x =
  trans (cong (coerce-functor⁻¹ F (μ-type F)) (sem-Out-In wf (coerce-functor F (μ-type F) x)))
        (coerce-round-trip F (μ-type F) x)

-- | In ∘ out-μ = id (Lambek, μ-type, other direction)
--
-- Proof: eval (In ∘ out-μ) x
--      = sem-In (coerce-functor (coerce-functor⁻¹ (sem-Out x)))
--      = sem-In (sem-Out x)                    [by coerce⁻¹-round-trip]
--      = x                                      [by sem-In-Out]
--
eval-In-out-μ : ∀ {F} (wf : WellFormedF F) (m : AllocMode) (x : ⟦ μ-type F ⟧) →
  eval (In wf m ∘ out-μ wf) x ≡ x
eval-In-out-μ ps {F} wf m x =
  trans (cong (sem-In F) (coerce⁻¹-round-trip F (μ-type F) (sem-Out wf x)))
        (sem-In-Out wf x)

-- | Out ∘ in-ν = id (Lambek, ν-type, one direction)
--
-- Proof: eval (Out ∘ in-ν) x
--      = coerce-functor⁻¹ (sem-CoOut (sem-CoIn (coerce-functor x)))
--      = coerce-functor⁻¹ (coerce-functor x)   [by sem-CoOut-CoIn]
--      = x                                      [by coerce-round-trip]
--
eval-Out-in-ν : ∀ {F} (wf : WellFormedF F) (m : AllocMode) (x : ⟦ ⟦ F ⟧T (ν-type F) ⟧) →
  eval (Out wf ∘ in-ν wf m) x ≡ x
eval-Out-in-ν ps {F} wf m x =
  trans (cong (coerce-functor⁻¹ F (ν-type F)) (sem-CoOut-CoIn wf (coerce-functor F (ν-type F) x)))
        (coerce-round-trip F (ν-type F) x)

-- | in-ν ∘ Out = id (Lambek, ν-type, other direction)
--
-- Proof: eval (in-ν ∘ Out) x
--      = sem-CoIn (coerce-functor (coerce-functor⁻¹ (sem-CoOut x)))
--      = sem-CoIn (sem-CoOut x)                [by coerce⁻¹-round-trip]
--      = x                                      [by sem-CoIn-CoOut]
--
eval-in-ν-Out : ∀ {F} (wf : WellFormedF F) (m : AllocMode) (x : ⟦ ν-type F ⟧) →
  eval (in-ν wf m ∘ Out wf) x ≡ x
eval-in-ν-Out ps {F} wf m x =
  trans (cong (sem-CoIn F) (coerce⁻¹-round-trip F (ν-type F) (sem-CoOut wf x)))
        (sem-CoIn-CoOut wf x)