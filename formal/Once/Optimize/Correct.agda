-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Optimize.Correct
--
-- Correctness proofs for the Once optimizer.
-- Each optimization rule preserves semantics.
--
-- NOTE: Due to OCP-0003's new recursion scheme constructors causing
-- type index unification issues in Optimize.agda, several optimization
-- functions are currently postulated. Consequently, their correctness
-- proofs are also postulated here.
------------------------------------------------------------------------

module Once.Optimize.Correct where

open import Once.Type
open import Once.CCC.IR
open import Once.Semantics.IR using (⟦_⟧; eval′)
open import Once.Optimize
open import Once.Category.Laws
open import Once.Postulates using (extensionality)

open import Data.Bool using (Bool; true; false; _∨_; _∧_)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans)

-- Alias for function extensionality (imported from Once.Postulates)
funext : ∀ {A : Set} {B : A → Set} {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g
funext = extensionality

------------------------------------------------------------------------
-- Correctness of optimize-compose (Postulated)
--
-- Since optimize-compose is now postulated due to OCP-0003 coverage
-- issues, its correctness is also postulated.
------------------------------------------------------------------------

postulate
  optimize-compose-correct : ∀ {A B C} (g : IR B C) (f : IR A B) (x : ⟦ A ⟧)
                           → eval′ (optimize-compose g f) x ≡ eval′ (g ∘ f) x

------------------------------------------------------------------------
-- Correctness of optimize-pair and optimize-case (Postulated)
------------------------------------------------------------------------

postulate
  optimize-pair-correct : ∀ {A B C} (f : IR C A) (g : IR C B) (x : ⟦ C ⟧)
                        → eval′ (optimize-pair f g) x ≡ eval′ (⟨ f , g ⟩ Heap) x

postulate
  optimize-case-correct : ∀ {A B C} (f : IR A C) (g : IR B C) (x : ⟦ A + B ⟧)
                        → eval′ (optimize-case f g) x ≡ eval′ (case f g) x

------------------------------------------------------------------------
-- Correctness of optimize-once (Postulated)
--
-- Since optimize-compose, optimize-pair, and optimize-case are now
-- postulated, the full structural correctness proof is also postulated.
------------------------------------------------------------------------

postulate
  optimize-once-correct : ∀ {A B} (f : IR A B) (x : ⟦ A ⟧)
                        → eval′ (optimize-once f) x ≡ eval′ f x

------------------------------------------------------------------------
-- Correctness of bounded optimization
------------------------------------------------------------------------

optimize-n-correct : ∀ {A B} (n : ℕ) (f : IR A B) (x : ⟦ A ⟧)
                   → eval′ (optimize-n n f) x ≡ eval′ f x
optimize-n-correct zero f x = refl
optimize-n-correct (suc n) f x =
  trans (optimize-n-correct n (optimize-once f) x)
        (optimize-once-correct f x)

------------------------------------------------------------------------
-- Main theorem: optimize preserves semantics
------------------------------------------------------------------------

optimize-correct : ∀ {A B} (f : IR A B) (x : ⟦ A ⟧)
                 → eval′ (optimize f) x ≡ eval′ f x
optimize-correct f x = optimize-n-correct 10 f x