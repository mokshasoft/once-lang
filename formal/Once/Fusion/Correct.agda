-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Fusion.Correct
--
-- Correctness proofs for fusion rules.
--
-- NOTE: Due to OCP-0003, fusion-compose is currently just plain
-- composition (g ∘ f), so correctness is trivial (refl).
------------------------------------------------------------------------

module Once.Fusion.Correct where

open import Once.Type
open import Once.CCC.IR
open import Once.Semantics.IR using (⟦_⟧; eval′)
open import Once.Fusion
open import Once.Postulates using (extensionality)

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans)

------------------------------------------------------------------------
-- Correctness of fusion-compose
--
-- Currently fusion-compose is just (g ∘ f), so this is trivially refl.
------------------------------------------------------------------------

fusion-compose-correct : ∀ {A B C} (g : IR B C) (f : IR A B) (x : ⟦ A ⟧)
                       → eval′ (fusion-compose g f) x ≡ eval′ (g ∘ f) x
fusion-compose-correct g f x = refl

------------------------------------------------------------------------
-- Correctness of fusion-once (Postulated)
------------------------------------------------------------------------

postulate
  fusion-once-correct : ∀ {A B} (f : IR A B) (x : ⟦ A ⟧)
                      → eval′ (fusion-once f) x ≡ eval′ f x

------------------------------------------------------------------------
-- Correctness of bounded iteration
------------------------------------------------------------------------

fusion-n-correct : ∀ {A B} (n : ℕ) (f : IR A B) (x : ⟦ A ⟧)
                 → eval′ (fusion-n n f) x ≡ eval′ f x
fusion-n-correct zero f x = refl
fusion-n-correct (suc n) f x =
  trans (fusion-n-correct n (fusion-once f) x)
        (fusion-once-correct f x)

------------------------------------------------------------------------
-- Main theorem: fusion preserves semantics
------------------------------------------------------------------------

fusion-correct : ∀ {A B} (f : IR A B) (x : ⟦ A ⟧)
               → eval′ (fusion f) x ≡ eval′ f x
fusion-correct f x = fusion-n-correct 10 f x