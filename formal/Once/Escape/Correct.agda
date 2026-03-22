-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Escape.Correct
--
-- Correctness proofs for escape analysis.
--
-- Key insight: AllocMode is semantically transparent - it is explicitly
-- ignored in the eval function (Once/Semantics.agda). Therefore, all
-- escape analysis rewrites that only change AllocMode are trivially
-- correct by refl.
--
-- NOTE: Due to OCP-0003's escape-compose being postulated, the
-- correctness proofs are also postulated here.
------------------------------------------------------------------------

module Once.Escape.Correct where

open import Once.Type
open import Once.CCC.IR
open import Once.Semantics.IR using (⟦_⟧; eval′)
open import Once.Escape
open import Once.Postulates using (extensionality)

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans)

------------------------------------------------------------------------
-- Correctness of escape-compose (Postulated)
--
-- Since escape-compose is now postulated due to OCP-0003 coverage
-- issues, its correctness is also postulated.
------------------------------------------------------------------------

postulate
  escape-compose-correct : ∀ {A B C} (g : IR B C) (f : IR A B) (x : ⟦ A ⟧)
                         → eval′ (escape-compose g f) x ≡ eval′ (g ∘ f) x

------------------------------------------------------------------------
-- Correctness of escape-once (Postulated)
------------------------------------------------------------------------

postulate
  escape-once-correct : ∀ {A B} (f : IR A B) (x : ⟦ A ⟧)
                      → eval′ (escape-once f) x ≡ eval′ f x

------------------------------------------------------------------------
-- Correctness of bounded iteration
------------------------------------------------------------------------

escape-n-correct : ∀ {A B} (n : ℕ) (f : IR A B) (x : ⟦ A ⟧)
                 → eval′ (escape-n n f) x ≡ eval′ f x
escape-n-correct zero f x = refl
escape-n-correct (suc n) f x =
  trans (escape-n-correct n (escape-once f) x)
        (escape-once-correct f x)

------------------------------------------------------------------------
-- Main theorem: escape analysis preserves semantics
------------------------------------------------------------------------

escape-correct : ∀ {A B} (f : IR A B) (x : ⟦ A ⟧)
               → eval′ (escape f) x ≡ eval′ f x
escape-correct f x = escape-n-correct 10 f x