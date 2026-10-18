{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.OneName — one declaration per name (`Spec.Signature.OneName`):
-- two entries named alike are one entry, at one type.
------------------------------------------------------------------------

module Once.Metatheory.OneName where

open import Data.Empty using (⊥-elim)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.AllPairs using (_∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Once.Spec.Signature using (Signature; OneName; _∶_; module Decl)

decl-unique : ∀ {Σ : Signature} → OneName Σ → ∀ {c t t′} → (c ∶ t) ∈ Σ → (c ∶ t′) ∈ Σ → t ≡ t′
decl-unique (_ ∷ _) (here refl) (here refl) = refl
decl-unique (all ∷ _) (here refl) (there q) = ⊥-elim (All.lookup all (∈-map⁺ Decl.name q) refl)
decl-unique (all ∷ _) (there p) (here refl) = ⊥-elim (All.lookup all (∈-map⁺ Decl.name p) refl)
decl-unique (_ ∷ rest) (there p) (there q) = decl-unique rest p q

mem-unique : ∀ {Σ : Signature} → OneName Σ → ∀ {d} (p q : d ∈ Σ) → p ≡ q
mem-unique (_ ∷ _) (here refl) (here refl) = refl
mem-unique (all ∷ _) (here refl) (there q) = ⊥-elim (All.lookup all (∈-map⁺ Decl.name q) refl)
mem-unique (all ∷ _) (there p) (here refl) = ⊥-elim (All.lookup all (∈-map⁺ Decl.name p) refl)
mem-unique (_ ∷ rest) (there p) (there q) = cong there (mem-unique rest p q)
