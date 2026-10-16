{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Unfold — forcing an unfold runs the coalgebra and
-- unfolds the rest, at each grade a coalgebra may have (at most `act`), up to
-- bisimilarity
-- (`unfold-out≈`; `Spec.Metatheory.Recursion.unfold-out` is its `EqM`
-- form, `Once.Metatheory.Recursion`).
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature; call)

module Once.Metatheory.Unfold (Σ : Signature) where

open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Once.Spec.Grade using (pure; act; eff; _⊑π_; ⊑-pa; ⊑-act)
open import Once.Spec.Polynomial using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF; sfmap)
open import Once.Spec.Effect Σ
open import Once.Spec.Domain Σ using (anaM; anaP; mapP; anaA; treeA; mapA)

open T∞ using (force)
open _≈_ using (force≈)
open νM using (outν)

module Unfold (G : SFunctor) where
  mapP≡ : ∀ {X} (c : X → ⟦ G ⟧SF X) H (l : ⟦ H ⟧SF X) → mapP G H c l ≡ sfmap H (anaP G c) l
  mapP≡ c (SK B)     l        = refl
  mapP≡ c SId        l        = refl
  mapP≡ c (H₁ S⊕ H₂) (inj₁ x) = cong inj₁ (mapP≡ c H₁ x)
  mapP≡ c (H₁ S⊕ H₂) (inj₂ y) = cong inj₂ (mapP≡ c H₂ y)
  mapP≡ c (H₁ S⊗ H₂) (x , y)  = cong₂ _,_ (mapP≡ c H₁ x) (mapP≡ c H₂ y)

  mapA≡ : ∀ {X} (c : X → T (⟦ G ⟧SF X)) H (l : ⟦ H ⟧SF X) → mapA G H c l ≡ sfmap H (anaA G c) l
  mapA≡ c (SK B)     l        = refl
  mapA≡ c SId        l        = refl
  mapA≡ c (H₁ S⊕ H₂) (inj₁ x) = cong inj₁ (mapA≡ c H₁ x)
  mapA≡ c (H₁ S⊕ H₂) (inj₂ y) = cong inj₂ (mapA≡ c H₂ y)
  mapA≡ c (H₁ S⊗ H₂) (x , y)  = cong₂ _,_ (mapA≡ c H₁ x) (mapA≡ c H₂ y)

  returnEq : ∀ {X} {x y : X} → x ≡ y → BlockEq {X = X} _≈_ (roll (done (inj₁ x))) (roll (done (inj₁ y)))
  returnEq refl = return≈

  treeA≈  : ∀ {X} (c : X → T (⟦ G ⟧SF X)) (t : T (⟦ G ⟧SF X))
          → embed (treeA G c t) ≈ embed (t >>=T λ l → returnT (sfmap G (anaA G c) l))
  treeA≈B : ∀ {X} (c : X → T (⟦ G ⟧SF X)) (t : T (⟦ G ⟧SF X))
          → BlockEq _≈_ (mapT inj₁ (treeA G c t)) (mapT inj₁ (t >>=T λ l → returnT (sfmap G (anaA G c) l)))
  force≈ (treeA≈ c t) = treeA≈B c t
  treeA≈B c (roll (done l))            = returnEq (mapA≡ c G l)
  treeA≈B c (roll (node (call o a k))) = node≈ λ b → treeA≈B c (k b)

  -- Forcing an unfold, in `T∞`: the coalgebra, then the unfold at the
  -- recursive positions.
  unfold-out≈ : ∀ {π} (g : π ⊑π act) {X : Set} (c : X → M π (⟦ G ⟧SF X)) (x : X)
              → toT∞ π (outν (anaM g G c x)) ≈ toT∞ π (fmap π (sfmap G (anaM g G c)) (c x))
  force≈ (unfold-out≈ ⊑-pa c x) = returnEq (mapP≡ c G (c x))
  unfold-out≈ ⊑-act c x = treeA≈ c (c x)
