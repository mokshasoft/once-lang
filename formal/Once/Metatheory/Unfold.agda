{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Unfold — forcing an unfold runs the coalgebra and
-- unfolds the rest, at each grade, as trees up to bisimilarity
-- (`unfold-out≈`; `Spec.Metatheory.Recursion.unfold-out` is its `EqM`
-- form, `Once.Metatheory.Recursion`).
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature; call)

module Once.Metatheory.Unfold (Σ : Signature) where

open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Once.Spec.Grade using (pure; act; eff⁺; eff)
open import Once.Spec.Polynomial using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF; sfmap)
open import Once.Spec.Effect Σ
open import Once.Spec.Domain Σ
  using (anaM; anaP; mapP; anaA; treeA; mapA; anaE; treeE; stepE; mapE; anaG; rootG; treeG; stepG; mapG)

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

  mapE≡ : ∀ {X} (c : X → T∞ (⟦ G ⟧SF X)) H (l : ⟦ H ⟧SF X) → mapE G H c l ≡ sfmap H (anaE G c) l
  mapE≡ c (SK B)     l        = refl
  mapE≡ c SId        l        = refl
  mapE≡ c (H₁ S⊕ H₂) (inj₁ x) = cong inj₁ (mapE≡ c H₁ x)
  mapE≡ c (H₁ S⊕ H₂) (inj₂ y) = cong inj₂ (mapE≡ c H₂ y)
  mapE≡ c (H₁ S⊗ H₂) (x , y)  = cong₂ _,_ (mapE≡ c H₁ x) (mapE≡ c H₂ y)

  mapG≡ : ∀ {X} (c : X → T⁺ (⟦ G ⟧SF X)) H (l : ⟦ H ⟧SF X) → mapG G H c l ≡ sfmap H (anaG G c) l
  mapG≡ c (SK B)     l        = refl
  mapG≡ c SId        l        = refl
  mapG≡ c (H₁ S⊕ H₂) (inj₁ x) = cong inj₁ (mapG≡ c H₁ x)
  mapG≡ c (H₁ S⊕ H₂) (inj₂ y) = cong inj₂ (mapG≡ c H₂ y)
  mapG≡ c (H₁ S⊗ H₂) (x , y)  = cong₂ _,_ (mapG≡ c H₁ x) (mapG≡ c H₂ y)

  doneEq : ∀ {X} {x y : X} → x ≡ y → StepEq {X = X} {Y = T∞ X} _≈_ (done x) (done y)
  doneEq refl = done≈

  treeE≈ : ∀ {X} (c : X → T∞ (⟦ G ⟧SF X)) (t : T∞ (⟦ G ⟧SF X))
         → treeE G c t ≈ (t >>=∞ λ l → return∞ (sfmap G (anaE G c) l))
  treeE≈S : ∀ {X} (c : X → T∞ (⟦ G ⟧SF X)) (s : Step (⟦ G ⟧SF X) (T∞ (⟦ G ⟧SF X)))
          → StepEq _≈_ (stepE G c s) (bindStep s λ l → return∞ (sfmap G (anaE G c) l))
  force≈ (treeE≈ c t) = treeE≈S c (force t)
  treeE≈S c (done l)            = doneEq (mapE≡ c G l)
  treeE≈S c (node (call o a k)) = node≈ λ b → treeE≈ c (k b)

  treeG≈ : ∀ {X} (c : X → T⁺ (⟦ G ⟧SF X)) (t : T∞ (⟦ G ⟧SF X))
         → treeG G c t ≈ (t >>=∞ λ l → return∞ (sfmap G (anaG G c) l))
  treeG≈S : ∀ {X} (c : X → T⁺ (⟦ G ⟧SF X)) (s : Step (⟦ G ⟧SF X) (T∞ (⟦ G ⟧SF X)))
          → StepEq _≈_ (stepG G c s) (bindStep s λ l → return∞ (sfmap G (anaG G c) l))
  force≈ (treeG≈ c t) = treeG≈S c (force t)
  treeG≈S c (done l)            = doneEq (mapG≡ c G l)
  treeG≈S c (node (call o a k)) = node≈ λ b → treeG≈ c (k b)

  rootG≈ : ∀ {X} (c : X → T⁺ (⟦ G ⟧SF X)) (r : T⁺ (⟦ G ⟧SF X))
         → forget⁺ (rootG G c r) ≈ forget⁺ (r >>=⁺ λ l → return∞ (sfmap G (anaG G c) l))
  force≈ (rootG≈ c (call⁺ (call o a k))) = node≈ λ b → treeG≈ c (k b)

  treeA≈ : ∀ {X} (c : X → T (⟦ G ⟧SF X)) (t : T (⟦ G ⟧SF X))
         → embed (treeA G c t) ≈ embed (t >>=T λ l → returnT (sfmap G (anaA G c) l))
  force≈ (treeA≈ c (roll (done l)))            = doneEq (mapA≡ c G l)
  force≈ (treeA≈ c (roll (node (call o a k)))) = node≈ λ b → treeA≈ c (k b)

  -- Forcing an unfold, as a tree: the coalgebra, then the unfold at the
  -- recursive positions.
  unfold-out≈ : ∀ π {X : Set} (c : X → M π (⟦ G ⟧SF X)) (x : X)
              → toT∞ π (outν (anaM π G c x)) ≈ toT∞ π (fmap π (sfmap G (anaM π G c)) (c x))
  force≈ (unfold-out≈ pure c x) = doneEq (mapP≡ c G (c x))
  unfold-out≈ act  c x = treeA≈ c (c x)
  unfold-out≈ eff⁺ c x = rootG≈ c (c x)
  unfold-out≈ eff  c x = treeE≈ c (c x)
