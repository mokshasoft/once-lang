-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · Lib — SIZES SHRINK UNDER THE PEELS (PLAN-FAITHFUL F6).
--
-- A decoder whose subject does not shrink (a conversion's `ctrn`, a
-- typing's `⊢conv`) recurses on FUEL: the inhabitant's size `sz`.  Every
-- peel of a payload — a node's payload, a pair's halves — is smaller.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.Size where

open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Metatheory.Canonicity using ( sz; _≤_; ≤-refl; ≤-trans; ≤-suc; un≤; ≤+ˡ; ≤+ʳ )
open import DirectedHoTT.Lib.Sugar using ( tag; conₗ )

-- the payload of a node is smaller than the node
szp : (k : ℕ) (p : RTm ε) {f : ℕ} → sz (conₗ k p) ≤ suc f → sz p ≤ f
szp k p h = ≤-trans (≤-trans (≤+ʳ (sz (tag {ε} k)) (sz p)) (≤-suc ≤-refl)) (un≤ h)

-- …and so are a pair's halves
szˡ : (a r : RTm ε) {f : ℕ} → sz (pair a r) ≤ suc f → sz a ≤ f
szˡ a r h = ≤-trans (≤+ˡ (sz a) (sz r)) (un≤ h)

szʳ : (a r : RTm ε) {f : ℕ} → sz (pair a r) ≤ suc f → sz r ≤ f
szʳ a r h = ≤-trans (≤+ʳ (sz a) (sz r)) (un≤ h)
