-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★ THE CORE'S TRAVERSAL IS THE KNOT'S, normal form
-- for normal form.
--
-- `Examples/SigMeth.#trav` at the Knot's signature and the renaming kit,
-- on an OPEN term at an open depth, has exactly the normal form of the
-- Knot's weakening `Knot/Ren.wk` (the Lib's `SynTrav`, generated per
-- signature): the core's method is written as the Lib's `methAt` is, so
-- the two meet without an η or a commuting conversion.  Run by
-- `Algorithm/NbE`; with `nbe-sound` this is a certified CONVERSION, the
-- step a Knot family needs to move onto the core (PLAN-BIDI §3g).
--
-- Negative control: the core's traversal at the wrong sort.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.NbETravAgree where
open import normalizer.Syntax.Types using ( _≡_; refl; ⊤; tt; ⊥ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import Agda.Builtin.List using ( List; []; _∷_ )
open import Agda.Builtin.Bool using ( Bool; true; false )
open import DirectedHoTT.Spec.Syntax using ( ε; _∙; vz; vs )
import DirectedHoTT.Spec.Syntax as R
open import DirectedHoTT.Lib.NatNum using ( num )
open import DirectedHoTT.Lib.Sugar using ( tag )
open import DirectedHoTT.Algorithm.DecEq using ( Dec; _≟Tm_; yes; no )
open import DirectedHoTT.Examples.SigCore using ( #KΣ )
open import DirectedHoTT.Examples.SigMeth using ( #trav; #rVF; #rWK; #rV0; #rNK )
open import DirectedHoTT.Examples.SigCoreEval using ( nfᴺ; ⟪_⟫; _⋆_ )
import DirectedHoTT.Examples.Knot.Ren as KR

private
  Γ₂ = (ε ∙) ∙
  -- an open depth and an open term
  d t : R.RTm Γ₂
  d = R.var (vs vz)
  t = R.var vz

  -- the core's weakening at sort s: the renaming kit, environment `fsuc`
  wkCore : ℕ → R.RTm Γ₂
  wkCore s = ⟪ #trav ⟫ ⋆ (num 2 ∷ tag 1 ∷ ⟪ #KΣ ⟫ ∷ ⟪ #rVF ⟫ ∷ ⟪ #rWK ⟫ ∷ ⟪ #rV0 ⟫ ∷ ⟪ #rNK ⟫
                         ∷ tag s ∷ d ∷ t ∷ R.nsuc d ∷ R.lam (R.fsuc (R.var vz)) ∷ [])

  IsYes : {P : Set} → Dec P → Set
  IsYes (yes _) = ⊤
  IsYes (no _)  = ⊥
  fromYes : {P : Set} (p : Dec P) → IsYes p → P
  fromYes (yes p) _ = p

  differs : R.RTm Γ₂ → R.RTm Γ₂ → Bool
  differs a b with a ≟Tm b
  ... | yes _ = false
  ... | no _  = true

opaque
  unfolding KR.wk

  -- ★ the core's traversal at the Knot's signature IS the Knot's weakening
  trav-is-wk : nfᴺ (wkCore 1) ≡ nfᴺ (KR.wk 1 d t)
  trav-is-wk = fromYes (nfᴺ (wkCore 1) ≟Tm nfᴺ (KR.wk 1 d t)) tt

  trav-is-wk✗ : differs (nfᴺ (wkCore 0)) (nfᴺ (KR.wk 1 d t)) ≡ true
  trav-is-wk✗ = refl
