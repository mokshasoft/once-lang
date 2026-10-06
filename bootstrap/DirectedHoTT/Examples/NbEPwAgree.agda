-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★ THE CORE'S Pw IS THE KNOT'S, normal form for
-- normal form.
--
-- `Examples/PwCore.#PwD` applied to an open index has exactly the normal
-- form of the Knot's generated description `Knot/Pw.PwF.DF` (whose fibre
-- method, convoy, weakening and `⌜Tm⌝` are Agda-opaque, hence the
-- `unfolding`).  Run by `Algorithm/NbE`; with `nbe-sound` this is a
-- certified CONVERSION — the step that lets the Knot's Pw be the core's.
--
-- Negative control: the Knot's description at a different index variable.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.NbEPwAgree where
open import normalizer.Syntax.Types using ( _≡_; refl; ⊤; tt; ⊥ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import Agda.Builtin.Bool using ( Bool; true; false )
open import DirectedHoTT.Spec.Syntax using ( ε; _∙; vz; vs )
open import DirectedHoTT.Spec.Signature using ( Sig )
import DirectedHoTT.Spec.Syntax as R
open import DirectedHoTT.Algorithm.NbE using ( nbe )
open import DirectedHoTT.Algorithm.DecEq using ( Dec; _≟Tm_; yes; no )
import DirectedHoTT.Examples.PwCore as P
open import DirectedHoTT.Examples.Knot.RedIx using ( CP )
open import DirectedHoTT.Examples.Knot.Pw using ( module PwF )
import DirectedHoTT.Examples.Knot.Ren as KR
import DirectedHoTT.Examples.Knot.JudgeIx as JI

private
  ⟪_⟫ : {Γ : R.Cx} → ℕ → R.RTm Γ
  ⟪ d ⟫ = R.ref d (Sig.body P.S d)

  Γ₂ = (ε ∙) ∙

  IsYes : {P : Set} → Dec P → Set
  IsYes (yes _) = ⊤
  IsYes (no _)  = ⊥
  fromYes : {P : Set} (p : Dec P) → IsYes p → P
  fromYes (yes p) _ = p

  differs : R.RTm Γ₂ → R.RTm Γ₂ → Bool
  differs a b with a ≟Tm b
  ... | yes _ = false
  ... | no _  = true

  -- the description applied to an index variable
  core lib : R.RTm Γ₂ → R.RTm Γ₂
  core x = R.app ⟪ P.#PwD ⟫ x
  lib  x = R.app PwF.DF x

opaque
  unfolding PwF.FIBMₒ CP KR.wk JI.⌜Tm⌝

  -- ★ the core's description of Pw IS the Knot's
  pw-is-pw : nbe 100000 (core (R.var vz)) ≡ nbe 100000 (lib (R.var vz))
  pw-is-pw = fromYes (nbe 100000 (core (R.var vz)) ≟Tm nbe 100000 (lib (R.var vz))) tt

  pw-is-pw✗ : differs (nbe 100000 (core (R.var vz))) (nbe 100000 (lib (R.var (vs vz)))) ≡ true
  pw-is-pw✗ = refl
