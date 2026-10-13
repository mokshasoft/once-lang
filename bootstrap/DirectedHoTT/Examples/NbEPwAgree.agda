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
open import DirectedHoTT.Spec.Syntax using ( Defs )
open import DirectedHoTT.Spec.SigWf using ( WfK )
open import DirectedHoTT.Spec.SigExtend using ( _⊑ᴰ_ )
import DirectedHoTT.Examples.PredsCore as Core₀
module DirectedHoTT.Examples.NbEPwAgree (𝒮 : Defs) (wf : WfK 𝒮) (inCore : Core₀.Kc ⊑ᴰ 𝒮) where
open import normalizer.Syntax.Types using ( _≡_; refl )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import Agda.Builtin.Bool using ( Bool; true; false )
open import DirectedHoTT.Spec.Syntax using ( ε; _∙; vz; vs; unit )
import DirectedHoTT.Spec.Syntax as R
open import DirectedHoTT.Algorithm.DecEq using ( Dec; _≟Tm_; yes; no )
import DirectedHoTT.Examples.PwCore as P
-- evaluated at the core's table (the core's term refers into it)
open import DirectedHoTT.Algorithm.NbETable using ( mkTbl )
open import DirectedHoTT.Algorithm.NbE (mkTbl P.Kc) using ( nbe )
-- ★ the Knot read over ANY signature containing the core (a parameter: at
--   the concrete `Core₀.Kc`, applying the Knot's modules alone took 81 s /
--   ~5 GB against 8 s here; its codes are syntax, so they reduce alike)
import DirectedHoTT.Metatheory.Entries as Entries
open import DirectedHoTT.Examples.Knot.RedIx 𝒮 wf using ( CP )
open import DirectedHoTT.Examples.Knot.Pw 𝒮 wf inCore using ( module PwF )
import DirectedHoTT.Examples.Knot.Ren 𝒮 wf as KR
import DirectedHoTT.Examples.Knot.JudgeIx 𝒮 wf as JI
import DirectedHoTT.Lib.Syn 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf) as LS

private
  ⟪_⟫ : {Γ : R.Cx} → ℕ → R.RTm Γ
  ⟪ d ⟫ = R.ref d

  Γ₂ = (ε ∙) ∙


  differs : R.RTm Γ₂ → R.RTm Γ₂ → Bool
  differs a b with a ≟Tm b
  ... | yes _ = false
  ... | no _  = true

  -- equality FROM the Boolean: `differs a b ≡ false` by `refl` runs in
  --   ~16 s; the same decision through `IsYes`/`fromYes` at the concrete
  --   normal forms went past the memory cap (2026-10-09)
  same : (a b : R.RTm Γ₂) → differs a b ≡ false → a ≡ b
  same a b e with a ≟Tm b
  ... | yes p = p
  same a b () | no _

  -- the description applied to an index variable
  core lib : R.RTm Γ₂ → R.RTm Γ₂
  core x = R.app ⟪ P.#PwD ⟫ x
  lib  x = R.app (PwF.DF unit) x

opaque
  unfolding PwF.FIBMₒ CP KR.wk JI.⌜Tm⌝ LS.SK LS.SD

  -- ★ the core's description of Pw IS the Knot's
  pw-is-pw : nbe 100000 (core (R.var vz)) ≡ nbe 100000 (lib (R.var vz))
  pw-is-pw = same _ _ refl

  pw-is-pw✗ : differs (nbe 100000 (core (R.var vz))) (nbe 100000 (lib (R.var (vs vz)))) ≡ true
  pw-is-pw✗ = refl
