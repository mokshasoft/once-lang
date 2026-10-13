-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★ THE CORE'S SIDE CONDITIONS ARE THE KNOT'S,
-- normal form for normal form (PLAN-BIDI §3g, P6).
--
-- `Examples/PredsCore`: the shared index `#PJ` is the Knot's `StkAₘ.J`,
-- and each family's description applied to an open index has exactly the
-- normal form of the Knot's generated one (`Knot/Preds.<F>F.DF`, whose
-- fibre method is Agda-opaque, hence the `unfolding`).  Run by
-- `Algorithm/NbE`; with `nbe-sound` each is a certified CONVERSION.
--
-- Negative controls: the Knot's description at a different index variable.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs )
open import DirectedHoTT.Spec.SigWf using ( WfK )
open import DirectedHoTT.Spec.SigExtend using ( _⊑ᴰ_ )
import DirectedHoTT.Examples.PredsCore as Core₀
module DirectedHoTT.Examples.NbEPredsAgree (𝒮 : Defs) (wf : WfK 𝒮) (core : Core₀.Kc ⊑ᴰ 𝒮) where
open import normalizer.Syntax.Types using ( _≡_; refl )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import Agda.Builtin.Bool using ( Bool; true; false )
open import DirectedHoTT.Spec.Syntax using ( ε; _∙; vz; vs; unit )
import DirectedHoTT.Spec.Syntax as R
open import DirectedHoTT.Algorithm.DecEq using ( Dec; _≟Tm_; yes; no )
import DirectedHoTT.Examples.PredsCore as P
-- evaluated at the core's table (the core's term refers into it)
open import DirectedHoTT.Algorithm.NbETable using ( mkTbl )
open import DirectedHoTT.Algorithm.NbE (mkTbl P.Kc) using ( nbe )
-- ★ the Knot read over ANY signature containing the core (a parameter: at
--   the concrete `Core₀.Kc`, applying the Knot's modules alone took 81 s /
--   ~5 GB against 8 s here; its codes are syntax, so they reduce alike)
import DirectedHoTT.Metatheory.Entries as Entries
open import DirectedHoTT.Examples.Knot.Preds 𝒮 wf core using ( module StkAₘ; module NNCF; module StkAF; module StkCF; module FlatF; ⌜StkA⌝; ⌜StkC⌝ )
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

  -- a description applied to an index variable
  _·ᵛ_ : R.RTm Γ₂ → R.RTm Γ₂ → R.RTm Γ₂
  d ·ᵛ x = R.app d x

opaque
  unfolding NNCF.FIBMₒ StkAF.FIBMₒ StkCF.FIBMₒ FlatF.FIBMₒ LS.SK LS.SD ⌜StkA⌝ ⌜StkC⌝

  -- ★ the shared index IS the Knot's
  index-is-index : nbe 100000 (⟪_⟫ {Γ₂} P.#PJ) ≡ nbe 100000 (StkAₘ.J {Γ₂})
  index-is-index = same _ _ refl

  -- ★ the core's description of NNC IS the Knot's (control: another index variable)
  nnc-is-nnc : nbe 100000 (⟪ P.#NNCD ⟫ ·ᵛ R.var vz) ≡ nbe 100000 (NNCF.DF unit ·ᵛ R.var vz)
  nnc-is-nnc = same _ _ refl

  nnc-is-nnc✗ : differs (nbe 100000 (⟪ P.#NNCD ⟫ ·ᵛ R.var vz)) (nbe 100000 (NNCF.DF unit ·ᵛ R.var (vs vz))) ≡ true
  nnc-is-nnc✗ = refl

  -- ★ the core's description of StkA IS the Knot's (control: another index variable)
  stkA-is-stkA : nbe 100000 (⟪ P.#StkAD ⟫ ·ᵛ R.var vz) ≡ nbe 100000 (StkAF.DF unit ·ᵛ R.var vz)
  stkA-is-stkA = same _ _ refl

  stkA-is-stkA✗ : differs (nbe 100000 (⟪ P.#StkAD ⟫ ·ᵛ R.var vz)) (nbe 100000 (StkAF.DF unit ·ᵛ R.var (vs vz))) ≡ true
  stkA-is-stkA✗ = refl

  -- ★ the core's description of StkC IS the Knot's (control: another index variable)
  stkC-is-stkC : nbe 100000 (⟪ P.#StkCD ⟫ ·ᵛ R.var vz) ≡ nbe 100000 (StkCF.DF unit ·ᵛ R.var vz)
  stkC-is-stkC = same _ _ refl

  stkC-is-stkC✗ : differs (nbe 100000 (⟪ P.#StkCD ⟫ ·ᵛ R.var vz)) (nbe 100000 (StkCF.DF unit ·ᵛ R.var (vs vz))) ≡ true
  stkC-is-stkC✗ = refl

  -- ★ the core's description of Flat IS the Knot's (control: another index variable)
  flat-is-flat : nbe 100000 (⟪ P.#FlatD ⟫ ·ᵛ R.var vz) ≡ nbe 100000 (FlatF.DF unit ·ᵛ R.var vz)
  flat-is-flat = same _ _ refl

  flat-is-flat✗ : differs (nbe 100000 (⟪ P.#FlatD ⟫ ·ᵛ R.var vz)) (nbe 100000 (FlatF.DF unit ·ᵛ R.var (vs vz))) ≡ true
  flat-is-flat✗ = refl
