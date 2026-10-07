-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — `depth` FOR THE SCOPED SYNTAX: the same fold as
-- `Examples/Scoped.size` at a different ALGEBRA (`Lib/TelFold.depthAlg`).
--
-- ★ That is the claim the fold was factored out to support: two measures
--   over the same description differ in an algebra, not in any
--   per-constructor work.  And `depth` is not a toy alternative to
--   `size` — where a constructor BRANCHES the two disagree (`app`'s size
--   SUMS its children, its depth MAXES them), and for a syntax the depth
--   is usually the measure you want.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.ScopedDepth where
import DirectedHoTT.Examples.Lib0 as Lib0
open import DirectedHoTT.Spec.Syntax using ( ∅ᴷ )
open import DirectedHoTT.Examples.Sig0 using ( wf₀; ok₀; refs₀; tbl₀; tok₀ )
open import DirectedHoTT.Spec.Syntax using ( Cx; RTm; Nat; El; ⌜Nat⌝; ielim )
open Lib0.Spec-Typing using ( Ctx; ⌊_⌋; _⊢_∷_; ty-Nat; ⊢⌜Nat⌝; ⊢ielim )
open Lib0.Lib-Sugar using ( methₗ )
open Lib0.Lib-TelFold using ( depthAlg; foldMs; ⊢foldE )
open import DirectedHoTT.Examples.Scoped using ( TmTs; TmD; ⊢TmD; TmOK; Tm )

dpTm : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
dpTm n t = ielim TmD n (methₗ (foldMs depthAlg TmTs)) t

⊢dpTm : {Γ : Ctx} {n t : RTm ⌊ Γ ⌋} →
        Γ ⊢ n ∷ El ⌜Nat⌝ → Γ ⊢ t ∷ Tm n → Γ ⊢ dpTm n t ∷ Nat
⊢dpTm dn dt = ⊢ielim ⊢⌜Nat⌝ ⊢TmD ty-Nat (⊢foldE depthAlg ⊢⌜Nat⌝ TmOK) dn dt
