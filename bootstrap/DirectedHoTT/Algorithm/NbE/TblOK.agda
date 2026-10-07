-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT — ★ A SOUND VALUE TABLE (PLAN-REF, E4).
--
-- The evaluator forces `vref d` to the table's entry d.  That is sound
-- exactly when every entry is CLOSED (scope is preserved through δ) and
-- READS as a term convertible with `ref d` — the reference unfolded and
-- evaluated.  A name beyond the table is its own value: closed, and read
-- as itself.  `Algorithm/NbETable` builds the table of a
-- signature and proves it sound, along the telescope.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( KSig )
open import DirectedHoTT.Algorithm.NbE.Value using ( Tbl )
module DirectedHoTT.Algorithm.NbE.TblOK (𝒮 : KSig) (tbl : Tbl) where
open import Agda.Builtin.Nat using () renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax using ( Cx; ref )
open import DirectedHoTT.Spec.Reduction 𝒮 using ( _≅_ )
open import normalizer.Syntax.Types using ( _×_; _,_ )
open import DirectedHoTT.Algorithm.NbE tbl using ( Lv; ⌊_⌋; lookupT )
open import DirectedHoTT.Algorithm.NbERead using ( TblSc )

TblReads : Set
TblReads = ∀ {Δ : Cx} (L : Lv Δ) (d : ℕ) → ref {Δ} d ≅ ⌊ lookupT tbl d ⌋ L

TblOK : Set
TblOK = TblSc tbl × TblReads

tblSc : TblOK → TblSc tbl
tblSc (c , _) = c

tblReads : TblOK → TblReads
tblReads (_ , r) = r
