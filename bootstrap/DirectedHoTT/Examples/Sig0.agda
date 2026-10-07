-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — the EMPTY signature, for examples that define
-- nothing (PLAN-REF, D082).  The kernel, its metatheory and its libraries
-- are parameterised by the signature; an example that uses no reference
-- instantiates them here, so its tests compute on a concrete signature.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Sig0 where
open import normalizer.Syntax.Types using ( tt )
open import Agda.Builtin.Nat using () renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax using ( Defs; ∅ᴷ )
open import DirectedHoTT.Spec.SigWf using ( WfK )
import DirectedHoTT.Spec.Typing as Ty
import DirectedHoTT.Metatheory.Entries as Entries
import DirectedHoTT.Metatheory.Fundamental.Semantic as Sem

-- the empty signature is well-formed (no entries)
wf₀ : WfK ∅ᴷ
wf₀ = tt

ok₀ : Ty.EntriesOK ∅ᴷ 0
ok₀ = Entries.sigOK ∅ᴷ 0 wf₀

refs₀ : Sem.RefsOK ∅ᴷ 0
refs₀ = Entries.refsOK ∅ᴷ 0 (λ p → p) wf₀

-- the empty signature's value table (NbE), and its soundness
open import DirectedHoTT.Algorithm.NbE.Value using ( Tbl )
open import DirectedHoTT.Algorithm.NbETable using ( mkTbl; mkTbl-ok )
import DirectedHoTT.Algorithm.NbE.TblOK as TO

tbl₀ : Tbl
tbl₀ = mkTbl ∅ᴷ

tok₀ : TO.TblOK ∅ᴷ tbl₀
tok₀ = mkTbl-ok ∅ᴷ
