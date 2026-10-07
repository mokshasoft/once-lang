-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT — ★ A WELL-FORMED SIGNATURE (PLAN-REF, D082).
--
-- The signature is the definition context, and this is its context
-- formation: entry m is typed using only the names before it (its
-- PREFIX, `Spec/Typing 𝒮 m`) — its declared type well-formed, its body
-- inhabiting it.  Acyclicity is what makes δ terminate: a body typed with
-- every name could refer to itself.
--
-- `Metatheory/Entries` turns it into what the metatheory reads: every
-- entry typed at any larger bound (`SigOK`), and every reference
-- reducible (`RefsOK`).
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Spec.SigWf where
open import normalizer.Syntax.Types using ( ⊤; _×_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax using ( Defs )
import DirectedHoTT.Spec.Typing as Ty

-- entries 0 … m-1, each typed in its prefix
WfUpTo : Defs → ℕ → Set
WfUpTo 𝒮 zero    = ⊤
WfUpTo 𝒮 (suc m) = WfUpTo 𝒮 m × Ty.EntryOK 𝒮 m m

-- the whole signature
WfK : Defs → Set
WfK 𝒮 = WfUpTo 𝒮 (Defs.size 𝒮)
