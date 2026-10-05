-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★ A SIGNATURE EXTENDED IN ANOTHER MODULE.
--
-- `Examples/SigCore`'s signature (22 entries, checked there) is extended
-- here by two entries that refer into it.  The base's proof `SigCore.wf`
-- is REUSED: `WfSig (S ▸ˢ e)` is `WfSig S × EntryWf S e` definitionally
-- (`Metatheory/Signature`), so only the new entries are checked — this
-- module costs what its own entries cost, not SigCore's 40 s.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.SigExtendTest where
open import normalizer.Syntax.Types using ( _≡_; refl )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax using ( ε; vz; vs )
import DirectedHoTT.Spec.Syntax as R
open import DirectedHoTT.Spec.Signature using ( Sig )
open import DirectedHoTT.Metatheory.Signature using ( WfSig )
open import DirectedHoTT.Algorithm.Surface
open import DirectedHoTT.Algorithm.SigBuild using ( module SigExtend )
open import DirectedHoTT.Algorithm.NbE using ( nbe )
open import DirectedHoTT.Lib.NatNum using ( num )
import DirectedHoTT.Examples.SigCore as Base

-- references are ABSOLUTE (the base has 22 entries); the tables below are
-- indexed by the new entry's position in this segment
pattern #add    = 1
#double #four : ℕ
#double = 22
#four   = 23

interleaved mutual
  tys : ℕ → STy ε
  tms : ℕ → STm ε
  -- double n = add n n (an entry of the BASE)
  tys 0 = Π Nat Nat
  tms 0 = lam □ᵀ (app (app (ref #add) (var vz)) (var vz))
  -- four = double 2 (an entry of THIS segment)
  tys 1 = Nat
  tms 1 = app (ref #double) (nsuc (nsuc nzero))
  tys _ = Unit
  tms _ = unit

open SigExtend Base.S Base.abody Base.wf 2 tys tms 1000 public

-- ★ only the two new entries are checked; the base's proof is reused
wf : WfSig S
wf = fromJust wfSig _

-- and the extended signature computes: four = 4
⟪_⟫ : {Γ : R.Cx} → ℕ → R.RTm Γ
⟪ d ⟫ = R.ref d (Sig.body S d)

four : nbe {ε} 100000 ⟪ #four ⟫ ≡ num 4
four = refl
