-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT — ★ A SIGNATURE WRITTEN IN THE SURFACE, checked by
--                      evaluation.  (PLAN-BIDI S7, `Algorithm/SigBuild`)
--
-- `Examples/Signature`'s Σ₃, plus a fourth entry, written WITHOUT the
-- core's annotations and without a single hand-written derivation: the
-- well-formedness proof `wf` is the checker's output, `fromJust wfSig _`.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.SigBuild where
open import normalizer.Syntax.Types using ( ⊥ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax using ( ε; vz )
open import DirectedHoTT.Spec.Annotated using ( ATm; base )
open import DirectedHoTT.Algorithm.Surface
open import DirectedHoTT.Metatheory.Signature using ( WfSig; consistencyˢ )
import DirectedHoTT.Spec.TypingA as TA

pattern v₀ = var vz

tys : ℕ → STy ε
tys 0 = Π Nat Nat
tys 1 = U
tys 2 = El (ref 1)
tys 3 = Π Nat Nat
tys _ = Unit

tms : ℕ → STm ε
tms 0 = lam □ᵀ (nsuc v₀)                                   -- suc′
tms 1 = ⌜Nat⌝                                              -- N
tms 2 = app (ref 0) nzero                                  -- one : El N
tms 3 = lam □ᵀ (natrec □ᵀ nzero (nsuc (nsuc v₀)) v₀)       -- double
tms _ = unit

open import DirectedHoTT.Algorithm.SigBuild using ( module SigBuild )
open SigBuild 4 tys tms 100

-- ★ the whole signature's well-formedness: the checker's output
wf : WfSig S
wf = fromJust wfSig _

consistent : {t : ATm ε} → TA._⊢ᴬ_∷_ S TA.◇ᴬ t base → ⊥
consistent = consistencyˢ S wf
