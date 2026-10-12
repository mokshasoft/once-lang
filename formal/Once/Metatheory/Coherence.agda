-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Coherence — the core meaning is a function of the judgment
-- (`Spec.Core.Coherence`, plan 0.116).
--
-- SCAFFOLD: POSTULATED, to be discharged by plan 0.116 phase D1. It is
-- postulated only now that it is believed TRUE: before plan 0.116 B a `let` at
-- quantity `Zero` dropped an effectful right-hand side while the same judgment
-- at `One` ran it, so the statement was false. The positions where it fails
-- would be the non-syntax-directed rules (`⊢sub-use`, `⊢sub-eff`, `⊢coerce`)
-- and the quantities `let`, `case` and `lam` hide; the proof goes by induction
-- on the two derivations, normalising those rules (plan 0.116 §3 D1).
--
-- Nothing proves anything FROM it: it discharges the Spec's claim on the apex.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Core.PolyTy using (Sig)
open import Once.Spec.Contract using (ISig)

module Once.Metatheory.Coherence {Fs : ISig} {s : ℕ} (S : Sig Fs s) where

open import Once.Spec.Core.Coherence S using (Coherence)

postulate
  coherence : Coherence
