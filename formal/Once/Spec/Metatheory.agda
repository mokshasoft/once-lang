-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Metatheory — WHAT THE LANGUAGE PROMISES ABOUT ITSELF (D304).
--
-- A metatheorem is a claim about the Spec ALONE: it mentions no compiler. If
-- one cannot be proved, the LANGUAGE is wrong, not the compiler — D276 made
-- the grades affine precisely so that substitution is typed. So the
-- statements are part of the Spec, read with the definition they constrain;
-- the proofs are not (D140): they live under `Once.Metatheory`, which may
-- import only the Spec and its semantic domain, never the compiler
-- (`scripts/metatheory-gate.sh`). `Once.Certified` carries the proofs, so
-- each statement is on the apex and goes red when the Spec moves.
--
-- Today, for every signature of definitions `S`, the core's TERM MODEL
-- (`Once.Spec.Core.TermModel`): substitution of terms is typed (`subst-⊢`),
-- a pure `let` means its substitution (`let-β`, referential transparency),
-- and substitution of types is typed (`ty-subst-⊢`, D303).
------------------------------------------------------------------------

module Once.Spec.Metatheory where

open import Data.Nat using (ℕ)
open import Once.Spec.Contract using (ISig)
open import Once.Spec.Core.PolyTy using (Sig)
open import Once.Spec.Core.TermModel using (TermModel) public

Metatheory : Set
Metatheory = ∀ {Fs : ISig} {s : ℕ} (S : Sig Fs s) → TermModel S
