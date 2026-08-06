-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Certified — THE SHIPPED ARTEFACT: correctness ∧ well-behavedness.
--
-- `Once.Adequacy.CorrectCompiler` is the MINIMAL, do-not-edit correctness
-- spec (soundness ⟺ completeness against the independent meaning). It is
-- intentionally kept free of "nice" engineering properties (determinism,
-- totality, error-message shape, algebraic identities): those are not part
-- of the mathematical notion of correctness and must never be smuggled into
-- `correct` (see the mandate in `Once.Adequacy`).
--
-- But we still want those properties GUARANTEED and drift-proof. This module
-- conjoins the two concerns as a single product whose inhabitant cannot be
-- constructed unless BOTH hold:
--   • `correctness` — the apex `CorrectCompiler` (`Once.Compiler`);
--   • `typechecker` — the `VerifiedTypeChecker` bundle (determinism ∧ totality
--     ∧ error-preservation ∧ frontend identities, stated over the REAL
--     `inferElab`/`checkElab`, so it cannot drift from the live elaborator).
--
-- Because both fields are stated over the actual entry points, a regression in
-- either makes `once-certified` fail to type-check — the drift that let
-- `ErrorProofs` rot silently (it had lost its only consumer in the Plan 0.49
-- relational-spec pivot) can no longer happen once the build gates this module.
--
-- Room for future per-layer bundles (parser well-formedness, optimizer
-- preservation, backend refinement) as additional fields — each its own record
-- in its own layer, conjoined here, never folded into `correct`.
------------------------------------------------------------------------

-- Plan 0.63 (D089): parameterised by the DEFINITION'S identity, which keys its
-- labels. `o` is constant for a whole definition, so it belongs on the module
-- rather than on every lemma — which is what keeps the statements below
-- UNCHANGED: the emitter is imported APPLIED, so each call site reads as before.
open import Once.CanonicalName using (CanonicalName)

open import Data.Nat using (ℕ)

import Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds as RB

module Once.Certified
  (o : CanonicalName) (program-bound : ℕ)
  (x86-64-heap-room : RB.HeapRoom o) (x86-64-stack-room : RB.StackRoom o) where

-- P5 (OCP-0006): the correctness criterion is consumed THROUGH the spec
-- door — `Once.Spec` is on the certified path, not an island.
open import Once.Spec using (CorrectCompiler)
open import Once.Compiler o program-bound x86-64-heap-room x86-64-stack-room using (once-compiler)
open import Once.TypeCheck.Verified using (VerifiedTypeChecker; verifiedTypeChecker)

record CertifiedBuild : Set₁ where
  field
    correctness : CorrectCompiler       -- soundness + completeness (the minimal claim)
    typechecker : VerifiedTypeChecker    -- determinism ∧ totality ∧ errors ∧ identities

once-certified : CertifiedBuild
once-certified = record
  { correctness = once-compiler
  ; typechecker = verifiedTypeChecker
  }
