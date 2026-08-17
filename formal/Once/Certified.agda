-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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
import Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds as RBr
import Once.Adequacy.ArchCorrectness.X86-32.ResourceBounds as RB32

module Once.Certified
  (o : CanonicalName) (program-bound : ℕ)
  (x86-64-heap-room : RB.HeapRoom o) (x86-64-stack-room : RB.StackRoom o)
  (x86-64-call-room : RB.CallRoom o)
  (x86-64-reg-range : RB.RegRange o)
  (x86-64-scratch-dec-guarded : RB.ScratchDecGuarded o)
  (x86-64-addr-no-wrap : RB.AddrNoWrap o)
  (x86-64-lit-fits : RB.LitFits o)
  -- Plan 0.65: riscv64's three, threaded the same way (D087). They could not
  -- be stated until riscv64 had a correspondence to condition them on; now
  -- they are, the apex constrains their shape instead of G2 inventing it.
  (riscv64-heap-room : RBr.HeapRoom o) (riscv64-stack-room : RBr.StackRoom o)
  (riscv64-call-room : RBr.CallRoom o)
  (riscv64-reg-range : RBr.RegRange o)
  (riscv64-scratch-dec-guarded : RBr.ScratchDecGuarded o)
  (riscv64-slot-addr-no-wrap : RBr.SlotAddrNoWrap o)
  (riscv64-addr-no-wrap : RBr.AddrNoWrap o)
  (riscv64-lit-fits : RBr.LitFits o)
  -- …and x86-32's seven (plan 0.66 X3): the arch had none while its simulation
  -- was a whole-cloth postulate, which is precisely what a deleted apex
  -- postulate makes visible — the resources a running program needs.
  (x86-32-heap-room : RB32.HeapRoom o) (x86-32-stack-room : RB32.StackRoom o)
  (x86-32-call-room : RB32.CallRoom o)
  (x86-32-reg-range : RB32.RegRange o)
  (x86-32-scratch-dec-guarded : RB32.ScratchDecGuarded o)
  (x86-32-addr-no-wrap : RB32.AddrNoWrap o)
  (x86-32-lit-fits : RB32.LitFits o) where

-- P5 (OCP-0006): the correctness criterion is consumed THROUGH the spec
-- door — `Once.Spec` is on the certified path, not an island.
open import Once.Spec using (CorrectCompiler)
open import Once.Compiler o program-bound x86-64-heap-room x86-64-stack-room x86-64-call-room
       x86-64-reg-range x86-64-scratch-dec-guarded x86-64-addr-no-wrap x86-64-lit-fits
       riscv64-heap-room riscv64-stack-room riscv64-call-room
       riscv64-reg-range riscv64-scratch-dec-guarded riscv64-slot-addr-no-wrap
       riscv64-addr-no-wrap riscv64-lit-fits
       x86-32-heap-room x86-32-stack-room x86-32-call-room
       x86-32-reg-range x86-32-scratch-dec-guarded x86-32-addr-no-wrap x86-32-lit-fits using (once-compiler)
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
