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
--   • `correctness` — the apex `CorrectCompiler`, on the Spec (`once-compiler`);
--   • `typechecker` — the `VerifiedTypeChecker` bundle (determinism ∧ totality
--     ∧ error-preservation ∧ frontend identities, stated over the REAL
--     `inferElab`/`checkElab`, so it cannot drift from the live elaborator).
--   • `nonvacuous` — a model of each assumption whose type is not obviously
--     inhabited (`Once.Certified.Models`, D302): the claim is not vacuous.
--   • `language` — the core's metatheory (plan 0.102 B, D276): its term model
--     is a graded category and ⟦_⟧ a functor out of it — typed substitution,
--     and `let x = u in t` ≡ `t[u/x]` for pure `u` (referential transparency).
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

open import Data.Nat using (ℕ)

import Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds as RB
import Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds as RBr
import Once.Adequacy.ArchCorrectness.X86-32.ResourceBounds as RB32

-- Plan 0.107: the entry unit's owner is the EMITTER's (`Once.Compile.entry-owner`),
-- not a parameter — the theorem is about the program actually emitted.
open import Once.Compile using (entry-owner)

module Once.Certified
  (x86-64-heap-room : ∀ ι → RB.HeapRoom entry-owner ι) (x86-64-stack-room : ∀ ι → RB.StackRoom entry-owner ι)
  (x86-64-call-room : ∀ ι → RB.CallRoom entry-owner ι)
  (x86-64-reg-range : ∀ ι → RB.RegRange entry-owner ι)
  (x86-64-addr-no-wrap : ∀ ι → RB.AddrNoWrap entry-owner ι)
  (x86-64-lit-fits : ∀ ι → RB.LitFits entry-owner ι)
  -- Plan 0.65: riscv64's three, threaded the same way (D087). They could not
  -- be stated until riscv64 had a correspondence to condition them on; now
  -- they are, the apex constrains their shape instead of G2 inventing it.
  (riscv64-heap-room : ∀ ι → RBr.HeapRoom entry-owner ι) (riscv64-stack-room : ∀ ι → RBr.StackRoom entry-owner ι)
  (riscv64-call-room : ∀ ι → RBr.CallRoom entry-owner ι)
  (riscv64-reg-range : ∀ ι → RBr.RegRange entry-owner ι)
  (riscv64-slot-addr-no-wrap : ∀ ι → RBr.SlotAddrNoWrap entry-owner ι)
  (riscv64-addr-no-wrap : ∀ ι → RBr.AddrNoWrap entry-owner ι)
  (riscv64-lit-fits : ∀ ι → RBr.LitFits entry-owner ι)
  -- …and x86-32's six (plan 0.66 X3): the arch had none while its simulation
  -- was a whole-cloth postulate, which is precisely what a deleted apex
  -- postulate makes visible — the resources a running program needs.
  (x86-32-heap-room : ∀ ι → RB32.HeapRoom entry-owner ι) (x86-32-stack-room : ∀ ι → RB32.StackRoom entry-owner ι)
  (x86-32-call-room : ∀ ι → RB32.CallRoom entry-owner ι)
  (x86-32-reg-range : ∀ ι → RB32.RegRange entry-owner ι)
  (x86-32-addr-no-wrap : ∀ ι → RB32.AddrNoWrap entry-owner ι)
  (x86-32-lit-fits : ∀ ι → RB32.LitFits entry-owner ι) where

-- The correctness criterion and the metatheory are the Spec's (`Once/Spec`).
open import Once.Spec.Correct using (CorrectCompiler)
open import Once.Spec.Metatheory using (Metatheory)
open import Once.Compiler x86-64-heap-room x86-64-stack-room x86-64-call-room
       x86-64-reg-range x86-64-addr-no-wrap x86-64-lit-fits
       riscv64-heap-room riscv64-stack-room riscv64-call-room
       riscv64-reg-range riscv64-slot-addr-no-wrap
       riscv64-addr-no-wrap riscv64-lit-fits
       x86-32-heap-room x86-32-stack-room x86-32-call-room
       x86-32-reg-range x86-32-addr-no-wrap x86-32-lit-fits
       using (arch-correctness)
import Once.Adequacy.SpecApex as SpecApex
open import Once.TypeCheck.Verified using (VerifiedTypeChecker; verifiedTypeChecker)
-- Plan 0.102 phase B (D276, D304): the language's own metatheory, stated in the
-- Spec (`Once.Spec.Metatheory`), proved under `Once.Metatheory`.
open import Once.Metatheory using (metatheory)
open import Once.Certified.Models using (NonVacuous; models)

-- The correctness theorem, on the Spec (plan 0.121, D332): the compiler's own
-- (`Compile.correctᵈ`, over its working language) carried to the Spec's source,
-- typing and behaviour by the two bridges, both proved (`SpecApex.bridges`).
once-compiler : CorrectCompiler
once-compiler = SA.spec-compiler SA.bridges
  where
    module SA = SpecApex arch-correctness

record CertifiedBuild : Set₁ where
  field
    correctness : CorrectCompiler       -- soundness + completeness (the minimal claim)
    typechecker : VerifiedTypeChecker    -- determinism ∧ totality ∧ errors ∧ identities
    -- what the language promises about itself (the Spec's metatheory): the term
    -- model is a graded category, ⟦_⟧ a functor out of it — substitution of terms
    -- and of types is typed, a pure term may replace its `let`; subtyping is a
    -- partial order with unique derivations, and usage does not depend on mode
    language    : Metatheory
    -- the assumptions are satisfiable: the claim is not about an empty set (D302)
    nonvacuous  : NonVacuous

-- plan 0.125 S5 — UNCONDITIONAL AGAIN, AND NOT VACUOUS ON THIS ACCOUNT.
--
-- From plan 0.91 to here it took the three block-table coherence hypotheses
-- (one per target), and D340 showed their type EMPTY: the apex was vacuous a
-- second way. Plan 0.125 made the value relation say what a closure or a ν
-- DOES (`ValidAtWF` as a function on the type), so `apply`/`Out` read a
-- callee's run off the value and `curry`/`Ana`/`in-ν` prove it; and the
-- program's functions are discharged along the table (`FlatFromObs.block-runs`).
-- What the machine-correctness layer still assumes is listed in
-- `Once.Postulates`; `cata-correct` is proved for every cata (plan 0.125
-- cata M1/M4: `strat-const` by `CataConst`, the loop strategy `strat-branching`
-- by `CataBr.Branching`; `IRObsCorrect.Cata`).
once-certified : CertifiedBuild
once-certified = record
  { correctness = once-compiler
  ; typechecker = verifiedTypeChecker
  ; language    = metatheory
  ; nonvacuous  = models
  }
