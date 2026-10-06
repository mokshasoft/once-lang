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
open import Once.CanonicalName using (CanonicalName)

open import Data.Nat using (ℕ)

open import Once.Denotation.TraceMonad using (Interp)
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
  (x86-64-scratch-dec-guarded : ∀ ι → RB.ScratchDecGuarded entry-owner ι)
  (x86-64-addr-no-wrap : ∀ ι → RB.AddrNoWrap entry-owner ι)
  (x86-64-lit-fits : ∀ ι → RB.LitFits entry-owner ι)
  -- Plan 0.65: riscv64's three, threaded the same way (D087). They could not
  -- be stated until riscv64 had a correspondence to condition them on; now
  -- they are, the apex constrains their shape instead of G2 inventing it.
  (riscv64-heap-room : ∀ ι → RBr.HeapRoom entry-owner ι) (riscv64-stack-room : ∀ ι → RBr.StackRoom entry-owner ι)
  (riscv64-call-room : ∀ ι → RBr.CallRoom entry-owner ι)
  (riscv64-reg-range : ∀ ι → RBr.RegRange entry-owner ι)
  (riscv64-scratch-dec-guarded : ∀ ι → RBr.ScratchDecGuarded entry-owner ι)
  (riscv64-slot-addr-no-wrap : ∀ ι → RBr.SlotAddrNoWrap entry-owner ι)
  (riscv64-addr-no-wrap : ∀ ι → RBr.AddrNoWrap entry-owner ι)
  (riscv64-lit-fits : ∀ ι → RBr.LitFits entry-owner ι)
  -- …and x86-32's seven (plan 0.66 X3): the arch had none while its simulation
  -- was a whole-cloth postulate, which is precisely what a deleted apex
  -- postulate makes visible — the resources a running program needs.
  (x86-32-heap-room : ∀ ι → RB32.HeapRoom entry-owner ι) (x86-32-stack-room : ∀ ι → RB32.StackRoom entry-owner ι)
  (x86-32-call-room : ∀ ι → RB32.CallRoom entry-owner ι)
  (x86-32-reg-range : ∀ ι → RB32.RegRange entry-owner ι)
  (x86-32-scratch-dec-guarded : ∀ ι → RB32.ScratchDecGuarded entry-owner ι)
  (x86-32-addr-no-wrap : ∀ ι → RB32.AddrNoWrap entry-owner ι)
  (x86-32-lit-fits : ∀ ι → RB32.LitFits entry-owner ι) where

-- P5 (OCP-0006): the correctness criterion is consumed THROUGH the spec
-- door — `Once.Spec` is on the certified path, not an island.
open import Once.Spec using (CorrectCompiler)
open import Once.Compiler x86-64-heap-room x86-64-stack-room x86-64-call-room
       x86-64-reg-range x86-64-scratch-dec-guarded x86-64-addr-no-wrap x86-64-lit-fits
       riscv64-heap-room riscv64-stack-room riscv64-call-room
       riscv64-reg-range riscv64-scratch-dec-guarded riscv64-slot-addr-no-wrap
       riscv64-addr-no-wrap riscv64-lit-fits
       x86-32-heap-room x86-32-stack-room x86-32-call-room
       x86-32-reg-range x86-32-scratch-dec-guarded x86-32-addr-no-wrap x86-32-lit-fits
       using (once-compiler; BlockRunsHyp-x86-64; BlockRunsHyp-x86-32; BlockRunsHyp-riscv64)
open import Once.TypeCheck.Verified using (VerifiedTypeChecker; verifiedTypeChecker)
-- Plan 0.102 phase B (D276): the language's own metatheory, stated in the Spec.
open import Once.Spec.Contract using (ISig)
open import Once.Spec.Core.PolyTy using (Sig)
import Once.Spec.Core.TermModel as TM
open import Once.Adequacy.TermModel using (termModel)

record CertifiedBuild : Set₁ where
  field
    correctness : CorrectCompiler       -- soundness + completeness (the minimal claim)
    typechecker : VerifiedTypeChecker    -- determinism ∧ totality ∧ errors ∧ identities
    -- the term model is a graded category, ⟦_⟧ a functor out of it: substitution
    -- is typed, and a pure term may replace its `let` (referential transparency)
    language    : ∀ {Fs : ISig} {s : ℕ} (S : Sig Fs s) → TM.TermModel S

-- plan 0.91 parallel track (2026-09-17) — THE ASSUMPTION IS NOW IN THE
-- STATEMENT.
--
-- `once-certified` used to be unconditional. It was also VACUOUS: it rested on
-- `block-runs`, which D213 refuted with a machine-checked `⊥`
-- (`Once/Probe/ApexInconsistent.boom`). An inconsistent assumption proves
-- everything, so the unconditional reading was worth nothing.
--
-- It now takes the three block-table coherence hypotheses — one per target,
-- because `BlockRuns` is `FrameSemantics`-relative and the single postulate was
-- quietly standing for all three at once. The theorem reads:
--
--     IF the emitter's block table is coherent on each target,
--     THEN the compiler is correct and the typechecker is verified.
--
-- That is WEAKER than what stood here and TRUE, where what stood here was
-- stronger and vacuous. Discharging the hypotheses is plan 0.93's purpose: the
-- fact they assert is BEHAVIOURAL, and D217 showed (machine-checked, one cell
-- two denotations) that no property of a machine STATE can supply it — which
-- is why `ValidAtWF` has to become a relation recursive on the TYPE rather
-- than a `data` indexed by it.
once-certified : BlockRunsHyp-x86-64 → BlockRunsHyp-x86-32 → BlockRunsHyp-riscv64
               → CertifiedBuild
once-certified b64 b32 brv = record
  { correctness = once-compiler b64 b32 brv
  ; typechecker = verifiedTypeChecker
  ; language    = termModel
  }
