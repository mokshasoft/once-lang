-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.X86-64 — x86-64's backend-correctness
-- witness, routed THROUGH the generic per-IR observable theorem.
--
-- This is where the cata proofs are TIED to the apex. `x86-64-correct`'s
-- `ir-flat-correct` field is discharged through `ir-obs-correct` — the
-- total IR-observable dispatch (`Once.CCC.Codegen.IRObsCorrectFlat`),
-- instantiated at x86-64's `FrameSemantics`. Since `ir-obs-correct` routes
-- the `Cata` constructor to `cata-correct`, `cata-correct` is now
-- LOAD-BEARING for the apex `correct`: a change to it changes this witness.
--
-- The remaining per-target FS plumbing — the `_start`/loader entry state,
-- its preconditions (`ValidAtWF` of the `tt` input, frontier 0, …), the
-- per-IR observation bound, and the `take n` prefix lift from
-- `traces-agree` to `ir-flat-correct`'s ∀-n shape — is bundled in the
-- single NAMED bridge `x86-flat-from-obs`. It is provable (it is just the
-- entry-state setup + the prefix lemma, no new mathematics), and is the
-- last gap between `cata-correct` and `x86-64-correct`.
------------------------------------------------------------------------

module Once.Adequacy.ArchCorrectness.X86-64 where

open import Data.Nat using (ℕ)
open import Once.CCC.IR using (IR)
open import Once.Adequacy.CPU using (x86-64; arch-semantics)
open import Once.Adequacy.Compile using (ArchCorrect)
open import Once.CCC.Target.X86-64.FrameInstantiation using (x86v3-frame-semantics)
open import Once.CCC.Codegen.IRObsCorrectFlat using (module IRObsCorrectFlatness)

-- The observation bound for this target (per-IR; ≥ the relevant `ir-size`s).
postulate program-bound : ℕ

open IRObsCorrectFlatness {x86v3-frame-semantics} program-bound
  using (IRObsCorrectF; ir-obs-correct)

-- The per-target bridge: the FS-level per-IR observable theorem
-- (`ir-obs-correct`, routing `Cata → cata-correct`) → x86-64's `ArchCorrect`.
-- NAMED so the entry/prefix plumbing is explicit; consumes `ir-obs-correct`
-- so `cata-correct` is load-bearing.
postulate
  x86-flat-from-obs :
    (∀ {A B} (ir : IR A B) → IRObsCorrectF ir)
    → ArchCorrect x86-64 (arch-semantics x86-64)

-- x86-64's witness, DISCHARGED THROUGH ir-obs-correct (→ cata-correct).
x86-64-correct : ArchCorrect x86-64 (arch-semantics x86-64)
x86-64-correct = x86-flat-from-obs ir-obs-correct
