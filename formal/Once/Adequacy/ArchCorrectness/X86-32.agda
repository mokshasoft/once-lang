-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.X86-32 — x86-32's backend-correctness
-- witness, routed THROUGH the generic per-IR observable theorem.
--
-- Mirror of `Once.Adequacy.ArchCorrectness.X86-64` (Plan 0.53 Phase 2):
-- `x86-32-correct` is discharged through `ir-obs-correct` — the total
-- IR-observable dispatch (`Once.CCC.Codegen.IRObsCorrectFlat`, GENERIC in
-- `FrameSemantics`), instantiated at x86-32's `FrameSemantics`. Since
-- `ir-obs-correct` routes `Cata → cata-correct`, `cata-correct` is
-- LOAD-BEARING for the apex `correct` on this target too.
--
-- The remaining per-target FS plumbing (entry state, its preconditions,
-- the per-IR observation bound, the prefix lift from `traces-agree` to
-- `ir-flat-correct`'s ∀-n shape) is bundled in the single NAMED bridge
-- `x86-32-flat-from-obs` — the same shape/trust as x86-64's
-- `x86-flat-from-obs`. This raises x86-32 from a whole-record postulate to
-- exactly x86-64's level.
------------------------------------------------------------------------

module Once.Adequacy.ArchCorrectness.X86-32 where

open import Data.Nat using (ℕ)
open import Once.Adequacy.CPU using (x86-32; arch-semantics)
open import Once.Adequacy.Compile using (ArchCorrect)
open import Once.CCC.Target.X86-32.FrameInstantiation using (x86-32-frame-semantics)
open import Once.CCC.Machine.SMCore using (LocState)
open import Once.CCC.Machine.Allocation using (AllocState)
open import Once.CCC.Codegen.IRObsCorrectFlat using (module IRObsCorrectFlatness)
import Once.Adequacy.ArchCorrectness.FlatFromObs as FFO

postulate
  program-bound : ℕ
  -- loader `_start` entry frame (named data trust input; Layer 2 builds it).
  entry-s     : LocState x86-32-frame-semantics
  entry-alloc : AllocState {x86-32-frame-semantics}

open IRObsCorrectFlatness {x86-32-frame-semantics} program-bound using (ir-obs-correct)

-- x86-32's witness, CONSTRUCTED via the shared FlatFromObs (Phase B L1).
x86-32-correct : ArchCorrect x86-32 (arch-semantics x86-32)
x86-32-correct =
  FFO.flat-from-obs x86-32 x86-32-frame-semantics (arch-semantics x86-32)
    program-bound entry-s entry-alloc ir-obs-correct
