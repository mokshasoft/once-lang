-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.RiscV64 — riscv64's backend-correctness
-- witness, routed THROUGH the generic per-IR observable theorem.
--
-- Mirror of `Once.Adequacy.ArchCorrectness.X86-64` (Plan 0.53 Phase 3):
-- `riscv64-correct` is discharged through `ir-obs-correct` — the total
-- IR-observable dispatch (`Once.CCC.Codegen.IRObsCorrectFlat`, GENERIC in
-- `FrameSemantics`), instantiated at riscv64's `FrameSemantics`. Since
-- `ir-obs-correct` routes `Cata → cata-correct`, `cata-correct` is
-- LOAD-BEARING for the apex `correct` on this target too.
--
-- The remaining per-target FS plumbing is bundled in the single NAMED
-- bridge `riscv64-flat-from-obs` — the same shape/trust as x86-64's
-- `x86-flat-from-obs`. This raises riscv64 from a whole-record postulate to
-- exactly x86-64's level.
------------------------------------------------------------------------

module Once.Adequacy.ArchCorrectness.RiscV64 where

open import Data.Nat using (ℕ)
open import Once.IR using (IR)
open import Once.Adequacy.CPU using (riscv64; arch-semantics)
open import Once.Adequacy.Compile using (ArchCorrect)
open import Once.CCC.Target.RiscV64.FrameInstantiation using (rv64-frame-semantics)
open import Once.CCC.Codegen.IRObsCorrectFlat using (module IRObsCorrectFlatness)

-- The observation bound for this target (per-IR; ≥ the relevant `ir-size`s).
postulate program-bound : ℕ

open IRObsCorrectFlatness {rv64-frame-semantics} program-bound
  using (IRObsCorrectF; ir-obs-correct)

-- The per-target bridge: the FS-level per-IR observable theorem
-- (`ir-obs-correct`, routing `Cata → cata-correct`) → riscv64's `ArchCorrect`.
postulate
  riscv64-flat-from-obs :
    (∀ {A B} (ir : IR A B) → IRObsCorrectF ir)
    → ArchCorrect riscv64 (arch-semantics riscv64)

-- riscv64's witness, DISCHARGED THROUGH ir-obs-correct (→ cata-correct).
riscv64-correct : ArchCorrect riscv64 (arch-semantics riscv64)
riscv64-correct = riscv64-flat-from-obs ir-obs-correct
