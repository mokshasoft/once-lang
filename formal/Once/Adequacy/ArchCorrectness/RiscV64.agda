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
-- riscv64-correct is now CONSTRUCTED via the shared `FlatFromObs` module
-- (Phase B L1): `asm-sem`/`flat-trace` DEFINED, `assemble-correct` = `refl`,
-- with named postulates `asm-trace-correct`/`ir-flat-correct` + the loader
-- `entry-s`/`entry-alloc`. The old monolithic `riscv64-flat-from-obs`
-- postulate is retired.
------------------------------------------------------------------------

module Once.Adequacy.ArchCorrectness.RiscV64 where

open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe)
open import Once.IR using (IR; Unit)  -- Plan 0.52 M2: IRTy Unit
open import Once.Denotation.Behavior using (Behavior)
open import Once.Adequacy.CPU using (riscv64; arch-semantics)
open import Once.Adequacy.Compile using (ArchCorrect)
open import Once.CCC.Target.RiscV64.FrameInstantiation using (rv64-frame-semantics)
open import Once.CCC.Codegen.IRObsCorrectFlat using (module IRObsCorrectFlatness)
import Once.Adequacy.ArchCorrectness.FlatFromObs as FFO

postulate
  program-bound : ℕ

open IRObsCorrectFlatness {rv64-frame-semantics} program-bound using (ir-obs-correct)

-- riscv64's witness, CONSTRUCTED via the shared FlatFromObs (Phase B L1).
riscv64-correct : ArchCorrect riscv64 (arch-semantics riscv64)
riscv64-correct =
  FFO.flat-from-obs riscv64 rv64-frame-semantics (arch-semantics riscv64)
    program-bound ir-obs-correct
