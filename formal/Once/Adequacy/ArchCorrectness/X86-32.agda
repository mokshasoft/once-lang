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
-- x86-32-correct is now CONSTRUCTED via the shared `FlatFromObs` module
-- (Phase B L1): `asm-sem`/`flat-trace` DEFINED, `assemble-correct` = `refl`,
-- with named postulates `asm-trace-correct`/`ir-flat-correct` + the loader
-- `entry-s`/`entry-alloc`. The old monolithic `x86-32-flat-from-obs`
-- postulate is retired.
------------------------------------------------------------------------

module Once.Adequacy.ArchCorrectness.X86-32 where

open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe)
open import Once.IR using (IR; Unit)  -- Plan 0.52 M2: IRTy Unit
open import Once.Denotation.Behavior using (Behavior)
open import Once.Adequacy.CPU using (x86-32; arch-semantics)
open import Once.Adequacy.Compile using (ArchCorrect)
open import Once.CCC.Target.X86-32.FrameInstantiation using (x86-32-frame-semantics)
open import Once.CCC.Codegen.IRObsCorrectFlat using (module IRObsCorrectFlatness)
import Once.Adequacy.ArchCorrectness.FlatFromObs as FFO

postulate
  program-bound : ℕ

open IRObsCorrectFlatness {x86-32-frame-semantics} program-bound using (ir-obs-correct)

-- x86-32's witness, CONSTRUCTED via the shared FlatFromObs (Phase B L1).
-- Plan 0.54 rung B: the concrete↔abstract seam, now LOCALISED here (was an
-- internal FlatFromObs postulate). At this per-arch instance the concrete
-- machine IS visible, so the arith slice is dischargeable from
-- `dispatch-arith-preserves`; the non-arith remainder is the explicit ISA /
-- printer / loader trust (GNU `as` class). Stated against the DEFINED
-- `flat-trace` via `FFO.AsmTraceCorrect`.
postulate
  asm-trace-correct-x86-32 :
    FFO.AsmTraceCorrect x86-32 x86-32-frame-semantics (arch-semantics x86-32) program-bound
      (FFO.flat-trace-of x86-32 x86-32-frame-semantics (arch-semantics x86-32) program-bound ir-obs-correct)

x86-32-correct : ArchCorrect x86-32 (arch-semantics x86-32)
x86-32-correct =
  FFO.flat-from-obs x86-32 x86-32-frame-semantics (arch-semantics x86-32)
    program-bound ir-obs-correct asm-trace-correct-x86-32
