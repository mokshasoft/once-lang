-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.X86-64
--
-- x86-64 backend correctness, now CONSTRUCTED via the shared `FlatFromObs`
-- module (Plan 0.53-step2 / Phase B Layer 1) instead of the old monolithic
-- `x86-flat-from-obs` postulate. Explicit trust surface: `asm-sem` DEFINED,
-- `assemble-correct` = `refl`; the remaining gaps are the named postulates
-- `flat-trace` (the flat-machine trace — Layer 2 defines it concretely with
-- an adequate fuel), `asm-trace-correct` (printer/loader), and
-- `ir-flat-correct` (→ Layer 2). `ir-obs-correct` is threaded so
-- `cata-correct` stays load-bearing for the apex.
------------------------------------------------------------------------

module Once.Adequacy.ArchCorrectness.X86-64 where

open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe)
open import Once.IR using (IR; Unit)  -- Plan 0.52 M2: IRTy Unit
open import Once.Denotation.Behavior using (Behavior)
open import Once.Adequacy.CPU using (x86-64; arch-semantics)
open import Once.Adequacy.Compile using (ArchCorrect)
open import Once.CCC.Target.X86-64.FrameInstantiation using (x86v3-frame-semantics)
open import Once.CCC.Codegen.IRObsCorrectFlat using (module IRObsCorrectFlatness)
import Once.Adequacy.ArchCorrectness.FlatFromObs as FFO

postulate
  program-bound : ℕ
  -- the flat-machine SigOp trace of a compiled IR (a named DATA trust input;
  -- Layer 2 defines it concretely as `take n (flat-events (EF …) …)`).

open IRObsCorrectFlatness {x86v3-frame-semantics} program-bound using (ir-obs-correct)

x86-64-correct : ArchCorrect x86-64 (arch-semantics x86-64)
x86-64-correct =
  FFO.flat-from-obs x86-64 x86v3-frame-semantics (arch-semantics x86-64)
    program-bound ir-obs-correct
