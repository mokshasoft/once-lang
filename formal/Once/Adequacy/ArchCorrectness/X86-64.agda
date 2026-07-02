-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.X86-64
--
-- x86-64 backend correctness, now CONSTRUCTED via the shared
-- `FlatFromObs` module (Plan 0.53-step2 / Phase B Layer 1) instead of the
-- old monolithic `x86-flat-from-obs` postulate. The trust surface is now
-- explicit + named: `asm-sem`/`flat-trace` are DEFINED, `assemble-correct`
-- is `refl`, and the remaining gaps are the named postulates
-- `asm-trace-correct` (printer/loader) + `ir-flat-correct` (→ Layer 2),
-- plus the loader `_start` entry frame (`entry-s`/`entry-alloc`), a data
-- trust input Layer 2 constructs concretely. `ir-obs-correct` is still
-- threaded, so `cata-correct` stays load-bearing for the apex.
------------------------------------------------------------------------

module Once.Adequacy.ArchCorrectness.X86-64 where

open import Data.Nat using (ℕ)
open import Once.Adequacy.CPU using (x86-64; arch-semantics)
open import Once.Adequacy.Compile using (ArchCorrect)
open import Once.CCC.Target.X86-64.FrameInstantiation using (x86v3-frame-semantics)
open import Once.CCC.Machine.SMCore using (LocState)
open import Once.CCC.Machine.Allocation using (AllocState)
open import Once.CCC.Codegen.IRObsCorrectFlat using (module IRObsCorrectFlatness)
import Once.Adequacy.ArchCorrectness.FlatFromObs as FFO

postulate
  program-bound : ℕ
  -- The loader `_start` entry frame: LocState + allocator (next-slot ≡ 0).
  -- A named DATA trust input (constructible; Layer 2 builds it concretely).
  entry-s     : LocState x86v3-frame-semantics
  entry-alloc : AllocState {x86v3-frame-semantics}

open IRObsCorrectFlatness {x86v3-frame-semantics} program-bound using (ir-obs-correct)

x86-64-correct : ArchCorrect x86-64 (arch-semantics x86-64)
x86-64-correct =
  FFO.flat-from-obs x86-64 x86v3-frame-semantics (arch-semantics x86-64)
    program-bound entry-s entry-alloc ir-obs-correct
