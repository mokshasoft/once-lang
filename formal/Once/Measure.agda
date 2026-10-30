-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Measure — `once stats`: what the emitted code costs, statically
-- (MERGE.md §1 "Emitted code and its cost"; run-time counts are plan 0.130).
--
-- A tool beside the compiler, as `Once.Format` is: it reads the program image
-- the build emits (`Compile.image-of`; a library's, `lib-image`) and counts it
-- (`Measure.Image`). The compiler does not import it.
------------------------------------------------------------------------

module Once.Measure where

open import Data.Bool using (Bool)
open import Data.Maybe using (just; nothing)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Once.IR using (Heap)
open import Once.Compile using (compileResolvedModule; findMain; tableOf; image-of; lib-image)
open import Once.Denotation.Program using (irProgram)
open import Once.Parser.Module.Core using (Resolved)
open import Once.Measure.Image using (image-stats; show-stats)

-- | The static costs of the module's image, optimized or not, or the
-- compiler's error. A library's image is its functions.
statsOf : Bool → Resolved → String ⊎ String
statsOf doOpt mod with compileResolvedModule Heap doOpt mod
... | inj₁ err = inj₁ err
... | inj₂ cfs with findMain cfs
...   | nothing = inj₂ (show-stats (image-stats (lib-image (tableOf cfs))))
...   | just ir = inj₂ (show-stats (image-stats (image-of (irProgram (tableOf cfs) ir))))
