-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Target.X86-64.RuntimeParams
--
-- X86-64 runtime environment assumptions.
--
-- Provides the RuntimeContract for X86-64, capturing what the
-- OS/linker guarantees: memory region bounds and disjointness.
------------------------------------------------------------------------

module Once.CCC.Target.X86-64.RuntimeParams where

open import Once.Memory.RuntimeContract

------------------------------------------------------------------------
-- X86-64 RuntimeContract
--
-- Memory bounds, region validity, and disjointness guarantees
-- provided by the runtime environment.
------------------------------------------------------------------------

postulate
  x86-64-runtime : RuntimeContract

-- Re-export fields for convenience
open RuntimeContract x86-64-runtime public