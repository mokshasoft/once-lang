-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Target.RiscV64.RuntimeParams
--
-- RISC-V 64 runtime environment assumptions.
--
-- Provides the RuntimeContract for RISC-V64, capturing what the
-- OS/linker guarantees: memory region bounds and disjointness.
------------------------------------------------------------------------

module Once.CCC.Target.RiscV64.RuntimeParams where

open import Once.Memory.RuntimeContract

------------------------------------------------------------------------
-- RISC-V64 RuntimeContract
--
-- Memory bounds, region validity, and disjointness guarantees
-- provided by the runtime environment.
------------------------------------------------------------------------

postulate
  rv64-runtime : RuntimeContract

-- Re-export fields for convenience
open RuntimeContract rv64-runtime public