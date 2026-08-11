-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Target.Arch — the single, shared target-architecture enum.
--
-- The architecture of the COMPILED BINARY (not the host the compiler runs
-- on). Owned by neither the codegen (`Once.Compile`) nor the verified CPU
-- interface (`Once.Adequacy.CPU.Interface`) — both import it, so there is
-- ONE `Arch` type across the pipeline and no relabelling map between a
-- "codegen Arch" and a "verified Arch".
------------------------------------------------------------------------

module Once.Target.Arch where

-- Supported architectures.
data Arch : Set where
  x86-64  : Arch
  x86-32  : Arch
  riscv64 : Arch
