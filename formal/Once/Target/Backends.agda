-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Target.Backends — plan 0.146 B1.7c (D465): THE ARCHES' CODE
-- GENERATORS, the one case split on the arch (`Target.Backend`).
------------------------------------------------------------------------

module Once.Target.Backends where

open import Once.Target.Arch using (Arch; x86-64; x86-32; riscv64)
open import Once.Target.Backend using (Backend)
import Once.Target.X86-64.Backend
import Once.Target.X86-32.Backend
import Once.Target.RiscV64.Backend

backend : Arch → Backend
backend x86-64  = Once.Target.X86-64.Backend.backend
backend x86-32  = Once.Target.X86-32.Backend.backend
backend riscv64 = Once.Target.RiscV64.Backend.backend
