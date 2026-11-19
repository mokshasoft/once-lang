-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.Backend.X86-64.StatePreserve  (Plan 0.54 Phase B / Option 2)
--
-- X86-64 instance of the arch-generic StatePreserveCore: just wire the arch's
-- regs/memory projections and register/memory agreement relations.
------------------------------------------------------------------------

module Once.Arith.Backend.X86-64.StatePreserve where

open import Once.CCC.Target.X86-64.Semantics using (State)
open State using (regs; memory)
open import Once.Arith.Backend.X86-64.Preserve using (AgreeCCC; agree-refl-ccc; AgreeCCC-trans)
open import Once.Arith.Backend.X86-64.MemPreserve using (module MemPreserveCore)
open MemPreserveCore using (AgreeMemFrom; AgreeMemFrom-refl; AgreeMemFrom-trans)

import Once.Arith.Backend.StatePreserveCore
module StatePreserveCore = Once.Arith.Backend.StatePreserveCore
  regs memory AgreeCCC agree-refl-ccc AgreeCCC-trans AgreeMemFrom AgreeMemFrom-refl AgreeMemFrom-trans
