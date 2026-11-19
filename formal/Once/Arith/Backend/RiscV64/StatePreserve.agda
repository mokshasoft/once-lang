-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.Backend.RiscV64.StatePreserve  (Plan 0.54 Phase B / Option 2)
--
-- RiscV64 instance of the arch-generic StatePreserveCore: just wire the arch's
-- regs/memory projections and register/memory agreement relations.
------------------------------------------------------------------------

module Once.Arith.Backend.RiscV64.StatePreserve where

open import Once.CCC.Target.RiscV64.Semantics using (State)
open State using (regs; memory)
open import Once.Arith.Backend.RiscV64.Preserve using (AgreeCCC; agree-refl-ccc; AgreeCCC-trans)
open import Once.Arith.Backend.RiscV64.MemPreserve using (module MemPreserveCore)
open MemPreserveCore using (AgreeMemFrom; AgreeMemFrom-refl; AgreeMemFrom-trans)

import Once.Arith.Backend.StatePreserveCore
module StatePreserveCore = Once.Arith.Backend.StatePreserveCore
  regs memory AgreeCCC agree-refl-ccc AgreeCCC-trans AgreeMemFrom AgreeMemFrom-refl AgreeMemFrom-trans
  using (PreservesCCCState; mkPresState; preserves-state-refl; preserves-state-trans)
