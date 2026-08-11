-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Target.RiscV64.Types
--
-- RISC-V 64-bit specific constants.
--
-- For types, import Once.Type directly.
-- For slot calculations, import Once.Memory.TypeSlots.
-- For semantics, import Once.Semantics.Machine.
------------------------------------------------------------------------

module Once.CCC.Target.RiscV64.Types where

open import Data.Nat using (ℕ)

-- | Bytes per slot (RV64 uses 64-bit words)
slot-bytes : ℕ
slot-bytes = 8
