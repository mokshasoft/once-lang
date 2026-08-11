-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Target.X86-64.Types
--
-- X86-64 specific constants.
--
-- For types, import Once.Type directly.
-- For slot calculations, import Once.Memory.TypeSlots.
-- For semantics, import Once.Semantics.Machine.
------------------------------------------------------------------------

module Once.CCC.Target.X86-64.Types where

open import Data.Nat using (ℕ)

-- | Bytes per slot (x86-64 uses 64-bit words)
slot-bytes : ℕ
slot-bytes = 8
