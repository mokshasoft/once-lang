-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Target.X86-32.Types
--
-- X86-32 specific constants.
--
-- For types, import Once.Type directly.
-- For slot calculations, import Once.Memory.TypeSlots.
-- For semantics, import Once.Semantics.Machine.
------------------------------------------------------------------------

module Once.CCC.Target.X86-32.Types where

open import Data.Nat using (ℕ)

-- | Bytes per slot (x86-32 uses 32-bit words)
slot-bytes : ℕ
slot-bytes = 4
