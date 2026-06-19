-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Semantics.Machine
--
-- Machine-level semantic interpretation.
--
-- Uses ℕ for Int (machine registers are natural numbers).
-- This module is TARGET-INDEPENDENT. Backends may provide additional
-- type representations (e.g., stack-type-slots for X86).
--
-- For IR evaluation semantics, use Once.Semantics.IR instead.
------------------------------------------------------------------------

module Once.Semantics.Machine where

open import Data.Nat using (ℕ)

-- Instantiate Core with ℕ for integers
open import Once.Semantics.Value ℕ public