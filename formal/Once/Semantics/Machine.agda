-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Semantics.Machine
--
-- Machine-level semantic interpretation.
--
-- D054: `Int` denotes the target's modular machine `Word`
-- (`Once.Word.Word64.Word`), NOT unbounded ℕ. The carrier is ℕ only as
-- scaffolding *inside* `Word`'s residue definition (CompCert's model);
-- boundedness + wraparound live in the modular ops. The 64-bit name is
-- canonical: the residue carrier is width-invariant, so per-target width
-- (x86-32 etc.) is an operational concern in the arith/backend layer.
-- This module is TARGET-INDEPENDENT. Backends may provide additional
-- type representations (e.g., stack-type-slots for X86).
--
-- For IR evaluation semantics, use Once.Semantics.IR instead.
------------------------------------------------------------------------

module Once.Semantics.Machine where

-- Instantiate the value semantics at the target `Word` carrier (D054).
open import Once.Word using (module Word64)
open import Once.Semantics.Value Word64.Word public
