-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Semantics.Machine
--
-- Machine-level semantic interpretation.
--
-- D054: `Int` denotes the modular machine `Word` (`Once.Word.Carrier`),
-- NOT unbounded ℕ. The carrier is ℕ only as scaffolding *inside* the
-- residue definition (CompCert's model); boundedness + wraparound live
-- in the modular ops. The carrier is deliberately WIDTH-AGNOSTIC: the
-- residue carrier is width-invariant, so per-target width is threaded
-- from the arch into the ops (D059), never baked into this denotation.
-- This module is TARGET-INDEPENDENT. Backends may provide additional
-- type representations (e.g., stack-type-slots for X86).
--
-- For IR evaluation semantics, use Once.Semantics.IR instead.
------------------------------------------------------------------------

module Once.Semantics.Machine where

-- Instantiate the value semantics at the target `Word` carrier (D054).
open import Once.Word using (Carrier)
open import Once.Semantics.Value Carrier public
