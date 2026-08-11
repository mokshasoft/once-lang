-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.X86-64.RunContext
--
-- x86-64's INSTANCE of the arch-generic run context (Plan 0.65 G1).
--
-- The content moved to `…ArchCorrectness.FlatCore.RunContext` unchanged —
-- `EntryLike`, `Reachable`, `Emitted`, `RunAt` are statements about the FLAT
-- machine and the emitted trace, and the only thing this arch supplied was the
-- number `slot-size`. This module is what supplies it, and re-exports the rest
-- so every existing importer reads exactly as before.
--
-- riscv64 and x86-32 get sibling modules of this shape (G2 / plan 0.66); the
-- definitions are shared, so a change to the run context is one edit, not
-- three.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics; frame-word)
open import Once.CCC.Target.X86-64.Syntax using (slot-size)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- Plan 0.63 (D089): parameterised by the DEFINITION'S identity, which keys its
-- labels. `o` is constant for a whole definition, so it belongs on the module
-- rather than on every lemma.
open import Once.CanonicalName using (CanonicalName)

module Once.Adequacy.ArchCorrectness.X86-64.RunContext (o : CanonicalName)
  (FS : FrameSemantics)
  (word-eq : frame-word FS ≡ slot-size)
  where

open import Once.Adequacy.ArchCorrectness.FlatCore.RunContext o FS slot-size word-eq public
