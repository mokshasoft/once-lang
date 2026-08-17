-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.X86-32.RunContext
--
-- x86-32's INSTANCE of the arch-generic run context (Plan 0.65 G1).
--
-- The content moved to `…ArchCorrectness.FlatCore.RunContext` unchanged —
-- `EntryLike`, `Reachable`, `Emitted`, `RunAt` are statements about the FLAT
-- machine and the emitted trace, and the only thing this arch supplied was the
-- number `slot-size`. This module is what supplies it, and re-exports the rest
-- so every existing importer reads exactly as before.
--
-- The third of the three sibling modules (plan 0.66 X2). The definitions are
-- shared, so a change to the run context is one edit, not three — and the only
-- thing that differs here is the number, which is 4.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics; frame-word)
open import Once.CCC.Target.X86-32.Syntax using (slot-size)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- Plan 0.63 (D089): parameterised by the DEFINITION'S identity, which keys its
-- labels. `o` is constant for a whole definition, so it belongs on the module
-- rather than on every lemma.
open import Once.CanonicalName using (CanonicalName)

module Once.Adequacy.ArchCorrectness.X86-32.RunContext (o : CanonicalName)
  (FS : FrameSemantics)
  (word-eq : frame-word FS ≡ slot-size)
  where

open import Once.Adequacy.ArchCorrectness.FlatCore.RunContext o FS slot-size word-eq public
