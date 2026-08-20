-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.RealizeBridge — the AGREEMENT BRIDGE (Plan 0.49 Phase 2 /
-- route 2). A PROOF (not semantics): the real `checkElab` algorithm agrees,
-- denotationally, with the REFERENCE elaboration `realize` (the spec).
--
-- This is the ONLY module allowed to import BOTH the elaborator (`checkElab`)
-- and the reference (`realize`) — it is where they meet. Discharging
-- `realize-agrees` is what FORCES `checkElab`'s term-choice against the
-- denotation (`SD`), closing the last cancellation (row-3). It is NOT trivial:
-- `realize (check-sound … cc)` is the CANONICAL term read off the term-free
-- derivation (built from the raw program), not a copy of `checkElab`'s `se`.
--
-- Companion to `Once.Adequacy.SourceFaithful.faithful` (which relates the OTHER
-- elaborator stage `elaborate : SExpr → IR` to `SD`). Together they force the
-- whole front-end against the one denotation.
------------------------------------------------------------------------

open import Once.Float.Dyadic using (FloatFormat)

-- Plan 0.73 (D113): this module's statements mention a denotation that is
-- target-relative at `Float`, so the format is a parameter. A MODULE parameter
-- rather than a per-lemma argument because everything here is a PROOF —
-- downstream uses these as facts and never reduces them — so the "recursive
-- function in a parameterised module stops reducing" trap does not apply. The
-- denotations themselves take it as an explicit argument.
module Once.Adequacy.RealizeBridge (fmt : FloatFormat) where

-- `realize-agrees` is now PROVEN (Plan 0.50: de-islanded). It used to be a
-- `postulate` here while the proof floated in a parallel module imported by
-- nothing — the apex assumed it as an axiom and never saw the proof. The proof
-- (the per-construct agreement lemmas + the `check-sound`/`checkElabV` bridge)
-- lives in `Once.Adequacy.RealizeAgrees`; this module RE-EXPORTS it so the apex
-- path (`Compile.main-realize-agrees` → here) consumes the real theorem. The
-- remaining debt is now `RealizeAgrees.{infer,check}-agreeV-todo`, which sit
-- transitively ON the apex path — itemized, not a disconnected island.
open import Once.Adequacy.RealizeAgrees fmt using (realize-agrees) public
