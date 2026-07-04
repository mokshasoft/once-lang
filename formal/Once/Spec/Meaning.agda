-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Spec.Meaning — the DYNAMIC semantics (OCP-0006, spec).
--
-- SPEC (trust boundary): what a program MEANS.
--   * `Once.Denotation.SourceDenote` (`⟦_⟧ˢ`) — the source meaning of surface
--     terms (D057: THE reference semantics).
--   * `Once.Denotation.Realize` (`realize`/`realize-morph`) — the elaborator-free
--     derivation → meaning bridge.
--   * `Once.Denotation.DenotTrace` (`evalᴰ`/`⟦_⟧ᴰ`) — the trace denotation.
--
-- `Once.IR` stays OUTSIDE the spec (OCP option a): it is a pure syntax
-- vocabulary tier (no machine behaviour), shared by spec and implementation like
-- `Once.Type`, so it is imported by these modules but NOT part of `Once.Spec`.
------------------------------------------------------------------------

module Once.Spec.Meaning where

open import Once.Denotation.SourceDenote public
open import Once.Denotation.Realize      public
open import Once.Denotation.DenotTrace    public
