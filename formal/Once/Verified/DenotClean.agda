-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Verified.DenotClean — the regression GATE for the denotational
-- semantics being TP-by-construction (D062).
--
-- Checked under `{-# OPTIONS --safe #-}`, this module imports the
-- denotational meaning (⟦_⟧ˢ / ⟦_⟧ᴰ / faithful / ⟦_⟧). Because `--safe` is
-- INFECTIVE — a safe module may only import safe modules — typechecking it
-- forces the ENTIRE import closure of the meaning to be free of:
--   * `{-# TERMINATING #-}` / `{-# NON_TERMINATING #-}`
--   * `primTrustMe`
--   * `--sized-types`
--   * `--no-positivity-check`, `--type-in-type`, and the other unsafe flags.
--
-- `--safe` does NOT reject `postulate` — that is reported separately by
-- `make denot-postulate-free` (a grep over the closure).
--
-- GREEN here ⟹ the denotational semantics is TERMINATING / trustMe / sized
-- free across its whole foundation. It is RED until `fuseW` (Hylo/Fuse) and
-- `sem-ana` (Ana), plus the off-path foundation pragmas reachable in the
-- closure, are discharged (D062).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Once.Verified.DenotClean where

import Once.Verified.SourceFaithful
import Once.Verified.SourceTrace
import Once.Verified.SourceDenote
import Once.Verified.DenotTrace
