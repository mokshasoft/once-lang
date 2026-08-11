-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Parser.Inline
--
-- Plan 0.6.2: this module is effectively empty. The previous
-- contents (`inlineReferences`, `expandBuiltins`, `betaReduceApps`,
-- `subst`) implemented RawExpr-level inlining + desugaring for
-- user-polymorphic definitions (plan 0.6 Phase C.*). They were
-- superseded by the typecheck-time schema-instantiation path in
-- `Once.TypeCheck.Elaborate` (plan 0.6.2 Phase 3). See D045 for
-- the architectural decision.
--
-- The module is kept as a no-op to preserve the import path for
-- downstream code that still references `Once.Parser.Inline`. If
-- no such imports remain, this file can be deleted entirely.
------------------------------------------------------------------------

module Once.Parser.Inline where
