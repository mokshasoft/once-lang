-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Correct — the correctness CRITERION (OCP-0006, spec).
--
-- SPEC (trust boundary): what "the compiler is correct" MEANS. Re-exports
-- `Once.Adequacy` — the `CorrectCompiler` record, which is proof-FREE: `correct`
-- is a FIELD whose TYPE is the top-level claim (soundness+trace ∧ completeness,
-- against the INDEPENDENT `_⊢_`/`⟦_⟧ˢ`). It is trusted because a machine-checked
-- proof is only worth the proposition it proves — a wrong/vacuous statement here
-- would make every instance proof worthless, and Agda cannot catch that for you.
--
-- The PROOF (the instance `Once.Compiler` filling `correct`) and the
-- `Once.Adequacy.*` sibling proof modules are machine-checked, hence NOT trusted,
-- and are NOT re-exported. Any NAMED postulates the instance rests on are
-- trust-boundary but live in the instance (see `make postulates`).
------------------------------------------------------------------------

module Once.Spec.Correct where

-- EXPLICIT re-export: the trust boundary is a DECISION, not whatever happens to
-- be in `Once.Adequacy`. Adding a definition there must not silently make it
-- part of the criterion a reader is asked to trust.
open import Once.Adequacy public using (CorrectCompiler)
