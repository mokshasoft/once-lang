-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Semantics.Machine.Laws
--
-- Machine-level (ℕ) instance of the value-semantics LAWS — the `ℕ`
open import Once.Float.Dyadic using (Dyadic)
-- counterpart of `Once.Semantics.Machine` for `Once.Semantics.Value.Laws`.
-- Consumers that need the identity laws (`sem-cata-In-id`, `sem-ana-Out-id`,
-- `sem-CoIn-CoOut`) import this; the definitions themselves stay in
-- `Once.Semantics.Machine` (Plan 0.47 step 3).
------------------------------------------------------------------------

module Once.Semantics.Machine.Laws where

open import Data.Nat using (ℕ)

open import Once.Word using (Carrier)
open import Once.Semantics.Value.Laws Carrier Dyadic public
