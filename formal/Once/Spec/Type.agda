-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Type — the type/functor-type GRAMMAR (OCP-0006, spec).
--
-- SPEC (trust boundary): the alphabet of types a Once program ranges over,
-- including the functor-type constructors (`μ-type`/`ν-type`). Re-exports
-- `Once.Type` verbatim. `Once.Functor.*` (deciders/operations over functors)
-- are IMPLEMENTATION, checked against this grammar, and are NOT re-exported.
------------------------------------------------------------------------

module Once.Spec.Type where

open import Once.Type public
