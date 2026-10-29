-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Machine.ClosureWellFormed — the value relation, at a definition
-- `o` and table `tbl`.
--
-- plan 0.125 S3: the relation is TABLE-FREE (`ValueRel`), so this module only
-- re-exports it; the parameters stay so every client's `ClosureWellFormed o
-- tbl` keeps reading as it did, and every instantiation shares one relation.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)
open import Data.List using (List)
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Machine.ClosureWellFormed (o : CanonicalName) (tbl : List IRFun) where

open import Once.CCC.Machine.ValueRel public
