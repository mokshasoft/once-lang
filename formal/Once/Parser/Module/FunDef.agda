-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Parser.Module.FunDef
--
-- Function-definition parser: parameter list, body, and the
-- operator-form declaration that may follow `(op)`. This file is a
-- pure re-exporter: the implementation is split across
-- `FunDef.Params`, `FunDef.Body`, and `FunDef.OpDecl` to cap the per-
-- file work MAlonzo does when lowering to Haskell (a single combined
-- file OOM-killed extraction).
------------------------------------------------------------------------

module Once.Parser.Module.FunDef where

open import Once.Parser.Module.FunDef.Params public
open import Once.Parser.Module.FunDef.Body public
open import Once.Parser.Module.FunDef.Def public
open import Once.Parser.Module.FunDef.OpDecl public
