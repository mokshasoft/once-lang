-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecGrammar.Conv — the compiler's types read as the Spec's.
--
-- `toTy` and `toPolyG` send a type the annotation and alias parsers
-- produce to the Spec's; a `rigid` parameter is never parsed, and goes
-- anywhere.
------------------------------------------------------------------------

module Once.Adequacy.SpecGrammar.Conv where

import Once.Internal.Type as LT
import Once.Spec.Type as LT
import Once.Spec.Type as LT
import Once.Spec.Surface.Syntax as LP
import Once.Internal.Type.Poly as LP
import Once.Spec.Type as ST
import Once.Spec.Surface.Syntax as SS

-- Schemas.
toPoly : LP.PolyType → SS.PolyType
toPoly A = A

toPolyF : LP.PolyFunctor → SS.PolyFunctor
toPolyF F = F

-- Ground types, as the Spec's types: the same (plan 0.122).
toTy  : LT.Type → ST.Type
toTy A = A

toFun : LT.Fun 0 → ST.Fun 0
toFun F = F
