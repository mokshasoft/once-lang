-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Surface.OpNames — the plain operators by their names before plan
-- 0.150 (`OpAdd` is `plain ‹ o+ ›`), for the parser and the printer, which
-- read and write them one by one. A match on all eleven covers `plain`.
------------------------------------------------------------------------

module Once.Surface.OpNames where

open import Once.Spec.Surface.Operator using (BinOp; plain; dotted; ‹_›; o%; o+; o-; o*; o/; o<; o<=; o>; o>=; o==; o!=)

pattern OpAdd = plain ‹ o+ ›
pattern OpSub = plain ‹ o- ›
pattern OpMul = plain ‹ o* ›
pattern OpDiv = plain ‹ o/ ›
pattern OpMod = plain o%
pattern OpLt  = plain ‹ o< ›
pattern OpLe  = plain ‹ o<= ›
pattern OpGt  = plain ‹ o> ›
pattern OpGe  = plain ‹ o>= ›
pattern OpEq  = plain ‹ o== ›
pattern OpNe  = plain ‹ o!= ›
