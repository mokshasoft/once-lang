-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecTokNames — the Spec's operator tokens by their names
-- before plan 0.150 draft C (`TPlus` is `TOp ‹ o+ ›`), and their IEEE forms
-- (`TPlusD` is `TOpD o+`), for the bridges and tables that go token by token.
-- A match on all eleven covers `TOp`, on all ten `TOpD`.
------------------------------------------------------------------------

module Once.Adequacy.SpecTokNames where

open import Once.Spec.Surface.Lexing using (Token; TOp; TOpD)
open import Once.Spec.Surface.Operator using (‹_›; o%; o+; o-; o*; o/; o<; o<=; o>; o>=; o==; o!=)

pattern TPlus    = TOp ‹ o+ ›
pattern TMinus   = TOp ‹ o- ›
pattern TStar    = TOp ‹ o* ›
pattern TSlash   = TOp ‹ o/ ›
pattern TPercent = TOp o%
pattern TLt      = TOp ‹ o< ›
pattern TLe      = TOp ‹ o<= ›
pattern TGt      = TOp ‹ o> ›
pattern TGe      = TOp ‹ o>= ›
pattern TEqEq    = TOp ‹ o== ›
pattern TNeq     = TOp ‹ o!= ›

pattern TPlusD  = TOpD o+
pattern TMinusD = TOpD o-
pattern TStarD  = TOpD o*
pattern TSlashD = TOpD o/
pattern TLtD    = TOpD o<
pattern TLeD    = TOpD o<=
pattern TGtD    = TOpD o>
pattern TGeD    = TOpD o>=
pattern TEqEqD  = TOpD o==
pattern TNeqD   = TOpD o!=
