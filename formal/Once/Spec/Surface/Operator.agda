{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Surface.Operator — the infix operators, once.
--
-- Eleven operators, `+ - * / % < <= > >= == !=`. Each but `%` has an IEEE
-- form at `Float`, written with a trailing `.` (`+.`, `<=.`, …; plan 0.150
-- N7, N8). How an operator is spelled is `Spec.Surface.Lexing.Glyph`; how
-- tightly it binds is `level` here; what it means is
-- `Spec.Surface.Typing.binSym`.
------------------------------------------------------------------------

module Once.Spec.Surface.Operator where

-- | The operators with an IEEE form.
data Dottable : Set where
  o+ o- o* o/ o< o<= o> o>= o== o!= : Dottable

-- | Every operator: one with an IEEE form, or `%`.
data Op : Set where
  ‹_› : Dottable → Op
  o%  : Op

-- | An infix operator as used: plain, or its IEEE form.
data BinOp : Set where
  plain  : Op → BinOp
  dotted : Dottable → BinOp

-- | How tightly an operator binds: a comparison (at most one, unchained), an
-- additive one, a multiplicative one; each binds tighter than the one before.
data Level : Set where
  comparison additive multiplicative : Level

level : Op → Level
level ‹ o+ ›  = additive
level ‹ o- ›  = additive
level ‹ o* ›  = multiplicative
level ‹ o/ ›  = multiplicative
level o%      = multiplicative
level ‹ o< ›  = comparison
level ‹ o<= › = comparison
level ‹ o> ›  = comparison
level ‹ o>= › = comparison
level ‹ o== › = comparison
level ‹ o!= › = comparison
