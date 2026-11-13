{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Surface.Operator — the infix operators, once.
--
-- Eleven operators, `+ - * / % < <= > >= == !=`. Each but `%` has an IEEE
-- form at `Float`, written with a trailing `.` (`+.`, `<=.`, …; plan 0.150
-- N7, N8). How an operator is spelled is `Spec.Surface.Lexing.Glyph`; how
-- tightly it binds is `level` here; what it means is its symbol, `binSym`
-- here (`Spec.Theory`; typed by `Spec.Surface.Typing`).
------------------------------------------------------------------------

module Once.Spec.Surface.Operator where

open import Once.Spec.Theory
  using (Theory; Ring; Division; Order; Equality; Rounded; Shape; binary; compare; Sym;
         ‵+; ‵-; ‵*; ‵/; ‵%; ‵<; ‵<=; ‵>; ‵>=; ‵==; ‵!=; ‵+ᵈ; ‵-ᵈ; ‵*ᵈ; ‵/ᵈ; ‵==ᵈ; ‵!=ᵈ; ‵<ᵈ; ‵<=ᵈ; ‵>ᵈ; ‵>=ᵈ)

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

------------------------------------------------------------------------
-- What an operator means: its theory's symbol
------------------------------------------------------------------------

-- Each binary operator is a symbol of one theory (`Spec.Theory`).
record BinSym : Set where
  constructor _∶_∶_
  field
    theory : Theory
    shape  : Shape
    symbol : Sym theory shape
open BinSym

binSym : BinOp → BinSym
binSym (plain ‹ o+ ›)  = Ring     ∶ binary  ∶ ‵+
binSym (plain ‹ o- ›)  = Ring     ∶ binary  ∶ ‵-
binSym (plain ‹ o* ›)  = Ring     ∶ binary  ∶ ‵*
binSym (plain ‹ o/ ›)  = Division ∶ binary  ∶ ‵/
binSym (plain o%)      = Division ∶ binary  ∶ ‵%
binSym (plain ‹ o< ›)  = Order    ∶ compare ∶ ‵<
binSym (plain ‹ o<= ›) = Order    ∶ compare ∶ ‵<=
binSym (plain ‹ o> ›)  = Order    ∶ compare ∶ ‵>
binSym (plain ‹ o>= ›) = Order    ∶ compare ∶ ‵>=
binSym (plain ‹ o== ›) = Equality ∶ compare ∶ ‵==
binSym (plain ‹ o!= ›) = Equality ∶ compare ∶ ‵!=
binSym (dotted o+)     = Rounded  ∶ binary  ∶ ‵+ᵈ
binSym (dotted o-)     = Rounded  ∶ binary  ∶ ‵-ᵈ
binSym (dotted o*)     = Rounded  ∶ binary  ∶ ‵*ᵈ
binSym (dotted o/)     = Rounded  ∶ binary  ∶ ‵/ᵈ
binSym (dotted o<)     = Rounded  ∶ compare ∶ ‵<ᵈ
binSym (dotted o<=)    = Rounded  ∶ compare ∶ ‵<=ᵈ
binSym (dotted o>)     = Rounded  ∶ compare ∶ ‵>ᵈ
binSym (dotted o>=)    = Rounded  ∶ compare ∶ ‵>=ᵈ
binSym (dotted o==)    = Rounded  ∶ compare ∶ ‵==ᵈ
binSym (dotted o!=)    = Rounded  ∶ compare ∶ ‵!=ᵈ
