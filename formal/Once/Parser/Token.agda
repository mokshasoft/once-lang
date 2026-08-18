-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Parser.Token
--
-- Token type for the Once lexer/parser.
-- Produced by the tokenizer, consumed by the parser.
------------------------------------------------------------------------

module Once.Parser.Token where

open import Data.String using (String)
open import Data.Integer using (ℤ)
open import Data.Nat using (ℕ)

------------------------------------------------------------------------
-- Tokens
------------------------------------------------------------------------

data Token : Set where
  -- Identifiers and literals
  TWord    : String → Token     -- identifier or keyword (fst, swap, Unit, import, assocL+)
  TInt     : ℤ → Token          -- integer literal
  -- PLAN 0.71: a float literal, carried as DIGITS rather than as a value —
  -- integer part, fraction digits, and the fraction's LENGTH. Three reasons it
  -- is not an `AgdaFloat` here:
  --   * a value would mean the LEXER already rounded, and the representability
  --     check (F4) needs the exact decimal to decide against;
  --   * `1.50` and `1.5` must stay distinct for the printer round-trip, which
  --     the length is what preserves;
  --   * Agda's `Float` is a double, and D109 made the width a TARGET property
  --     — the frontend must not bake the widest target into the language.
  -- The value denoted is `int + frac / 10 ^ flen`, exactly; nothing here
  -- rounds. Dyadic conversion and the acceptance check are F4's.
  TFloat   : ℕ → ℕ → ℕ → Token  -- int part, fraction digits, fraction length
  TString  : String → Token     -- string literal

  -- Punctuation
  TLParen  : Token              -- (
  TRParen  : Token              -- )
  TLBrace  : Token              -- {
  TRBrace  : Token              -- }
  TColon   : Token              -- :
  TEquals  : Token              -- =
  TArrow   : Token              -- ->         (unrestricted by default; preceding type may add ^q)
  TCaret1  : Token              -- ^1         (linear grade on argument type)
  TCaret0  : Token              -- ^0         (erased grade on argument type)
  TCaretW  : Token              -- ^w         (explicit unrestricted grade)
  TLambda  : Token              -- \
  TComma   : Token              -- ,
  TSemicolon : Token            -- ;
  TAt      : Token              -- @
  TPipe    : Token              -- |
  TDot     : Token              -- .

  -- Arithmetic/logical operators
  TPlus    : Token              -- +
  TMinus   : Token              -- -
  TStar    : Token              -- *
  TSlash   : Token              -- /
  TPercent : Token              -- %
  TAmpersand : Token            -- &

  -- Comparison operators
  TLt      : Token              -- <
  TLe      : Token              -- <=
  TGt      : Token              -- >
  TGe      : Token              -- >=
  TEqEq    : Token              -- ==
  TNeq     : Token              -- !=
  TBang    : Token              -- !          (EffectShape delimiter: `! halts`)

  -- Structure
  TNewline : Token              -- significant newline
  TEOF     : Token              -- end of file