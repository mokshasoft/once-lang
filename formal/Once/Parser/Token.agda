-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Parser.Token
--
-- Token type for the Once lexer/parser.
-- Produced by the tokenizer, consumed by the parser.
------------------------------------------------------------------------

module Once.Parser.Token where

open import Data.String using (String)
open import Data.Integer using (ℤ)

------------------------------------------------------------------------
-- Tokens
------------------------------------------------------------------------

data Token : Set where
  -- Identifiers and literals
  TWord    : String → Token     -- identifier or keyword (fst, swap, Unit, import, assocL+)
  TInt     : ℤ → Token          -- integer literal
  TString  : String → Token     -- string literal

  -- Punctuation
  TLParen  : Token              -- (
  TRParen  : Token              -- )
  TLBrace  : Token              -- {
  TRBrace  : Token              -- }
  TColon   : Token              -- :
  TEquals  : Token              -- =
  TArrow   : Token              -- ->
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

  -- Structure
  TNewline : Token              -- significant newline
  TEOF     : Token              -- end of file