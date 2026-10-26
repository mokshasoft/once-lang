-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Format.Spell — how each token of the Spec's lexing is written
-- (plan 0.124 step 4.0).
--
-- The formatter's document holds Spec tokens, not text, so that what it
-- writes is, by construction, a sequence of tokens and the blanks and
-- comments between them; `spell` is the text of one token. A float is written
-- with its fraction's leading zeros (`TFloat i f l`: `l` digits).
------------------------------------------------------------------------

module Once.Format.Spell where

open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (replicate)
open import Data.Nat using (ℕ; suc; _∸_)
import Data.Nat.Show as ℕS
open import Data.String using (String; fromList; length) renaming (_++_ to _++ˢ_)

open import Once.Spec.Surface.Lexing using (Token; TWord; TInt; TFloat; TString; TLParen; TRParen; TLBrace;
  TRBrace; TColon; TEquals; TArrow; TCaret1; TCaret0; TCaretW; TLambda; TComma; TSemicolon; TAt; TPipe;
  TDot; TPlus; TMinus; TStar; TSlash; TPercent; TAmpersand; TLt; TLe; TGt; TGe; TEqEq; TNeq; TBang;
  TNewline; TEOF)

showInt : ℤ → String
showInt (+ n)    = ℕS.show n
showInt -[1+ n ] = "-" ++ˢ ℕS.show (suc n)

-- `l` fraction digits, the leading ones zeros.
showFloat : ℕ → ℕ → ℕ → String
showFloat i f l = ℕS.show i ++ˢ "." ++ˢ fromList (replicate (l ∸ length (ℕS.show f)) '0') ++ˢ ℕS.show f

spell : Token → String
spell (TWord s)       = s
spell (TInt z)        = showInt z
spell (TFloat i f l)  = showFloat i f l
spell (TString s)     = "\"" ++ˢ s ++ˢ "\""
spell TLParen         = "("
spell TRParen         = ")"
spell TLBrace         = "{"
spell TRBrace         = "}"
spell TColon          = ":"
spell TEquals         = "="
spell TArrow          = "->"
spell TCaret1         = "^1"
spell TCaret0         = "^0"
spell TCaretW         = "^w"
spell TLambda         = "\\"
spell TComma          = ","
spell TSemicolon      = ";"
spell TAt             = "@"
spell TPipe           = "|"
spell TDot            = "."
spell TPlus           = "+"
spell TMinus          = "-"
spell TStar           = "*"
spell TSlash          = "/"
spell TPercent        = "%"
spell TAmpersand      = "&"
spell TLt             = "<"
spell TLe             = "<="
spell TGt             = ">"
spell TGe             = ">="
spell TEqEq           = "=="
spell TNeq            = "!="
spell TBang           = "!"
spell TNewline        = "\n"
spell TEOF            = ""
