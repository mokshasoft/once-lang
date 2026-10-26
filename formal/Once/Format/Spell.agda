-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Format.Spell — how each token of the Spec's lexing is written
-- (plan 0.124 step 4.0).
--
-- The formatter's document holds Spec tokens, not text, so that what it
-- writes is, by construction, a sequence of tokens and the blanks and
-- comments between them; `spell` is the text of one token. A float is written
-- with its fraction's leading zeros (`TFloat i f l`: `l` digits). The digits are
-- computed here, not by `show`, so that reading them back is a theorem.
------------------------------------------------------------------------

module Once.Format.Spell where

open import Data.Bool using (if_then_else_)
open import Data.Char using (Char)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (List; []; _∷_; _++_)
open import Data.Nat using (ℕ; zero; suc; _<ᵇ_; _/_; _%_)
open import Data.String using (String; fromList) renaming (_++_ to _++ˢ_)

open import Once.Spec.Surface.Lexing using (Token; TWord; TInt; TFloat; TString; TLParen; TRParen; TLBrace;
  TRBrace; TColon; TEquals; TArrow; TCaret1; TCaret0; TCaretW; TLambda; TComma; TSemicolon; TAt; TPipe;
  TDot; TPlus; TMinus; TStar; TSlash; TPercent; TAmpersand; TLt; TLe; TGt; TGe; TEqEq; TNeq; TBang;
  TNewline; TEOF)

-- A decimal digit.
digit : ℕ → Char
digit 0 = '0'
digit 1 = '1'
digit 2 = '2'
digit 3 = '3'
digit 4 = '4'
digit 5 = '5'
digit 6 = '6'
digit 7 = '7'
digit 8 = '8'
digit 9 = '9'
{-# CATCHALL #-}
digit _ = '0'

-- A number's decimal digits, the fewest (the fuel outlasts them: `n < fuel`).
digits : ℕ → ℕ → List Char
digits zero    n = []
digits (suc f) n = if n <ᵇ 10 then digit n ∷ [] else digits f (n / 10) ++ digit (n % 10) ∷ []

decimal : ℕ → List Char
decimal n = digits (suc n) n

-- The last `l` decimal digits of a number, leading zeros included.
fixed : ℕ → ℕ → List Char
fixed zero    f = []
fixed (suc l) f = fixed l (f / 10) ++ digit (f % 10) ∷ []

showInt : ℤ → String
showInt (+ n)    = fromList (decimal n)
showInt -[1+ n ] = "-" ++ˢ fromList (decimal (suc n))

-- `l` fraction digits.
showFloat : ℕ → ℕ → ℕ → String
showFloat i f l = fromList (decimal i ++ '.' ∷ fixed l f)

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
