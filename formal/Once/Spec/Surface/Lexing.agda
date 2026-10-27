{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Surface.Lexing — which token stream a text is.
--
-- `Lexes text ts`: reading `text` left to right gives the tokens `ts`.
-- Blanks are skipped; a newline is a token unless the next line is indented
-- (then it continues the line); `--` starts a comment to the end of the line,
-- `{-` a nested comment closed by `-}`. Two-character operators (`->`, `<=`,
-- `>=`, `==`, `!=`, `^0`, `^1`, `^w`) are one token. A number is an integer or,
-- with a `.` and a digit, a decimal; an identifier starts with a letter or
-- `_`. Nothing is dropped silently: a text is lexed to its end, so its
-- tokens end in `TEOF`, and one with an unterminated string literal, a `^`
-- that is not a grade, or a character that starts nothing has no token
-- stream.
------------------------------------------------------------------------

module Once.Spec.Surface.Lexing where

open import Agda.Builtin.Char using (primCharToNat)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Char using (Char; isAlpha; isDigit)
open import Data.Integer using (ℤ; +_)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc; _∸_; _*_; _+_; _≡ᵇ_)
open import Data.Product using (_×_; ∃-syntax)
import Data.Sum as Sum
open import Data.String using (String; toList; fromList)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- Tokens
------------------------------------------------------------------------

data Token : Set where
  TWord      : String → Token          -- an identifier or keyword
  TInt       : ℤ → Token               -- an integer literal
  TFloat     : ℕ → ℕ → ℕ → Token       -- a decimal: integer part, fraction digits, their number
  TString    : String → Token          -- a string literal
  TLParen TRParen TLBrace TRBrace               : Token   -- ( ) { }
  TColon TEquals TArrow                         : Token   -- : = ->
  TCaret1 TCaret0 TCaretW                       : Token   -- ^1 ^0 ^w
  TLambda TComma TSemicolon TAt TPipe TDot      : Token   -- \ , ; @ | .
  TPlus TMinus TStar TSlash TPercent TAmpersand : Token   -- + - * / % &
  TLt TLe TGt TGe TEqEq TNeq TBang              : Token   -- < <= > >= == != !
  TNewline TEOF                                 : Token

------------------------------------------------------------------------
-- Characters
------------------------------------------------------------------------

private
  code : Char → ℕ
  code = primCharToNat

isIdentStart : Char → Bool
isIdentStart c = isAlpha c ∨ (code c ≡ᵇ code '_')

isIdentContinue : Char → Bool
isIdentContinue c =
  isAlpha c ∨ isDigit c ∨ (code c ≡ᵇ code '_') ∨ (code c ≡ᵇ code '\'')
  ∨ (code c ≡ᵇ code '+') ∨ (code c ≡ᵇ code '*') ∨ (code c ≡ᵇ code '!') ∨ (code c ≡ᵇ code '?')

-- The value of decimal digits after those of value `a`.
digitsFrom : ℕ → List Char → ℕ
digitsFrom a []       = a
digitsFrom a (c ∷ cs) = digitsFrom (a * 10 + (code c ∸ code '0')) cs

-- The value of a list of decimal digits.
digitsToNat : List Char → ℕ
digitsToNat = digitsFrom 0

-- The characters that begin something other than a number or an identifier.
data Special : Char → Set where
  sp-space : Special ' '
  sp-tab : Special '\t'
  sp-cr : Special '\r'
  sp-nl : Special '\n'
  sp-backslash : Special '\\'
  sp-caret : Special '^'
  sp-dash : Special '-'
  sp-lbrace : Special '{'
  sp-lt : Special '<'
  sp-gt : Special '>'
  sp-eq : Special '='
  sp-bang : Special '!'
  sp-lparen : Special '('
  sp-rparen : Special ')'
  sp-rbrace : Special '}'
  sp-colon : Special ':'
  sp-comma : Special ','
  sp-semi : Special ';'
  sp-at : Special '@'
  sp-pipe : Special '|'
  sp-plus : Special '+'
  sp-star : Special '*'
  sp-slash : Special '/'
  sp-pct : Special '%'
  sp-amp : Special '&'
  sp-dot : Special '.'
  sp-quote : Special '"'

-- The first character of a list.
data Next : List Char → Char → Set where
  next : ∀ {c cs} → Next (c ∷ cs) c

------------------------------------------------------------------------
-- Pieces of a token
------------------------------------------------------------------------

-- The longest prefix of digits, and what follows it.
data Digits : List Char → List Char → List Char → Set where
  dg-end  : Digits [] [] []
  dg-stop : ∀ {c cs} → isDigit c ≡ false → Digits (c ∷ cs) [] (c ∷ cs)
  dg-more : ∀ {c cs ds r} → isDigit c ≡ true → Digits cs ds r → Digits (c ∷ cs) (c ∷ ds) r

-- A fraction: `.` and at least one digit.
data Fraction : List Char → List Char → List Char → Set where
  fraction : ∀ {d cs ds r} → isDigit d ≡ true → Digits cs ds r → Fraction ('.' ∷ d ∷ cs) (d ∷ ds) r

-- The longest prefix of identifier characters.
data IdentRest : List Char → List Char → List Char → Set where
  id-end  : IdentRest [] [] []
  id-stop : ∀ {c cs} → isIdentContinue c ≡ false → IdentRest (c ∷ cs) [] (c ∷ cs)
  id-more : ∀ {c cs i r} → isIdentContinue c ≡ true → IdentRest cs i r → IdentRest (c ∷ cs) (c ∷ i) r

-- A string literal's body up to its closing quote, with its escapes read.
data Escape : Char → Char → Set where
  esc-n  : Escape 'n' '\n'
  esc-t  : Escape 't' '\t'
  esc-r  : Escape 'r' '\r'
  esc-bs : Escape '\\' '\\'
  esc-q  : Escape '"' '"'

data StringBody : List Char → List Char → List Char → Set where
  sb-close : ∀ {cs} → StringBody ('"' ∷ cs) [] cs
  sb-esc   : ∀ {e c cs s r} → Escape e c → StringBody cs s r → StringBody ('\\' ∷ e ∷ cs) (c ∷ s) r
  sb-char  : ∀ {c cs s r} → c ≢ '"' → ¬ (c ≡ '\\' × ∃[ e ] ∃[ x ] (Next cs e × Escape e x))
           → StringBody cs s r → StringBody (c ∷ cs) (c ∷ s) r

-- A line comment's text: everything up to (not including) the newline.
data LineRest : List Char → List Char → Set where
  lr-end  : LineRest [] []
  lr-nl   : ∀ {cs} → LineRest ('\n' ∷ cs) ('\n' ∷ cs)
  lr-char : ∀ {c cs r} → c ≢ '\n' → LineRest cs r → LineRest (c ∷ cs) r

-- A nested comment at depth `n`: what follows its matching closes.
data BlockRest : ℕ → List Char → List Char → Set where
  br-done  : ∀ {cs} → BlockRest zero cs cs
  br-end   : ∀ {n} → BlockRest (suc n) [] []
  br-last  : ∀ {n c} → BlockRest (suc n) (c ∷ []) []
  br-open  : ∀ {n cs r} → BlockRest (suc (suc n)) cs r → BlockRest (suc n) ('{' ∷ '-' ∷ cs) r
  br-close : ∀ {n cs r} → BlockRest n cs r → BlockRest (suc n) ('-' ∷ '}' ∷ cs) r
  br-char  : ∀ {n c₁ c₂ cs r} → ¬ (c₁ ≡ '{' × c₂ ≡ '-') → ¬ (c₁ ≡ '-' × c₂ ≡ '}')
           → BlockRest (suc n) (c₂ ∷ cs) r → BlockRest (suc n) (c₁ ∷ c₂ ∷ cs) r

------------------------------------------------------------------------
-- The token stream
------------------------------------------------------------------------

data LexesChars : List Char → List Token → Set where
  lex-eof : LexesChars [] (TEOF ∷ [])
  -- blanks
  lex-space : ∀ {cs ts} → LexesChars cs ts → LexesChars (' ' ∷ cs) ts
  lex-tab   : ∀ {cs ts} → LexesChars cs ts → LexesChars ('\t' ∷ cs) ts
  lex-cr    : ∀ {cs ts} → LexesChars cs ts → LexesChars ('\r' ∷ cs) ts
  -- a newline continues the line when the next one is indented
  lex-nl-cont : ∀ {cs c ts} → Next cs c → (c ≡ ' ' Sum.⊎ c ≡ '\t') → LexesChars cs ts → LexesChars ('\n' ∷ cs) ts
  lex-nl      : ∀ {cs ts} → ¬ (Next cs ' ') → ¬ (Next cs '\t') → LexesChars cs ts → LexesChars ('\n' ∷ cs) (TNewline ∷ ts)
  -- grades
  lex-caret1  : ∀ {cs ts} → LexesChars cs ts → LexesChars ('^' ∷ '1' ∷ cs) (TCaret1 ∷ ts)
  lex-caret0  : ∀ {cs ts} → LexesChars cs ts → LexesChars ('^' ∷ '0' ∷ cs) (TCaret0 ∷ ts)
  lex-caretw  : ∀ {cs ts} → LexesChars cs ts → LexesChars ('^' ∷ 'w' ∷ cs) (TCaretW ∷ ts)
  -- `--`, `->`, `-`
  lex-comment : ∀ {cs r ts} → LineRest cs r → LexesChars r ts → LexesChars ('-' ∷ '-' ∷ cs) ts
  lex-arrow   : ∀ {cs ts} → LexesChars cs ts → LexesChars ('-' ∷ '>' ∷ cs) (TArrow ∷ ts)
  lex-minus   : ∀ {cs ts} → ¬ Next cs '-' → ¬ Next cs '>' → LexesChars cs ts → LexesChars ('-' ∷ cs) (TMinus ∷ ts)
  -- `{-`, `{`
  lex-block  : ∀ {cs r ts} → BlockRest 1 cs r → LexesChars r ts → LexesChars ('{' ∷ '-' ∷ cs) ts
  lex-lbrace : ∀ {cs ts} → ¬ Next cs '-' → LexesChars cs ts → LexesChars ('{' ∷ cs) (TLBrace ∷ ts)
  -- `x=` operators
  lex-le    : ∀ {cs ts} → LexesChars cs ts → LexesChars ('<' ∷ '=' ∷ cs) (TLe ∷ ts)
  lex-lt    : ∀ {cs ts} → ¬ Next cs '=' → LexesChars cs ts → LexesChars ('<' ∷ cs) (TLt ∷ ts)
  lex-ge    : ∀ {cs ts} → LexesChars cs ts → LexesChars ('>' ∷ '=' ∷ cs) (TGe ∷ ts)
  lex-gt    : ∀ {cs ts} → ¬ Next cs '=' → LexesChars cs ts → LexesChars ('>' ∷ cs) (TGt ∷ ts)
  lex-eqeq  : ∀ {cs ts} → LexesChars cs ts → LexesChars ('=' ∷ '=' ∷ cs) (TEqEq ∷ ts)
  lex-equal : ∀ {cs ts} → ¬ Next cs '=' → LexesChars cs ts → LexesChars ('=' ∷ cs) (TEquals ∷ ts)
  lex-neq   : ∀ {cs ts} → LexesChars cs ts → LexesChars ('!' ∷ '=' ∷ cs) (TNeq ∷ ts)
  lex-bang  : ∀ {cs ts} → ¬ Next cs '=' → LexesChars cs ts → LexesChars ('!' ∷ cs) (TBang ∷ ts)
  -- one-character tokens
  lex-lparen : ∀ {cs ts} → LexesChars cs ts → LexesChars ('(' ∷ cs) (TLParen ∷ ts)
  lex-rparen : ∀ {cs ts} → LexesChars cs ts → LexesChars (')' ∷ cs) (TRParen ∷ ts)
  lex-rbrace : ∀ {cs ts} → LexesChars cs ts → LexesChars ('}' ∷ cs) (TRBrace ∷ ts)
  lex-colon  : ∀ {cs ts} → LexesChars cs ts → LexesChars (':' ∷ cs) (TColon ∷ ts)
  lex-lambda : ∀ {cs ts} → LexesChars cs ts → LexesChars ('\\' ∷ cs) (TLambda ∷ ts)
  lex-comma  : ∀ {cs ts} → LexesChars cs ts → LexesChars (',' ∷ cs) (TComma ∷ ts)
  lex-semi   : ∀ {cs ts} → LexesChars cs ts → LexesChars (';' ∷ cs) (TSemicolon ∷ ts)
  lex-at     : ∀ {cs ts} → LexesChars cs ts → LexesChars ('@' ∷ cs) (TAt ∷ ts)
  lex-pipe   : ∀ {cs ts} → LexesChars cs ts → LexesChars ('|' ∷ cs) (TPipe ∷ ts)
  lex-plus   : ∀ {cs ts} → LexesChars cs ts → LexesChars ('+' ∷ cs) (TPlus ∷ ts)
  lex-star   : ∀ {cs ts} → LexesChars cs ts → LexesChars ('*' ∷ cs) (TStar ∷ ts)
  lex-slash  : ∀ {cs ts} → LexesChars cs ts → LexesChars ('/' ∷ cs) (TSlash ∷ ts)
  lex-pct    : ∀ {cs ts} → LexesChars cs ts → LexesChars ('%' ∷ cs) (TPercent ∷ ts)
  lex-amp    : ∀ {cs ts} → LexesChars cs ts → LexesChars ('&' ∷ cs) (TAmpersand ∷ ts)
  lex-dot    : ∀ {cs ts} → LexesChars cs ts → LexesChars ('.' ∷ cs) (TDot ∷ ts)
  -- string literals
  lex-string : ∀ {cs s r ts} → StringBody cs s r → LexesChars r ts
             → LexesChars ('"' ∷ cs) (TString (fromList s) ∷ ts)
  -- numbers
  lex-int   : ∀ {c cs ds r ts} → isDigit c ≡ true → Digits cs ds r → ¬ (∃[ f ] ∃[ r′ ] Fraction r f r′)
            → LexesChars r ts → LexesChars (c ∷ cs) (TInt (+ digitsToNat (c ∷ ds)) ∷ ts)
  lex-float : ∀ {c cs ds r f r′ ts} → isDigit c ≡ true → Digits cs ds r → Fraction r f r′
            → LexesChars r′ ts → LexesChars (c ∷ cs) (TFloat (digitsToNat (c ∷ ds)) (digitsToNat f) (length f) ∷ ts)
  -- identifiers
  lex-ident : ∀ {c cs i r ts} → ¬ Special c → isDigit c ≡ false → isIdentStart c ≡ true
            → IdentRest cs i r → LexesChars r ts → LexesChars (c ∷ cs) (TWord (fromList (c ∷ i)) ∷ ts)

Lexes : String → List Token → Set
Lexes text ts = LexesChars (toList text) ts
