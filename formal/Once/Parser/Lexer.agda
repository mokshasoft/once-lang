------------------------------------------------------------------------
-- Once.Parser.Lexer
--
-- Tokenizer for the Once language.
-- Converts a string (List Char) into a list of tokens.
------------------------------------------------------------------------

module Once.Parser.Lexer where

open import Data.List using (List; []; _∷_; _++_; reverse)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Bool using (Bool; true; false; _∨_; _∧_; not; if_then_else_)
open import Data.Char using (Char; isAlpha; isDigit; isSpace; isLower)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_; _<ᵇ_)
open import Data.Integer using (ℤ; +_)
open import Data.String using (String; fromList; toList)
open import Agda.Builtin.Char using (primCharEquality; primCharToNat)

-- | Convert Char to ℕ (character code)
toNat : Char → ℕ
toNat = primCharToNat

open import Once.Parser.Token

------------------------------------------------------------------------
-- Character Classification
------------------------------------------------------------------------

-- | Is this character an identifier start? [a-zA-Z_]
isIdentStart : Char → Bool
isIdentStart c = isAlpha c ∨ (toNat c ≡ᵇ toNat '_')

-- | Is this character an identifier continuation? [a-zA-Z0-9_'+*!?]
isIdentContinue : Char → Bool
isIdentContinue c =
  isAlpha c ∨ isDigit c ∨
  (toNat c ≡ᵇ toNat '_') ∨
  (toNat c ≡ᵇ toNat '\'') ∨
  (toNat c ≡ᵇ toNat '+') ∨
  (toNat c ≡ᵇ toNat '*') ∨
  (toNat c ≡ᵇ toNat '!') ∨
  (toNat c ≡ᵇ toNat '?')

-- | Character equality
_==c_ : Char → Char → Bool
c₁ ==c c₂ = primCharEquality c₁ c₂

------------------------------------------------------------------------
-- Lexer Helpers
------------------------------------------------------------------------

-- | Collect identifier continuation characters
collectIdent : List Char → List Char × List Char
collectIdent [] = [] , []
collectIdent (c ∷ cs) with isIdentContinue c
... | true = let (ident , rest) = collectIdent cs
             in  (c ∷ ident) , rest
... | false = [] , (c ∷ cs)

-- | Collect digits
collectDigits : List Char → List Char × List Char
collectDigits [] = [] , []
collectDigits (c ∷ cs) with isDigit c
... | true = let (digits , rest) = collectDigits cs
             in  (c ∷ digits) , rest
... | false = [] , (c ∷ cs)

-- | Convert digit chars to natural number
digitsToNat : List Char → ℕ
digitsToNat = go 0
  where
  charToDigit : Char → ℕ
  charToDigit c = toNat c Data.Nat.∸ toNat '0'

  go : ℕ → List Char → ℕ
  go acc [] = acc
  go acc (c ∷ cs) = go (acc Data.Nat.* 10 Data.Nat.+ charToDigit c) cs

-- | Collect string literal contents (after opening ")
-- Returns the string contents and remaining chars (after closing ")
collectString : List Char → Maybe (List Char × List Char)
collectString [] = nothing  -- unterminated string
collectString ('"' ∷ cs) = just ([] , cs)
collectString ('\\' ∷ 'n' ∷ cs) with collectString cs
... | just (s , rest) = just ('\n' ∷ s , rest)
... | nothing = nothing
collectString ('\\' ∷ 't' ∷ cs) with collectString cs
... | just (s , rest) = just ('\t' ∷ s , rest)
... | nothing = nothing
collectString ('\\' ∷ 'r' ∷ cs) with collectString cs
... | just (s , rest) = just ('\r' ∷ s , rest)
... | nothing = nothing
collectString ('\\' ∷ '\\' ∷ cs) with collectString cs
... | just (s , rest) = just ('\\' ∷ s , rest)
... | nothing = nothing
collectString ('\\' ∷ '"' ∷ cs) with collectString cs
... | just (s , rest) = just ('"' ∷ s , rest)
... | nothing = nothing
collectString (c ∷ cs) with collectString cs
... | just (s , rest) = just (c ∷ s , rest)
... | nothing = nothing

-- | Skip to end of line (for line comments)
skipLine : List Char → List Char
skipLine [] = []
skipLine ('\n' ∷ cs) = '\n' ∷ cs
skipLine (_ ∷ cs) = skipLine cs

-- | Skip block comment (handles nesting)
skipBlock : ℕ → List Char → List Char
skipBlock zero cs = cs
skipBlock (suc _) [] = []  -- unterminated block comment
skipBlock (suc n) ('{' ∷ '-' ∷ cs) = skipBlock (suc (suc n)) cs
skipBlock (suc n) ('-' ∷ '}' ∷ cs) = skipBlock n cs
skipBlock (suc n) (_ ∷ cs) = skipBlock (suc n) cs

------------------------------------------------------------------------
-- Main Tokenizer
------------------------------------------------------------------------

-- | Tokenize a list of characters into tokens.
-- Uses structural recursion on the character list.
{-# TERMINATING #-}
tokenize : List Char → List Token
tokenize [] = TEOF ∷ []

-- Line comments
tokenize ('-' ∷ '-' ∷ cs) = tokenize (skipLine cs)

-- Block comments
tokenize ('{' ∷ '-' ∷ cs) = tokenize (skipBlock 1 cs)

-- Whitespace (non-newline)
tokenize (' '  ∷ cs) = tokenize cs
tokenize ('\t' ∷ cs) = tokenize cs
tokenize ('\r' ∷ cs) = tokenize cs

-- Newlines: only significant if the next line starts at column 0 (not indented).
-- Indented continuation lines are treated as whitespace.
tokenize ('\n' ∷ ' ' ∷ cs) = tokenize (' ' ∷ cs)   -- continuation (space-indented)
tokenize ('\n' ∷ '\t' ∷ cs) = tokenize ('\t' ∷ cs)  -- continuation (tab-indented)
tokenize ('\n' ∷ cs) = TNewline ∷ tokenize cs        -- declaration separator

-- Two-character operators (max munch)
tokenize ('-' ∷ '>' ∷ cs) = TArrow ∷ tokenize cs
tokenize ('<' ∷ '=' ∷ cs) = TLe ∷ tokenize cs
tokenize ('>' ∷ '=' ∷ cs) = TGe ∷ tokenize cs
tokenize ('=' ∷ '=' ∷ cs) = TEqEq ∷ tokenize cs
tokenize ('!' ∷ '=' ∷ cs) = TNeq ∷ tokenize cs

-- Single-character punctuation
tokenize ('(' ∷ cs) = TLParen ∷ tokenize cs
tokenize (')' ∷ cs) = TRParen ∷ tokenize cs
tokenize ('{' ∷ cs) = TLBrace ∷ tokenize cs
tokenize ('}' ∷ cs) = TRBrace ∷ tokenize cs
tokenize (':' ∷ cs) = TColon ∷ tokenize cs
tokenize ('=' ∷ cs) = TEquals ∷ tokenize cs
tokenize ('\\' ∷ cs) = TLambda ∷ tokenize cs
tokenize (',' ∷ cs) = TComma ∷ tokenize cs
tokenize (';' ∷ cs) = TSemicolon ∷ tokenize cs
tokenize ('@' ∷ cs) = TAt ∷ tokenize cs
tokenize ('|' ∷ cs) = TPipe ∷ tokenize cs

-- Operators
tokenize ('+' ∷ cs) = TPlus ∷ tokenize cs
tokenize ('-' ∷ cs) = TMinus ∷ tokenize cs
tokenize ('*' ∷ cs) = TStar ∷ tokenize cs
tokenize ('/' ∷ cs) = TSlash ∷ tokenize cs
tokenize ('%' ∷ cs) = TPercent ∷ tokenize cs
tokenize ('&' ∷ cs) = TAmpersand ∷ tokenize cs
tokenize ('<' ∷ cs) = TLt ∷ tokenize cs
tokenize ('>' ∷ cs) = TGt ∷ tokenize cs
tokenize ('.' ∷ cs) = TDot ∷ tokenize cs

-- String literals
tokenize ('"' ∷ cs) with collectString cs
... | just (s , rest) = TString (fromList s) ∷ tokenize rest
... | nothing = []  -- error: unterminated string

-- Integer literals
tokenize (c ∷ cs) with isDigit c
... | true = let (digits , rest) = collectDigits cs
                 n = digitsToNat (c ∷ digits)
             in  TInt (+ n) ∷ tokenize rest

-- Identifiers (start with alpha or _)
... | false with isIdentStart c
...   | true = let (ident , rest) = collectIdent cs
               in  TWord (fromList (c ∷ ident)) ∷ tokenize rest

-- Unknown character: skip
...   | false = tokenize cs

------------------------------------------------------------------------
-- Entry Point
------------------------------------------------------------------------

-- | Tokenize a string
tokenizeString : String → List Token
tokenizeString s = tokenize (toList s)
