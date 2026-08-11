-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Parser.Module.OpName
--
-- Operator-name parser: `(` operator-chars `)`.
------------------------------------------------------------------------

module Once.Parser.Module.OpName where

open import Data.Char using (Char)
import Data.String
open import Data.List using (reverse)

open import Once.Parser.Module.Core

-- | Classifier: an operator-char token to its char, the closing paren, or
-- neither. Routes `parseOpCharsB` so the bridge dispatches in 3 cases, not 12.
data OpTok : Set where
  otClose : OpTok
  otChar  : Char → OpTok
  otNone  : OpTok

opTokClass : Token → OpTok
opTokClass TRParen    = otClose
opTokClass TDot       = otChar '.'
opTokClass TPlus      = otChar '+'
opTokClass TMinus     = otChar '-'
opTokClass TStar      = otChar '*'
opTokClass TSlash     = otChar '/'
opTokClass TPercent   = otChar '%'
opTokClass TLt        = otChar '<'
opTokClass TGt        = otChar '>'
opTokClass TPipe      = otChar '|'
opTokClass TAmpersand = otChar '&'
opTokClass TAt        = otChar '@'
opTokClass _          = otNone

-- | Bounded variant of `parseOpChars`: scans operator characters until
-- the closing paren. Each recursion shrinks by one token (structural on the
-- tail), so the residual is strictly shorter than the input.
-- De-`with`'d: the recursive result is a parameter of `pocStep`, so the bridge
-- can drive the reduction by casing that result.
pocStep : (tok : Token) (rest : List Token) → ParseAtB {String} rest → ParseAtB {String} (tok ∷ rest)
pocStep tok rest nothing                  = nothing
pocStep tok rest (just (s , rest' , bnd)) = just (s , rest' , <-trans bnd (s≤s ≤-refl))

-- The close case, split on the accumulator. Kept separate so `pocGo` splits on
-- the OpTok FIRST (otherwise `pocGo … (otChar ch)` is stuck on a variable `cs`).
pocClose : (tok : Token) (rest : List Token) → List Char → ParseAtB {String} (tok ∷ rest)
pocClose tok rest []       = nothing   -- empty operator
pocClose tok rest (c ∷ cs) = just (Data.String.fromList (reverse (c ∷ cs)) , rest , s≤s ≤-refl)

mutual
  parseOpCharsB : (toks : List Token) → List Char → ParseAtB {String} toks
  parseOpCharsB []          cs = nothing
  parseOpCharsB (tok ∷ rest) cs = pocGo tok rest cs (opTokClass tok)

  pocGo : (tok : Token) (rest : List Token) (cs : List Char) → OpTok → ParseAtB {String} (tok ∷ rest)
  pocGo tok rest cs (otChar ch) = pocStep tok rest (parseOpCharsB rest (ch ∷ cs))
  pocGo tok rest cs otNone      = nothing
  pocGo tok rest cs otClose     = pocClose tok rest cs

-- | Collect operator characters between parens (plain).
parseOpChars : List Token → List Char → Maybe (String × List Token)
parseOpChars toks cs with parseOpCharsB toks cs
... | just (s , rest , _) = just (s , rest)
... | nothing = nothing

-- | Bounded variant: on success consumes `(` + operator chars + `)`.
parseOperatorNameB : (toks : List Token) → ParseAtB {String} toks
parseOperatorNameB (TLParen ∷ rest) with parseOpCharsB rest []
... | just (s , rest' , bnd) = just (s , rest' , <-trans bnd (s≤s ≤-refl))
... | nothing = nothing
parseOperatorNameB _ = nothing

-- | Parse an operator name: (.) (&) (|>) etc.
parseOperatorName : Parser String
parseOperatorName toks with parseOperatorNameB toks
... | just (s , rest , _) = just (s , rest)
... | nothing = nothing
