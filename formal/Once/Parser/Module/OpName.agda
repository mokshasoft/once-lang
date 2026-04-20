-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

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

-- | Bounded variant of `parseOpChars`: scans operator characters until
-- the closing paren. Each recursion shrinks by one token, so the
-- residual is strictly shorter than the input.
parseOpCharsB : (toks : List Token) → List Char → ParseAtB {String} toks
parseOpCharsB (TRParen ∷ rest) [] = nothing  -- empty operator
parseOpCharsB (TRParen ∷ rest) (c ∷ cs) =
  just (Data.String.fromList (reverse (c ∷ cs)) , rest , s≤s ≤-refl)
parseOpCharsB (TDot ∷ rest) cs with parseOpCharsB rest ('.' ∷ cs)
... | just (s , rest' , bnd) = just (s , rest' , <-trans bnd (s≤s ≤-refl))
... | nothing = nothing
parseOpCharsB (TPlus ∷ rest) cs with parseOpCharsB rest ('+' ∷ cs)
... | just (s , rest' , bnd) = just (s , rest' , <-trans bnd (s≤s ≤-refl))
... | nothing = nothing
parseOpCharsB (TMinus ∷ rest) cs with parseOpCharsB rest ('-' ∷ cs)
... | just (s , rest' , bnd) = just (s , rest' , <-trans bnd (s≤s ≤-refl))
... | nothing = nothing
parseOpCharsB (TStar ∷ rest) cs with parseOpCharsB rest ('*' ∷ cs)
... | just (s , rest' , bnd) = just (s , rest' , <-trans bnd (s≤s ≤-refl))
... | nothing = nothing
parseOpCharsB (TSlash ∷ rest) cs with parseOpCharsB rest ('/' ∷ cs)
... | just (s , rest' , bnd) = just (s , rest' , <-trans bnd (s≤s ≤-refl))
... | nothing = nothing
parseOpCharsB (TPercent ∷ rest) cs with parseOpCharsB rest ('%' ∷ cs)
... | just (s , rest' , bnd) = just (s , rest' , <-trans bnd (s≤s ≤-refl))
... | nothing = nothing
parseOpCharsB (TLt ∷ rest) cs with parseOpCharsB rest ('<' ∷ cs)
... | just (s , rest' , bnd) = just (s , rest' , <-trans bnd (s≤s ≤-refl))
... | nothing = nothing
parseOpCharsB (TGt ∷ rest) cs with parseOpCharsB rest ('>' ∷ cs)
... | just (s , rest' , bnd) = just (s , rest' , <-trans bnd (s≤s ≤-refl))
... | nothing = nothing
parseOpCharsB (TPipe ∷ rest) cs with parseOpCharsB rest ('|' ∷ cs)
... | just (s , rest' , bnd) = just (s , rest' , <-trans bnd (s≤s ≤-refl))
... | nothing = nothing
parseOpCharsB (TAmpersand ∷ rest) cs with parseOpCharsB rest ('&' ∷ cs)
... | just (s , rest' , bnd) = just (s , rest' , <-trans bnd (s≤s ≤-refl))
... | nothing = nothing
parseOpCharsB (TAt ∷ rest) cs with parseOpCharsB rest ('@' ∷ cs)
... | just (s , rest' , bnd) = just (s , rest' , <-trans bnd (s≤s ≤-refl))
... | nothing = nothing
parseOpCharsB _ _ = nothing

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
