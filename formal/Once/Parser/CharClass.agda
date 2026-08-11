-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Parser.CharClass — small character-class helpers shared by the lexer,
-- the PolyType parser, and the generic type-grammar parser's TVar hook. Split
-- out of Once.Parser.PolyType so the generic instantiation can depend on it
-- without an import cycle. Plan 0.7-2.
------------------------------------------------------------------------

module Once.Parser.CharClass where

open import Data.Bool using (Bool; false)
open import Data.List using ([]; _∷_)
open import Data.String using (String)
open import Data.Char using (isLower)
import Data.String as StrLib

-- | Is the word a lowercase identifier (its first character is lowercase)?
-- Matches Haskell/ML/Idris convention: type variables are lowercase,
-- ground type names and user-declared type aliases are uppercase.
isLowerWord : String → Bool
isLowerWord s with StrLib.toList s
... | []      = false
... | (c ∷ _) = isLower c
