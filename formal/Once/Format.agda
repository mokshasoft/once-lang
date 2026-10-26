-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Format — `once fmt`: a module in the one canonical layout (plan 0.124).
--
-- The text is parsed as the compiler parses it (`parseStrict`); the module is
-- printed (`Format.Print`) with the comments the lexer kept (`Format.Lex`).
-- What does not parse is not formatted: the error is the parser's.
------------------------------------------------------------------------

module Once.Format where

open import Data.String using (String; toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Once.Spec.Surface.Syntax using (Module)
open import Once.Parser using (parseStrict)
open import Once.Format.Lex using (lexItems)
open import Once.Format.Print using (format)

private
  formatParsed : String → String ⊎ Module → String ⊎ String
  formatParsed text (inj₁ err) = inj₁ err
  formatParsed text (inj₂ m)   = inj₂ (format m (lexItems (toList text)))

-- | A source text in the canonical layout, or the parser's error.
formatSource : String → String ⊎ String
formatSource text = formatParsed text (parseStrict text)
