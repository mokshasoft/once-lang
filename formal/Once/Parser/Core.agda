-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Parser.Core
--
-- The parser type, and skipping newlines. The parsers themselves are
-- written by structural or well-founded recursion on the token list
-- (`Parser.Module`, `Parser.Expr`, `Parser.Type`), not with monadic
-- combinators.
------------------------------------------------------------------------

module Once.Parser.Core where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)

open import Once.Parser.Token

------------------------------------------------------------------------
-- Parser Type
------------------------------------------------------------------------

-- | A parser consumes tokens and produces a value with remaining tokens.
-- Nothing = parse failure, Just (a, rest) = success.
Parser : Set → Set
Parser A = List Token → Maybe (A × List Token)

-- | Skip newlines (zero or more).
-- Specialised to `TNewline` so termination is structurally visible:
-- each successful consumption removes exactly one token from the list.
-- The prior generic `many : Parser A → Parser (List A)` combinator
-- was removed (used only by `skipNewlines`; retaining it required a
-- `TERMINATING` pragma since generic `many p` has no
-- length-bound witness on `p`).
skipNewlines : Parser (List Token)
skipNewlines [] = just ([] , [])
skipNewlines (TNewline ∷ rest) with skipNewlines rest
... | just (ns , rest') = just (TNewline ∷ ns , rest')
... | nothing = just (TNewline ∷ [] , rest)
{-# CATCHALL #-}
skipNewlines (t ∷ rest) = just ([] , t ∷ rest)