-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Format.Comment — comments, formatted (plan 0.124 §8).
--
-- A line comment is written `-- text`, and a prose line longer than the width
-- is wrapped at its words, at its indentation (`Doc.para`). Lines are never
-- joined: whether a short line ends a thought (a header, `Expected: …`) is
-- not something the formatter can read. Kept as written: a banner (only
-- dashes), a line indented past `-- ` (code, a table), a list item, an empty
-- comment line, and a block comment `{- … -}`.
------------------------------------------------------------------------

module Once.Format.Comment where

open import Data.Bool using (Bool; true; false; _∨_; _∧_; if_then_else_)
open import Data.Char using (Char; isDigit)
import Data.Char as Ch
open import Data.List using (List; []; _∷_; _++_; reverse)
open import Data.String using (String; fromList; toList) renaming (_++_ to _++ˢ_)
open import Relation.Nullary using (does)

open import Once.Format.Doc using (Doc; empty; cmt; para; newline; _<>_)

private
  is : Char → Char → Bool
  is c d = does (c Ch.≟ d)

  allDash : List Char → Bool
  allDash []       = true
  allDash (c ∷ cs) = is c '-' ∧ allDash cs

  -- `* `, `- `, `+ `, `• `, `1. `, `1) `
  listItem : List Char → Bool
  listItem (c ∷ ' ' ∷ _) = is c '*' ∨ is c '-' ∨ is c '+' ∨ is c '•'
  {-# CATCHALL #-}
  listItem (c ∷ cs)      = isDigit c ∧ digitsThen cs
    where
      digitsThen : List Char → Bool
      digitsThen (d ∷ ' ' ∷ _) = is d '.' ∨ is d ')'
      {-# CATCHALL #-}
      digitsThen (d ∷ ds)      = isDigit d ∧ digitsThen ds
      digitsThen []            = false
  listItem []            = false

  -- The words of a text.
  words : List Char → List String
  words cs = go cs []
    where
      emitW : List Char → List String → List String
      emitW []        acc = acc
      emitW w@(_ ∷ _) acc = fromList (reverse w) ∷ acc
      go : List Char → List Char → List String
      go []       w = emitW w []
      go (c ∷ cs) w = if is c ' ' ∨ is c '\t' then emitW w (go cs []) else go cs (c ∷ w)

data CLine : Set where
  prose    : List String → CLine
  verbatim : String → CLine

-- | What a comment line is.
classify : String → CLine
classify s = go (toList s)
  where
    go : List Char → CLine
    go ('-' ∷ '-' ∷ body) =
      if allDash body then verbatim s
      else after body
      where
        after : List Char → CLine
        after (' ' ∷ []) = verbatim "--"
        after (' ' ∷ ' ' ∷ rest) = verbatim s
        {-# CATCHALL #-}
        after (' ' ∷ rest) = if listItem rest then verbatim s else prose (words rest)
        {-# CATCHALL #-}
        after rest = prose (words rest)
    {-# CATCHALL #-}
    go _ = verbatim s

-- | A run of comment lines on lines of their own, each line ended.
commentRun : List String → Doc
commentRun []       = empty
commentRun (c ∷ cs) with classify c
... | prose ws   = para ws <> newline <> commentRun cs
... | verbatim v = cmt v <> newline <> commentRun cs

-- | An end-of-line comment, `-- text` (not re-wrapped).
eolText : String → String
eolText s = go (toList s)
  where
    go : List Char → String
    go ('-' ∷ '-' ∷ body@(' ' ∷ _)) = s
    go ('-' ∷ '-' ∷ []) = s
    {-# CATCHALL #-}
    go ('-' ∷ '-' ∷ body) = if allDash body then s else "-- " ++ˢ fromList body
    {-# CATCHALL #-}
    go _ = s
