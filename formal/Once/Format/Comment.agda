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
-- comment line. A block comment `{- … -}` becomes line comments, one per line
-- of it (at the end of a line of code, one).
------------------------------------------------------------------------

module Once.Format.Comment where

open import Data.Bool using (Bool; true; false; _∨_; _∧_; if_then_else_)
open import Data.Char using (Char; isDigit)
import Data.Char as Ch
open import Data.List using (List; []; _∷_; _++_; reverse; concatMap; map)
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

  -- Blanks at both ends dropped.
  blankish : Char → Bool
  blankish c = is c ' ' ∨ is c '\t' ∨ is c '\r'

  dropBlanks : List Char → List Char
  dropBlanks []       = []
  dropBlanks (c ∷ cs) = if blankish c then dropBlanks cs else c ∷ cs

  strip : List Char → List Char
  strip cs = reverse (dropBlanks (reverse (dropBlanks cs)))

  -- The lines of a text.
  linesOf : List Char → List (List Char)
  linesOf cs = go cs []
    where
      go : List Char → List Char → List (List Char)
      go []       l = reverse l ∷ []
      go (c ∷ cs) l = if is c '\n' then reverse l ∷ go cs [] else go cs (c ∷ l)

  -- A block comment's text, without `{-` and `-}`.
  inside : List Char → List Char
  inside ('{' ∷ '-' ∷ cs) = unclose (reverse cs)
    where
      unclose : List Char → List Char
      unclose ('}' ∷ '-' ∷ rs) = reverse rs
      {-# CATCHALL #-}
      unclose rs              = reverse rs
  {-# CATCHALL #-}
  inside cs = cs

  isBlock : List Char → Bool
  isBlock ('{' ∷ '-' ∷ _) = true
  {-# CATCHALL #-}
  isBlock _               = false

  asLine : List Char → String
  asLine []        = "--"
  asLine l@(_ ∷ _) = fromList ('-' ∷ '-' ∷ ' ' ∷ l)

  -- Empty lines at both ends dropped.
  trimLines : List (List Char) → List (List Char)
  trimLines ls = reverse (dropEmpty (reverse (dropEmpty ls)))
    where
      dropEmpty : List (List Char) → List (List Char)
      dropEmpty ([] ∷ ls) = dropEmpty ls
      {-# CATCHALL #-}
      dropEmpty ls        = ls

-- | A comment as line comments: a block comment, one per line of it.
commentLines : String → List String
commentLines s =
  if isBlock (toList s) then map (λ l → asLine (strip l)) (trimLines (linesOf (inside (toList s))))
  else s ∷ []

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
commentRun cs = go (concatMap commentLines cs)
  where
    go : List String → Doc
    go []       = empty
    go (c ∷ cs) with classify c
    ... | prose ws   = para ws <> newline <> go cs
    ... | verbatim v = cmt v <> newline <> go cs

-- | An end-of-line comment, `-- text` (not re-wrapped); a block comment's
-- lines joined.
eolText : String → String
eolText s =
  if isBlock (toList s) then asLine (strip (concatMap (λ c → if is c '\n' then ' ' ∷ [] else c ∷ []) (inside (toList s))))
  else go (toList s)
  where
    go : List Char → String
    go ('-' ∷ '-' ∷ body@(' ' ∷ _)) = s
    go ('-' ∷ '-' ∷ []) = s
    {-# CATCHALL #-}
    go ('-' ∷ '-' ∷ body) = if allDash body then s else "-- " ++ˢ fromList body
    {-# CATCHALL #-}
    go _ = s
