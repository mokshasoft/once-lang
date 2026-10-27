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

-- (public: `Format.Proof.Rerender` reasons about them)
module _ where
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

  -- A blank: words end at one, and no line ends in one.
  blankish : Char → Bool
  blankish c = is c ' ' ∨ is c '\t' ∨ is c '\r'

  -- A word read (last character first), before the words after it.
  emitW : List Char → List String → List String
  emitW []        acc = acc
  emitW w@(_ ∷ _) acc = fromList (reverse w) ∷ acc

  wordsGo : List Char → List Char → List String
  wordsGo []       w = emitW w []
  wordsGo (c ∷ cs) w = if blankish c then emitW w (wordsGo cs []) else wordsGo cs (c ∷ w)

  -- The words of a text.
  words : List Char → List String
  words cs = wordsGo cs []

  -- Blanks at both ends dropped.
  dropBlanks : List Char → List Char
  dropBlanks []       = []
  dropBlanks (c ∷ cs) = if blankish c then dropBlanks cs else c ∷ cs

  strip : List Char → List Char
  strip cs = reverse (dropBlanks (reverse (dropBlanks cs)))

  -- The lines of a text.
  linesGo : List Char → List Char → List (List Char)
  linesGo []       l = reverse l ∷ []
  linesGo (c ∷ cs) l = if is c '\n' then reverse l ∷ linesGo cs [] else linesGo cs (c ∷ l)

  linesOf : List Char → List (List Char)
  linesOf cs = linesGo cs []

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

  dropEmpty : List (List Char) → List (List Char)
  dropEmpty ([] ∷ ls) = dropEmpty ls
  {-# CATCHALL #-}
  dropEmpty ls        = ls

  -- Empty lines at both ends dropped.
  trimLines : List (List Char) → List (List Char)
  trimLines ls = reverse (dropEmpty (reverse (dropEmpty ls)))

-- At least one line: an empty block comment is an empty line comment (so a
-- comment always prints as something).
atLeastOne : List String → List String
atLeastOne []         = "--" ∷ []
atLeastOne ls@(_ ∷ _) = ls

-- | A comment as line comments: a block comment, one per line of it.
commentLines : String → List String
commentLines s =
  if isBlock (toList s) then atLeastOne (map (λ l → asLine (strip l)) (trimLines (linesOf (inside (toList s)))))
  else s ∷ []

data CLine : Set where
  prose    : List String → CLine
  verbatim : String → CLine

-- What follows a comment line's `--`: `s` the line.
afterBlank : String → List Char → CLine
afterBlank s []       = verbatim "--"
afterBlank s (d ∷ ds) =
  if is d ' ' then verbatim s else if listItem (d ∷ ds) then verbatim s else prose (words (d ∷ ds))

afterDashes : String → List Char → CLine
afterDashes s []       = prose []
afterDashes s (c ∷ cs) = if is c ' ' then afterBlank s cs else prose (words (c ∷ cs))

classifyChars : String → List Char → CLine
classifyChars s ('-' ∷ '-' ∷ body) = if allDash body then verbatim s else afterDashes s body
{-# CATCHALL #-}
classifyChars s _                  = verbatim s

-- | What a comment line is.
classify : String → CLine
classify s = classifyChars s (toList s)

-- | A run of comment lines on lines of their own, each line ended.
commentLinesDoc : List String → Doc

commentRun : List String → Doc
commentRun cs = commentLinesDoc (concatMap commentLines cs)

-- | A comment line: prose filled to the width, the rest as written.
lineDoc : CLine → Doc
lineDoc (prose ws)   = para ws
lineDoc (verbatim v) = cmt v

-- | Line comments, each on a line of its own.
commentLinesDoc []       = empty
commentLinesDoc (c ∷ cs) = lineDoc (classify c) <> newline <> commentLinesDoc cs

-- | An end-of-line comment, `-- text` (not re-wrapped); a block comment's
-- lines joined. One whose `--` a blank or a dash follows is kept as written,
-- so the comments that end one line, joined, read back as themselves.
-- (after `--`: a blank or a dash, kept; else a blank is put after it)
eolChars : String → List Char → String
eolChars s ('-' ∷ '-' ∷ [])     = s
eolChars s ('-' ∷ '-' ∷ c ∷ cs) = if is c ' ' ∨ is c '-' then s else fromList ('-' ∷ '-' ∷ ' ' ∷ c ∷ cs)
{-# CATCHALL #-}
eolChars s _                    = s

eolText : String → String
eolText s =
  if isBlock (toList s) then asLine (strip (concatMap (λ c → if is c '\n' then ' ' ∷ [] else c ∷ []) (inside (toList s))))
  else eolChars s (toList s)
