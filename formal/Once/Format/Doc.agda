-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Format.Doc — documents and their layout (plan 0.124 step 2).
--
-- A document is text with places where a line may break (`line`), indented
-- blocks (`nest`) and groups that are laid out flat when they fit the width
-- (`group`). Two breaks are forced: `newline` ends the line unless it is
-- already ended (so breaks never pile up into blank lines), `blank` leaves one
-- empty line. A group that contains a forced break is never flat. `eol c`
-- puts `c` at the end of the current line, whenever that line ends (an
-- end-of-line comment: it takes no room and breaks nothing).
--
-- The layout writes indentation only before text, so no line ends in blanks
-- and an empty line is empty. One style: the width and the indent are
-- constants (`width`, `indent`), not options (D341).
------------------------------------------------------------------------

module Once.Format.Doc where

open import Data.Bool using (Bool; true; false; _∨_; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; replicate; reverse)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤ᵇ_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; fromList; toList; length)
open import Data.Char using (Char)
import Data.Char as Ch
open import Relation.Nullary using (does)

-- | The style (D341).
width indent : ℕ
width  = 100
indent = 2

infixr 6 _<>_

data Doc : Set where
  empty   : Doc
  text    : String → Doc       -- a piece of text with no line break in it
  line    : Doc                -- a space when flat, a line break when not
  newline : Doc                -- a line break unless the line is already ended
  blank   : Doc                -- an empty line
  eol     : String → Doc       -- text at the end of the current line
  _<>_    : Doc → Doc → Doc
  nest    : ℕ → Doc → Doc      -- the lines it breaks are indented by this much more
  group   : Doc → Doc          -- flat when it fits, else broken

-- Text, spaces between.
_<+>_ : Doc → Doc → Doc
a <+> b = a <> text " " <> b
infixr 6 _<+>_

-- Documents separated by soft breaks.
sep : List Doc → Doc
sep []       = empty
sep (d ∷ ds) = d <> sep-rest ds
  where
    sep-rest : List Doc → Doc
    sep-rest []       = empty
    sep-rest (e ∷ es) = line <> e <> sep-rest es

------------------------------------------------------------------------
-- Layout
------------------------------------------------------------------------

-- The width of a document laid out flat; `nothing` when it cannot be flat.
flatWidth : Doc → Maybe ℕ
flatWidth empty     = just 0
flatWidth (text s)  = just (length s)
flatWidth line      = just 1
flatWidth newline   = nothing
flatWidth blank     = nothing
flatWidth (eol _)   = just 0
flatWidth (a <> b)  = plus (flatWidth a) (flatWidth b)
  where
    plus : Maybe ℕ → Maybe ℕ → Maybe ℕ
    plus (just m) (just n) = just (m + n)
    plus (just _) nothing  = nothing
    plus nothing  _        = nothing
flatWidth (nest _ d) = flatWidth d
flatWidth (group d)  = flatWidth d

-- The layout state: the reversed output, the column, the indentation of the
-- current line while it is still empty (it is written before its first text,
-- so an empty line stays empty), and what goes at the end of the current line.
record St : Set where
  constructor st
  field
    out   : List Char
    col   : ℕ
    pend  : Maybe ℕ
    ends  : List String

private
  -- Text, after the pending indentation of a fresh line.
  emit : String → St → St
  emit s (st o c (just i) e) = st (reverse (toList s) ++ reverse (replicate i ' ') ++ o) (i + length s) nothing e
  emit s (st o c nothing e)  = st (reverse (toList s) ++ o) (c + length s) nothing e

  -- What goes at the end of a line, each after a space.
  flush : List String → List Char → List Char
  flush []       o = o
  flush (x ∷ xs) o = flush xs (reverse (toList x) ++ ' ' ∷ o)

  -- End the line (if it is not already ended); the next one is indented by
  -- `i`. A line holding only an end-of-line text is not empty: the text goes
  -- on it, alone.
  -- Blanks at the end of the (reversed) output: no line ends in them.
  trim : List Char → List Char
  trim []       = []
  trim (c ∷ cs) = if does (c Ch.≟ ' ') then trim cs else c ∷ cs

  brk : ℕ → St → St
  brk i (st o c (just _) [])       = st o 0 (just i) []
  brk i (st o c (just j) (x ∷ xs)) = st ('\n' ∷ flush xs (reverse (toList x) ++ reverse (replicate j ' ') ++ o)) 0 (just i) []
  brk i (st o c nothing e)         = st ('\n' ∷ flush e (trim o)) 0 (just i) []

  -- An empty line (never at the start of the text).
  blankLine : ℕ → St → St
  blankLine i σ with brk i σ
  ... | st [] c p e = st [] 0 (just i) e
  ... | st (x ∷ o) c p e = st ('\n' ∷ x ∷ o) 0 (just i) e

  fits : ℕ → Maybe ℕ → Bool
  fits c (just n) = (c + n) ≤ᵇ width
  fits c nothing  = false

-- | Lay out a document at an indentation, flat or not.
layout : ℕ → Bool → Doc → St → St
layout i f empty      σ = σ
layout i f (text s)   σ = emit s σ
layout i true  line   σ = emit " " σ
layout i false line   σ = brk i σ
layout i f newline    σ = brk i σ
layout i f blank      σ = blankLine i σ
layout i f (eol s)    (st o c p e) = st o c p (e ++ (s ∷ []))
layout i f (a <> b)   σ = layout i f b (layout i f a σ)
layout i f (nest n d) σ = layout (i + n) f d σ
layout i true  (group d) σ = layout i true d σ
layout i false (group d) σ = layout i (fits (column σ) (flatWidth d)) d σ
  where
    column : St → ℕ
    column (st _ c nothing _)  = c
    column (st _ _ (just j) _) = j

-- | A document as text, ending in exactly one newline.
render : Doc → String
render d with brk 0 (layout 0 false d (st [] 0 (just 0) []))
... | st o _ _ _ = fromList (reverse o)
