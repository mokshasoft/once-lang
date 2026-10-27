-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Format.Doc — documents and their layout (plan 0.124 step 2).
--
-- A document is tokens (`tk`, written by `spell`), blanks (`sp`) and comments
-- (`cmt`, `para`), with places where a line may break (`line`), indented
-- blocks (`nest`) and groups that are laid out flat when they fit the width
-- (`group`). Two breaks are forced: `newline` ends the line unless it is
-- already ended (so breaks never pile up into blank lines), `blank` leaves one
-- empty line; they break a flat group too. Comments take no room in deciding
-- whether a group is flat, so the code's layout is its own. `eol c`
-- puts `c` at the end of the current line, whenever that line ends (an
-- end-of-line comment: it takes no room and breaks nothing).
--
-- The layout writes lexemes (`Lexeme`), and what it writes lexes as the
-- document's tokens whatever the document (`Format.Proof`): a blank goes
-- between two tokens that would otherwise run together (`apart`), a comment
-- is a line comment and ends its line, indentation is written only before
-- text (so no line ends in blanks and an empty line is empty), and an
-- indented line is never empty (an empty line ends what the indentation
-- continues). One style: the width and the indent are constants (`width`,
-- `indent`), not options (D341).
------------------------------------------------------------------------

module Once.Format.Doc where

open import Data.Bool using (Bool; true; false; _∨_; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; replicate; reverse; concatMap; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤ᵇ_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; fromList; toList)
import Data.String as Str
open import Data.Char using (Char)
import Data.Char as Ch
open import Relation.Nullary using (does)
open import Once.Spec.Surface.Lexing using (Token; TWord; TInt; TFloat; TMinus; TArrow; TGt; TGe; TLt;
  TEquals; TEqEq; TBang; TNeq; TLBrace; TPlus; TStar; TDot)
open import Once.Format.Spell using (spell)

-- | The style (D341).
width indent : ℕ
width  = 100
indent = 2

infixr 6 _<>_

data Doc : Set where
  empty   : Doc
  tk      : Token → Doc        -- a token, as `spell` writes it
  sp      : Doc                -- a blank
  cmt     : String → Doc       -- a comment, which ends its line
  para    : List String → Doc  -- a comment paragraph: its words filled to the width, each line `-- …`
  line    : Doc                -- a space when flat, a line break when not
  newline : Doc                -- a line break unless the line is already ended
  blank   : Doc                -- an empty line (between declarations: an indented one is a line break)
  eol     : String → Doc       -- a comment at the end of the current line
  _<>_    : Doc → Doc → Doc
  nest    : ℕ → Doc → Doc      -- the lines it breaks are indented by this much more
  group   : Doc → Doc          -- flat when it fits, else broken

------------------------------------------------------------------------
-- What the layout writes
------------------------------------------------------------------------

-- The classes `apart` reads.
continues dashes greater equals number : Token → Bool
continues (TWord _)      = true
continues (TInt _)       = true
continues (TFloat _ _ _) = true
continues TPlus          = true
continues TStar          = true
continues TBang          = true
continues TNeq           = true
{-# CATCHALL #-}
continues _              = false
number TDot = true
{-# CATCHALL #-}
number t    = continues t
dashes TMinus = true
dashes TArrow = true
{-# CATCHALL #-}
dashes _      = false
greater TGt = true
greater TGe = true
{-# CATCHALL #-}
greater _   = false
equals TEquals = true
equals TEqEq   = true
{-# CATCHALL #-}
equals _       = false

-- After a comment's `--` (one is added when it has none).
body : List Char → List Char
body ('-' ∷ '-' ∷ cs) = cs
{-# CATCHALL #-}
body cs               = ' ' ∷ cs

-- The text is written as lexemes: a token, a blank, a line end, the
-- indentation of a line, a comment.
data Lexeme : Set where
  lt   : Token → Lexeme
  lsp  : Lexeme
  lnl  : Lexeme
  lind : ℕ → Lexeme
  lcm  : List Char → Lexeme

chars : Lexeme → List Char
chars (lt t)   = toList (spell t)
chars lsp      = ' ' ∷ []
chars lnl      = '\n' ∷ []
chars (lind i) = replicate i ' '
chars (lcm c)  = c

-- | Two tokens that would lex as one, or as something else, written together:
-- a word or a number before a word, a number, `+`, `*`, `!`, `!=` (they
-- continue a word) or, after a number, `.`; `-` before `-`, `->`, `>`, `>=`; `<`, `>`,
-- `=`, `!` before `=`, `==`; `{` before `-`, `->`.
apart : Token → Token → Bool
apart (TWord _)      t    = continues t
apart (TInt _)       t    = number t
apart (TFloat _ _ _) t    = number t
apart TMinus         t    = dashes t ∨ greater t
apart TLt            t    = equals t
apart TGt            t    = equals t
apart TEquals        t    = equals t
apart TBang          t    = equals t
apart TLBrace        t    = dashes t
{-# CATCHALL #-}
apart _              _    = false

-- Line breaks as blanks.
oneLine : List Char → List Char
oneLine []       = []
oneLine (c ∷ cs) = (if does (c Ch.≟ '\n') then ' ' else c) ∷ oneLine cs

-- | A comment's text, as a line comment: `--` first, on one line.
lineComment : List Char → List Char
lineComment cs = '-' ∷ '-' ∷ oneLine (body cs)

------------------------------------------------------------------------
-- Layout
------------------------------------------------------------------------
-- The width of a document's code laid out flat. Comments take no room: a
-- comment ends its line wherever it stands (an end-of-line comment at the end,
-- one on lines of its own with a forced break), so whether a group is flat is
-- the code's alone.
flatWidth : Doc → ℕ
flatWidth empty      = 0
flatWidth (tk t)     = Str.length (spell t)
flatWidth sp         = 1
flatWidth (cmt _)    = 0
flatWidth (para _)   = 0
flatWidth line       = 1
flatWidth newline    = 0
flatWidth blank      = 0
flatWidth (eol _)    = 0
flatWidth (a <> b)   = flatWidth a + flatWidth b
flatWidth (nest _ d) = flatWidth d
flatWidth (group d)  = flatWidth d

-- The layout state: the lexemes written (last first), the column, the
-- indentation of the current line while it is still empty (it is written
-- before its first text, so an empty line stays empty), and the comments that
-- go at the end of the current line.
record St : Set where
  constructor st
  field
    out   : List Lexeme
    col   : ℕ
    pend  : Maybe ℕ
    ends  : List String

-- The column text would start at.
column : St → ℕ
column (st _ c nothing _)  = c
column (st _ _ (just j) _) = j

-- The steps of the layout (public: `Format.Proof.Layout` reasons about them).

-- A lexeme of width `n`, after the pending indentation of a fresh line.
put : Lexeme → ℕ → St → St
put x n (st o c (just i) e) = st (x ∷ lind i ∷ o) (i + n) nothing e
put x n (st o c nothing e)  = st (x ∷ o) (c + n) nothing e

-- A blank; none at the start of a line.
space : St → St
space (st o c (just i) e) = st o c (just i) e
space (st o c nothing e)  = put lsp 1 (st o c nothing e)

-- A token, after a blank when the one before it would run into it.
token : Token → St → St
token t (st (lt u ∷ o) c nothing e) =
  if apart u t then put (lt t) (Str.length (spell t)) (space (st (lt u ∷ o) c nothing e))
  else put (lt t) (Str.length (spell t)) (st (lt u ∷ o) c nothing e)
{-# CATCHALL #-}
token t σ = put (lt t) (Str.length (spell t)) σ

-- The end-of-line comments, after the line's text.
joined : List String → List Char
joined []       = []
joined (x ∷ []) = lineComment (toList x)
joined (x ∷ xs@(_ ∷ _)) = lineComment (toList x) ++ ' ' ∷ joined xs

-- Blanks at the end of the line: no line ends in them.
trim : List Lexeme → List Lexeme
trim (lsp ∷ o) = trim o
{-# CATCHALL #-}
trim o         = o

-- End the line (if it is not already ended); the next one is indented by
-- `i`. A line holding only end-of-line comments is not empty: they go on
-- it, alone.
brk : ℕ → St → St
brk i (st o c (just _) [])         = st o 0 (just i) []
brk i (st o c (just j) e@(_ ∷ _))  = st (lnl ∷ lcm (joined e) ∷ lind j ∷ o) 0 (just i) []
brk i (st o c nothing [])          = st (lnl ∷ trim o) 0 (just i) []
brk i (st o c nothing e@(_ ∷ _))   = st (lnl ∷ lcm (joined e) ∷ lsp ∷ trim o) 0 (just i) []

-- A comment: it ends its line (after the line's end-of-line comments).
comment : ℕ → String → St → St
comment i c (st o col p e) = brk i (st o col p (e ++ (c ∷ [])))

-- An empty line (never at the start of the text), between declarations.
blankLine : ℕ → St → St
blankLine i σ = after (brk i σ)
  where
    after : St → St
    after (st [] c p e)      = st [] 0 (just i) e
    after (st (x ∷ o) c p e) = st (lnl ∷ x ∷ o) 0 (just i) e

-- A paragraph's lines, from column `c`: a line takes the next word while it
-- fits (and always one word, however long). `cur`: the line's words, last
-- first.
fill : ℕ → ℕ → List String → List String → List (List String)
fill i c []          []       = [] ∷ []
fill i c cur@(_ ∷ _) []       = reverse cur ∷ []
fill i c []          (w ∷ ws) = fill i (c + 1 + Str.length w) (w ∷ []) ws
fill i c cur@(_ ∷ _) (w ∷ ws) =
  if (c + 1 + Str.length w) ≤ᵇ width then fill i (c + 1 + Str.length w) (w ∷ cur) ws
  else reverse cur ∷ fill i (i + 3 + Str.length w) (w ∷ []) ws

-- A line of a paragraph: `--`, then its words.
dashed : List String → List Char
dashed ws = '-' ∷ '-' ∷ concatMap (λ w → ' ' ∷ toList w) ws

paragraph : ℕ → List (List String) → St → St
paragraph i []         σ = σ
paragraph i (l ∷ ls)   σ = paragraph i ls (comment i (fromList (dashed l)) σ)

fits : ℕ → ℕ → Bool
fits c n = (c + n) ≤ᵇ width

-- | Lay out a document at an indentation, flat or not.
layout : ℕ → Bool → Doc → St → St
layout i f empty      σ = σ
layout i f (tk t)     σ = token t σ
layout i f sp         σ = space σ
layout i f (cmt c)    σ = comment i c σ
layout i f (para ws)  σ = paragraph i (fill i (column σ + 2) [] ws) σ
layout i true  line   σ = space σ
layout i false line   σ = brk i σ
layout i f newline    σ = brk i σ
layout zero    f blank σ = blankLine zero σ
layout (suc i) f blank σ = brk (suc i) σ
layout i f (eol s)    (st o c p e) = st o c p (e ++ (s ∷ []))
layout i f (a <> b)   σ = layout i f b (layout i f a σ)
layout i f (nest n d) σ = layout (i + n) f d σ
layout i true  (group d) σ = layout i true d σ
layout i false (group d) σ = layout i (fits (column σ) (flatWidth d)) d σ

-- | A document as lexemes, in order, ending with a line end.
lexemes : Doc → List Lexeme
lexemes d = reverse (St.out (brk 0 (layout 0 false d (st [] 0 (just 0) []))))

-- | A document as text, ending in exactly one newline.
render : Doc → String
render d = fromList (concatMap chars (lexemes d))

------------------------------------------------------------------------
-- The tokens of a document
------------------------------------------------------------------------

-- | A document's tokens, in order, before `r`: its layout and comments are
-- not tokens.
toks : Doc → List Token → List Token
toks empty      r = r
toks (tk t)     r = t ∷ r
toks sp         r = r
toks (cmt _)    r = r
toks (para _)   r = r
toks line       r = r
toks newline    r = r
toks blank      r = r
toks (eol _)    r = r
toks (a <> b)   r = toks a (toks b r)
toks (nest _ d) r = toks d r
toks (group d)  r = toks d r
