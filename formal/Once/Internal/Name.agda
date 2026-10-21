{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Internal.Name — the dotted form of a canonical name (`Once.Spec.Name`),
-- used as an external operation's key, and the names it renders apart.
------------------------------------------------------------------------

module Once.Internal.Name where

open import Data.Bool using (Bool; true; false; not; _∧_; T)
open import Data.Char using (Char; _≈ᵇ_)
open import Data.List using (List; []; _∷_)
open import Data.String using (String; toList)
import Data.String as String
open import Once.Spec.Name using (CanonicalName; canonical)

showCanonical : CanonicalName → String
showCanonical (canonical [])        = ""
showCanonical (canonical (x ∷ []))  = x
{-# CATCHALL #-}
showCanonical (canonical (x ∷ xs))  = x String.++ "." String.++ showCanonical (canonical xs)

-- A word: nonempty, without `.` — what the lexer makes of a name, and what
-- `showCanonical` renders apart (plan 0.121 R13, D329).
noDotB : List Char → Bool
noDotB []       = true
noDotB (c ∷ cs) = not (c ≈ᵇ '.') ∧ noDotB cs

wordCharsB : List Char → Bool
wordCharsB []       = false
wordCharsB (c ∷ cs) = noDotB (c ∷ cs)

wordB : String → Bool
wordB s = wordCharsB (toList s)

wordsB : List String → Bool
wordsB []       = true
wordsB (x ∷ xs) = wordB x ∧ wordsB xs

-- Every part of the name is a word.
wordNameB : CanonicalName → Bool
wordNameB (canonical xs) = wordsB xs

WordName : CanonicalName → Set
WordName c = T (wordNameB c)
