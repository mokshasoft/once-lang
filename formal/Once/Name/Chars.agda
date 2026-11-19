{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Name.Chars — the characters a name is made of.
--
-- An identifier starts with a letter or `_` and continues with letters,
-- digits and `_ ' + * ! ?`; an operator's name (`(<+>)`) is made of
-- `. + - * / % < > | & @`. The lexer reads names by these classes, and the
-- target's symbol encoding relies on the same classes to keep symbols apart.
------------------------------------------------------------------------

module Once.Name.Chars where

open import Agda.Builtin.Char using (primCharToNat)
import Data.Bool.ListAction
open import Data.Bool using (Bool; _∨_)
open import Data.Char using (Char; isAlpha; isDigit)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; _≡ᵇ_)

-- | A character's code.
toNat : Char → ℕ
toNat = primCharToNat

-- | Is this character an identifier start? [a-zA-Z_]
isIdentStart : Char → Bool
isIdentStart c = isAlpha c ∨ (toNat c ≡ᵇ toNat '_')

-- | Is this character an identifier continuation? [a-zA-Z0-9_'+*!?]
isIdentContinue : Char → Bool
isIdentContinue c =
  isAlpha c ∨ isDigit c ∨
  (toNat c ≡ᵇ toNat '_') ∨
  (toNat c ≡ᵇ toNat '\'') ∨
  (toNat c ≡ᵇ toNat '+') ∨
  (toNat c ≡ᵇ toNat '*') ∨
  (toNat c ≡ᵇ toNat '!') ∨
  (toNat c ≡ᵇ toNat '?')

-- | The characters an operator's name is made of (`(<+>)`; the grammar's
-- `OpChar`): `. + - * / % < > | & @`.
opNameChars : List Char
opNameChars = '.' ∷ '+' ∷ '-' ∷ '*' ∷ '/' ∷ '%' ∷ '<' ∷ '>' ∷ '|' ∷ '&' ∷ '@' ∷ []

isOpNameChar : Char → Bool
isOpNameChar c = Data.Bool.ListAction.any (λ k → toNat c ≡ᵇ toNat k) opNameChars
