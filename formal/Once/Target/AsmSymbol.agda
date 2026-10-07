-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Target.AsmSymbol — plan 0.107 §8 step 1 (D272): WHAT `as` ACCEPTS AS A
-- SYMBOL NAME.
--
-- The trust law `as-faithful` is stated over files whose symbols `as` reads as
-- symbols. Without this, a "symbol" may contain a newline and an instruction, so
-- `print` stops being injective and the law equates different files (D272).
--
-- The GNU `as` rule (all three targets): a symbol starts with a letter, `_`, `.`
-- or `$`, and continues with those or digits. Letters are `isAlpha` (multibyte
-- letters are accepted by `as`; the lexer's identifiers may contain them). No
-- whitespace, `:`, `,`, `#` or quote can occur, which is what keeps `print`
-- injective.
------------------------------------------------------------------------

module Once.Target.AsmSymbol where

open import Data.Bool using (Bool; _∨_; T)
open import Data.Char using (Char; isAlpha; isDigit; toℕ)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Nat using (_≡ᵇ_)
open import Data.String using (String; toList)
open import Data.Empty using (⊥)
open import Data.Product using (_×_)

-- `_`, `.` or `$`.
sym-punct : Char → Bool
sym-punct c = (toℕ c ≡ᵇ toℕ '_') ∨ (toℕ c ≡ᵇ toℕ '.') ∨ (toℕ c ≡ᵇ toℕ '$')

sym-start : Char → Bool
sym-start c = isAlpha c ∨ sym-punct c

sym-continue : Char → Bool
sym-continue c = sym-start c ∨ isDigit c

AsmSymChars : List Char → Set
AsmSymChars []       = ⊥
AsmSymChars (c ∷ cs) = T (sym-start c) × All (λ d → T (sym-continue d)) cs

-- | A string `as` reads as one symbol name.
AsmSym : String → Set
AsmSym s = AsmSymChars (toList s)
