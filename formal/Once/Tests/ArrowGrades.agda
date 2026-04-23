-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Tests.ArrowGrades
--
-- Smoke tests for the `A^q -> B` surface syntax introduced in the
-- Phase-next linearity extension. The parser desugars these to the
-- graded arrow `A ⇒[ q ] B` internally; this test file exercises the
-- round-trip at the Agda level.
--
-- Positive cases are definitions that type-check (demonstrating the
-- parser emits the expected `Type`). Negative cases are commented out
-- with explanation of the expected parse error.
--
-- Reference: plan 0.2.6 (linearity), docs/design/memory.md (surface syntax)
------------------------------------------------------------------------

module Once.Tests.ArrowGrades where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (Type; Unit; Int; Str; _*_; _+_;
                             _⇒[_]_; _⇒_; _⊸_; _⇒₀_;
                             Quantity; Zero; One; Many)
open import Once.Parser.Token
open import Once.Parser.Type using (parseType)

------------------------------------------------------------------------
-- Test 1: default `->` parses as Many
------------------------------------------------------------------------

-- `Int -> Int` → Int ⇒[ Many ] Int
test-default-arrow : parseType (TWord "Int" ∷ TArrow ∷ TWord "Int" ∷ [])
                  ≡ just (Int ⇒[ Many ] Int , [])
test-default-arrow = refl

------------------------------------------------------------------------
-- Test 2: `A^1 -> B` parses as a linear arrow
------------------------------------------------------------------------

-- `Int^1 -> Int` → Int ⇒[ One ] Int  (i.e., Int ⊸ Int)
test-linear-arrow : parseType (TWord "Int" ∷ TCaret1 ∷ TArrow ∷ TWord "Int" ∷ [])
                 ≡ just (Int ⇒[ One ] Int , [])
test-linear-arrow = refl

-- Alias check: the parsed type IS the `⊸` alias from Once.Type.
test-linear-alias : Int ⇒[ One ] Int ≡ Int ⊸ Int
test-linear-alias = refl

------------------------------------------------------------------------
-- Test 3: `A^0 -> B` parses as an erased arrow
------------------------------------------------------------------------

test-erased-arrow : parseType (TWord "Int" ∷ TCaret0 ∷ TArrow ∷ TWord "Unit" ∷ [])
                 ≡ just (Int ⇒[ Zero ] Unit , [])
test-erased-arrow = refl

test-erased-alias : Int ⇒[ Zero ] Unit ≡ Int ⇒₀ Unit
test-erased-alias = refl

------------------------------------------------------------------------
-- Test 4: `A^w -> B` parses as explicit unrestricted (same as ->)
------------------------------------------------------------------------

test-explicit-unrestricted : parseType (TWord "Int" ∷ TCaretW ∷ TArrow ∷ TWord "Int" ∷ [])
                          ≡ just (Int ⇒[ Many ] Int , [])
test-explicit-unrestricted = refl

-- Alias check
test-unrestricted-alias : Int ⇒[ Many ] Int ≡ Int ⇒ Int
test-unrestricted-alias = refl

------------------------------------------------------------------------
-- Test 5a: `(Int) -> Int` — parens around a single atom, default arrow
------------------------------------------------------------------------
-- Does the paren case work at all?
test-paren-default :
    parseType (TLParen ∷ TWord "Int" ∷ TRParen ∷ TArrow ∷ TWord "Int" ∷ [])
  ≡ just (Int ⇒[ Many ] Int , [])
test-paren-default = refl

------------------------------------------------------------------------
-- Test 5b: `(Int)^1 -> Int` — parens + grade on atom
------------------------------------------------------------------------
-- Isolates whether the grade-after-paren works at all.
test-paren-linear :
    parseType (TLParen ∷ TWord "Int" ∷ TRParen ∷ TCaret1 ∷ TArrow ∷ TWord "Int" ∷ [])
  ≡ just (Int ⇒[ One ] Int , [])
test-paren-linear = refl

------------------------------------------------------------------------
-- Test 5c: `(Int * String) -> Int` — compound in parens, default arrow
------------------------------------------------------------------------
-- NOTE: the token must be `TWord "String"` not `TWord "Str"` — the lexer
-- produces the source-level keyword, which the parser then maps to the
-- internal `Str` type. (Str is the internal name; String is surface.)
test-compound-paren-default :
    parseType (TLParen ∷ TWord "Int" ∷ TStar ∷ TWord "String" ∷ TRParen
               ∷ TArrow ∷ TWord "Int" ∷ [])
  ≡ just ((Int * Str) ⇒[ Many ] Int , [])
test-compound-paren-default = refl

------------------------------------------------------------------------
-- Test 5d: `(Int * String)^1 -> Int` — compound + grade
------------------------------------------------------------------------
test-compound-paren-linear :
    parseType (TLParen ∷ TWord "Int" ∷ TStar ∷ TWord "String" ∷ TRParen
               ∷ TCaret1 ∷ TArrow ∷ TWord "Int" ∷ [])
  ≡ just ((Int * Str) ⇒[ One ] Int , [])
test-compound-paren-linear = refl

------------------------------------------------------------------------
-- Test 5c: `A -> B -> C` with default arrow grades (Many on both)
------------------------------------------------------------------------

test-curried-default :
    parseType (TWord "Int" ∷ TArrow ∷ TWord "Int" ∷ TArrow ∷ TWord "Int" ∷ [])
  ≡ just (Int ⇒[ Many ] (Int ⇒[ Many ] Int) , [])
test-curried-default = refl

------------------------------------------------------------------------
-- Test 6: higher-arity — `A^1 -> B^0 -> C` (curried, each arrow graded)
------------------------------------------------------------------------

-- `Int^1 -> Int^0 -> Int` (right-associative)
test-curried-grades :
    parseType (TWord "Int" ∷ TCaret1 ∷ TArrow
               ∷ TWord "Int" ∷ TCaret0 ∷ TArrow
               ∷ TWord "Int" ∷ [])
  ≡ just (Int ⇒[ One ] (Int ⇒[ Zero ] Int) , [])
test-curried-grades = refl

------------------------------------------------------------------------
-- Negative tests (commented — uncomment to observe parse-time rejection)
------------------------------------------------------------------------

-- `A^1` alone (no arrow following) → parser returns nothing.
--
-- Uncomment to verify (would turn `test-lonely-grade` into a type error):
--
-- test-lonely-grade-rejected :
--     parseType (TWord "Int" ∷ TCaret1 ∷ [])
--   ≡ just (Int , TCaret1 ∷ [])   -- parser consumes Int, leaves ^1 as garbage
-- test-lonely-grade-rejected = refl
--
-- Actually the parser returns just (Int , TCaret1 ∷ []) and lets the
-- caller (declaration parser) see the leftover TCaret1. The caller then
-- fails because `:` wasn't consumed. So the failure is at the
-- declaration level, not inside parseType. Good diagnostic position.

-- `A^1 * B` → parser rejects because ^1 is not followed by `->`.
-- The `parseTypeAtom` parses `A`, `parseTypeProd` would try to consume
-- `*`, but `^1` isn't a product continuation. `parseArrowTail` then sees
-- `TCaret1 ∷ TStar ∷ ...`, matches the explicit reject clause, returns
-- nothing.

-- `A -> B^1` at the top level would parse as `A -> B` with leftover
-- `^1`. The caller then fails on unexpected token. (Grades on outputs
-- aren't supported.)
