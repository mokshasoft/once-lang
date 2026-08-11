-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Grammar.Roundtrip
--
-- Plan 0.3 gap G1: structural round-trip theorem.
--
--   parseType (printGType g) ≡ just (toType c , [])     -- for Concrete c of g
--
-- Proven as the composition of two pieces:
--
--   1. `round-trip-rel` in `Once.Grammar.RelRoundtrip`:
--      structural induction on `Concrete g` producing a
--      `ParsesType (printGType g) (toType c) []` derivation.
--
--   2. `complete-type` in `Once.Grammar.ParserBridge`:
--      a derivation of `ParsesType toks T rest` implies
--      `parseType toks ≡ just (T , rest)`.
--
-- The old pre-WF-refactor proof of this file chained a battery of
-- `parseX-NotY` lemmas and `rewrite round-trip-X …` equations to push
-- parser reductions through abstract `printGType A ++ …` prefixes.
-- That approach broke when Parser/Type moved to well-founded recursion
-- (the abstract-Acc reductions stopped firing for `refl`). The
-- relation-plus-bridge split isolates the Acc-threading friction into
-- `ParserBridge` and leaves the round-trip derivations as clean
-- structural inductions.
------------------------------------------------------------------------

module Once.Grammar.Roundtrip where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Type using (Type)
import Once.Grammar as G
open G using (GType)
open import Once.Parser.Token using (Token)
open import Once.Parser.Type using (parseType)
open import Once.Grammar.Printer using (printGType; Concrete)
open import Once.Grammar.ParserRelation using (toType)
open import Once.Grammar.RelRoundtrip using (round-trip-rel)
open import Once.Grammar.ParserBridge using (complete-type)

------------------------------------------------------------------------
-- Top-level theorem: parseType (printGType g) ≡ just (toType c , [])
------------------------------------------------------------------------

round-trip-concrete :
  ∀ {g : GType} (c : Concrete g)
  → parseType (printGType g) ≡ just (toType c , [])
round-trip-concrete c = complete-type (round-trip-rel c)
