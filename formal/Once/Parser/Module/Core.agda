-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Parser.Module.Core
--
-- Shared types and bounded-parser primitives used across all of the
-- `Once.Parser.Module.*` submodules: the resolved module,
-- `ParseAtB` / `ParseAtB≤` wrappers, bounded lifts of the type and
-- expression sub-parsers, and the `anyWordB` token consumer.
------------------------------------------------------------------------

module Once.Parser.Module.Core where

open import Data.List using (List; _∷_; length)
open import Data.Bool using (Bool)
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂; Σ-syntax)
open import Data.String using (String; _≟_)
open import Data.Nat using (_≤_; _<_; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Nat.Induction using (<-wellFounded)

open import Once.Spec.Type using (Type)
open import Once.Spec.Surface.Syntax using (PolyType; Module)
open import Once.Internal.Syntax using (RawExpr)
open import Once.Parser.Token
open import Once.Parser.Type using (parseTypeWF)
open import Once.Parser.TypeRelation using (ParsesType-shrinks)
open import Once.Parser.Expr using (parseExprWF)
open import Once.Parser.ExprRelation using (ParsesExpr-shrinks)

------------------------------------------------------------------------
-- Module Types
--
-- A declaration and a module are the Spec's (`Once.Spec.Surface.Syntax`,
-- plan 0.122).
------------------------------------------------------------------------

-- | A module after import resolution: its declarations, references resolved
-- (the imports kept where they are written), and the signatures of the
-- modules it imports, each under the name a reference to it resolves to
-- (`showCanonical (canonical (path ++ [name]))`) — the Spec's `Imported`
-- part of the program's signature (plan 0.122).
record Resolved : Set where
  constructor resolved
  field
    rmodule  : Module
    imported : List (String × PolyType)

------------------------------------------------------------------------
-- Length-bound wrappers for sub-parsers.
------------------------------------------------------------------------

ParseAtB : ∀ {A : Set} → List Token → Set
ParseAtB {A} toks =
  Maybe (Σ[ a ∈ A ] Σ[ rest ∈ List Token ] length rest < length toks)

ParseAtB≤ : ∀ {A : Set} → List Token → Set
ParseAtB≤ {A} toks =
  Maybe (Σ[ a ∈ A ] Σ[ rest ∈ List Token ] length rest ≤ length toks)

-- The `-adapt` helpers exist so the `with`-free wrappers below
-- compile to plain function applications. An inline `with parseXWF
-- ...` version fuses the whole mutual WF-parser case-tree into the
-- wrapper's generated Haskell (tens of thousands of lines), OOMing
-- MAlonzo in downstream users.
open import Once.Parser.Type using (ParseTypeD)

parseTypeB-adapt : ∀ (toks : List Token) → ParseTypeD toks →
                   Maybe (Σ[ a ∈ Type ] Σ[ rest ∈ List Token ]
                            length rest < length toks)
parseTypeB-adapt _ nothing = nothing
parseTypeB-adapt _ (just (T , rest , d)) = just (T , rest , ParsesType-shrinks d)

parseTypeB : (toks : List Token) → ParseAtB {Type} toks
parseTypeB toks = parseTypeB-adapt toks
                    (parseTypeWF toks (<-wellFounded (length toks)))

open import Once.Parser.Expr using (ParseExprD)

parseExprB-adapt : ∀ (toks : List Token) → ParseExprD toks →
                   Maybe (Σ[ a ∈ RawExpr ] Σ[ rest ∈ List Token ]
                            length rest < length toks)
parseExprB-adapt _ nothing = nothing
parseExprB-adapt _ (just (e , rest , d)) = just (e , rest , ParsesExpr-shrinks d)

parseExprB : (toks : List Token) → ParseAtB {RawExpr} toks
parseExprB toks = parseExprB-adapt toks
                    (parseExprWF toks (<-wellFounded (length toks)))

------------------------------------------------------------------------
-- Bounded token consumers
------------------------------------------------------------------------

-- | Bounded version of anyWord: on success the remainder is strictly
-- shorter than the input.
anyWordB : (toks : List Token) → ParseAtB {String} toks
anyWordB (TWord s ∷ rest) = just (s , rest , s≤s ≤-refl)
{-# CATCHALL #-}
anyWordB _ = nothing

-- | Does the stream start with a word? PLAN 0.84: this is an executable parser
-- helper, so it belongs beside `anyWordB` — it used to live in
-- `Once.Grammar.ImportBridge`, which made three grammar RELATIONS import a
-- PROOF module. It relates definitionally to `anyWordB`, which is what the
-- import/typealias/fundef bridges rely on.
wordHead : List Token → Bool
wordHead toks = is-just (anyWordB toks)
