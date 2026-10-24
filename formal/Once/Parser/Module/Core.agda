-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Parser.Module.Core
--
-- Shared types and bounded-parser primitives used across all of the
-- `Once.Parser.Module.*` submodules: the declaration / module AST,
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
open import Once.Spec.Surface.Syntax using (PolyType; Import)
open import Once.Internal.Syntax using (RawExpr)
open import Once.Parser.Token
open import Once.Parser.Type using (parseTypeWF)
open import Once.Parser.TypeRelation using (ParsesType-shrinks)
open import Once.Parser.Expr using (parseExprWF)
open import Once.Parser.ExprRelation using (ParsesExpr-shrinks)

------------------------------------------------------------------------
-- Module Types
------------------------------------------------------------------------

-- D142: `AllocStrategy` (@stack/@heap/@pool/@arena/@const) is REMOVED from the
-- surface language. Allocation is mechanical — IR inputs/outputs are stack or
-- register-resident, bounded internals go to frontier scratch, unbounded
-- internals to the heap and are freed by the IR itself. Nothing in the source
-- picks. Supersedes D012/D013/D014; see plan 0.86.

data Decl : Set where
  -- Type signatures and primitives carry `PolyType` (not `Type`) so
  -- user-written polymorphic signatures (`swap : a * b → b * a`)
  -- survive parsing. Ground `Type` is recovered at `extractFunctions`
  -- via `isGround`/`extractGround`. Plan 0.6 Phase B.
  DTypeSig   : String → PolyType → Decl
  DFunDef    : String → RawExpr → Decl
  -- | `DSignature name ty`: a primitive the module declares. An imported
  -- module's are read from the module map (`Resolved.imported`), as the
  -- Spec's `Imported` reads them; never copied in (plan 0.122).
  -- Plan 0.98 E / D226: no effect annotation. An external arrow's effect is
  -- its CODOMAIN (`Void` halts, `Unit` emits), so `! halts` had nothing left
  -- to say.
  DSignature : String → PolyType → Decl
  DTypeAlias : String → List String → PolyType → Decl
  DImport    : Import → Decl

record Module : Set where
  constructor mkModule
  field
    decls : List Decl

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
