-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Parser
--
-- Top-level parser entry point.
-- Tokenizes a string and parses it into a Module.
------------------------------------------------------------------------

module Once.Parser where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ)
open import Relation.Nullary using (yes; no)

open import Once.Type using (Type)
open import Once.TypeCheck.Raw using (RawExpr; RVar)
open import Once.Parser.Token
open import Once.Parser.Lexer using (tokenizeString)
open import Once.Parser.Core using (Parser)
open import Once.Parser.Type using (parseType) public
open import Once.Parser.Expr using (parseExpr) public
open import Once.Parser.Module public
open import Once.Parser.Inline public
open import Once.Parser.TypeAlias public

-- Parser smoke tests (plan 0.3 G1): pull into the compilation graph
-- so a regression in parser behaviour fails `make parser`.
import Once.Parser.Tests


------------------------------------------------------------------------
-- Top-level Parse Function
------------------------------------------------------------------------

-- | Parse a source string into a Module.
-- Returns Nothing on parse failure.
parse : String → Maybe Module
parse source with parseModule (tokenizeString source)
... | just (m , _) = just m
... | nothing = nothing

------------------------------------------------------------------------
-- Processing Pipeline Helpers
------------------------------------------------------------------------

-- | Extract type aliases from a module's declarations
extractAliases : Module → TypeAliasEnv
extractAliases (mkModule ds) = go ds
  where
  go : List Decl → TypeAliasEnv
  go [] = []
  go (DTypeAlias name params body ∷ rest) = (name , params , body) ∷ go rest
  go (_ ∷ rest) = go rest

-- | Extract function definitions with their types (paired sig + def)
-- Returns: List (name, type, maybe alloc, body)
-- Processes declarations in order, matching type sigs with subsequent defs.
record FunInfo : Set where
  constructor mkFunInfo
  field
    funName  : String
    funType  : Type
    funAlloc : Maybe AllocStrategy
    funBody  : RawExpr

extractFunctions : TypeAliasEnv → Module → List FunInfo
extractFunctions aliases (mkModule ds) = go ds nothing
  where
  go : List Decl → Maybe (String × Type) → List FunInfo
  go [] _ = []
  go (DTypeSig name ty ∷ rest) _ =
    go rest (just (name , expandAliases aliases ty))
  go (DFunDef name alloc body ∷ rest) (just (sigName , sigTy)) with sigName ≟ name
  ... | yes _ = mkFunInfo name sigTy alloc body ∷ go rest nothing
  ... | no _  = go rest nothing  -- mismatched sig, skip
  -- Primitives: use RVar as placeholder body (actual impl is external)
  go (DPrimitive name ty ∷ rest) _ =
    mkFunInfo name (expandAliases aliases ty) nothing (RVar name) ∷ go rest nothing
  go (_ ∷ rest) pending = go rest pending

-- | Inline all functions and return elaboration-ready pairs
-- Each function's body is inlined with all previously-defined function bodies.
-- Returns: List (name, type, maybe alloc, inlined-body)
inlineAll : ℕ → List FunInfo → List FunInfo
inlineAll fuel fns = go [] fns
  where
  go : Defs → List FunInfo → List FunInfo
  go _ [] = []
  go defs (mkFunInfo name ty alloc body ∷ rest) =
    let inlined = inlineReferences fuel defs body
    in  mkFunInfo name ty alloc inlined ∷ go ((name , body) ∷ defs) rest