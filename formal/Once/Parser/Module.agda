-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Parser.Module
--
-- Module-level parser: declarations, imports, type aliases.
-- Produces a Module record containing all declarations.
------------------------------------------------------------------------

module Once.Parser.Module where

open import Data.List using (List; []; _∷_; _++_; reverse)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; _≟_)
open import Data.Char using (Char)
open import Relation.Nullary using (yes; no)

open import Once.Type using (Type)
open import Once.TypeCheck.Raw using (RawExpr; RLam)
open import Once.Parser.Token
open import Once.Parser.Core
open import Once.Parser.Type using (parseType)
open import Once.Parser.Expr using (parseExpr)

------------------------------------------------------------------------
-- Module Types
------------------------------------------------------------------------

data AllocStrategy : Set where
  Stack Heap Pool Arena Const : AllocStrategy

record Import : Set where
  constructor mkImport
  field
    path  : List String
    alias : Maybe String

data Decl : Set where
  DTypeSig   : String → Type → Decl
  DFunDef    : String → Maybe AllocStrategy → RawExpr → Decl
  DPrimitive : String → Type → Decl
  DTypeAlias : String → List String → Type → Decl
  DImport    : Import → Decl

record Module : Set where
  constructor mkModule
  field
    decls : List Decl

------------------------------------------------------------------------
-- Import Parser
------------------------------------------------------------------------

-- | Parse a dotted module path: Module.Path.Name
{-# TERMINATING #-}
parseModulePath : Parser (List String)

-- | Parse continuation of dotted path after first name
parsePathCont : String → Parser (List String)
parsePathCont name (TDot ∷ rest) with parseModulePath rest
... | just (path , rest') = just (name ∷ path , rest')
... | nothing = just (name ∷ [] , (TDot ∷ rest))
parsePathCont name rest = just (name ∷ [] , rest)

parseModulePath toks with anyWord toks
... | nothing = nothing
... | just (name , rest) = parsePathCont name rest

-- | Parse optional 'as Alias' after import path
parseImportAlias : List String → Parser Decl
parseImportAlias path (TWord "as" ∷ rest) with anyWord rest
... | just (alias , rest') = just (DImport (mkImport path (just alias)) , rest')
... | nothing = nothing
parseImportAlias path rest = just (DImport (mkImport path nothing) , rest)

-- | Parse: import Module.Path [as Alias]
parseImport : Parser Decl
parseImport toks with parseModulePath toks
... | nothing = nothing
... | just (path , rest) = parseImportAlias path rest

------------------------------------------------------------------------
-- Allocation Annotation Parser
------------------------------------------------------------------------

-- | Parse: @stack | @heap | @pool | @arena | @const
parseAlloc : Parser AllocStrategy
parseAlloc (TAt ∷ TWord "stack" ∷ rest) = just (Stack , rest)
parseAlloc (TAt ∷ TWord "heap" ∷ rest) = just (Heap , rest)
parseAlloc (TAt ∷ TWord "pool" ∷ rest) = just (Pool , rest)
parseAlloc (TAt ∷ TWord "arena" ∷ rest) = just (Arena , rest)
parseAlloc (TAt ∷ TWord "const" ∷ rest) = just (Const , rest)
parseAlloc _ = nothing

------------------------------------------------------------------------
-- Operator Name Parser
------------------------------------------------------------------------

-- | Collect operator characters between parens
{-# TERMINATING #-}
parseOpChars : List Token → List Char → Maybe (String × List Token)
parseOpChars (TDot ∷ rest) acc = parseOpChars rest ('.' ∷ acc)
parseOpChars (TPlus ∷ rest) acc = parseOpChars rest ('+' ∷ acc)
parseOpChars (TMinus ∷ rest) acc = parseOpChars rest ('-' ∷ acc)
parseOpChars (TStar ∷ rest) acc = parseOpChars rest ('*' ∷ acc)
parseOpChars (TSlash ∷ rest) acc = parseOpChars rest ('/' ∷ acc)
parseOpChars (TPercent ∷ rest) acc = parseOpChars rest ('%' ∷ acc)
parseOpChars (TLt ∷ rest) acc = parseOpChars rest ('<' ∷ acc)
parseOpChars (TGt ∷ rest) acc = parseOpChars rest ('>' ∷ acc)
parseOpChars (TPipe ∷ rest) acc = parseOpChars rest ('|' ∷ acc)
parseOpChars (TAmpersand ∷ rest) acc = parseOpChars rest ('&' ∷ acc)
parseOpChars (TAt ∷ rest) acc = parseOpChars rest ('@' ∷ acc)
parseOpChars (TRParen ∷ rest) [] = nothing  -- empty operator
parseOpChars (TRParen ∷ rest) acc = just (Data.String.fromList (reverse acc) , rest)
parseOpChars _ _ = nothing

-- | Parse an operator name: (.) (&) (|>) etc.
parseOperatorName : Parser String
parseOperatorName (TLParen ∷ rest) = parseOpChars rest []
parseOperatorName _ = nothing

------------------------------------------------------------------------
-- Declaration Parser
------------------------------------------------------------------------

-- | Parse function parameters before =
{-# TERMINATING #-}
parseParams : List Token → List String × List Token
parseParams (TWord name ∷ rest) with rest
... | (TEquals ∷ _) = name ∷ [] , rest  -- last param before =
... | (TWord _ ∷ _) = let (params , rest') = parseParams rest
                      in  name ∷ params , rest'
... | _ = [] , (TWord name ∷ rest)
parseParams toks = [] , toks

-- | Wrap body in lambdas for each parameter
wrapLams : List String → RawExpr → RawExpr
wrapLams [] body = body
wrapLams (p ∷ ps) body = RLam p (wrapLams ps body)

-- | Parse a single declaration
parseDecl : Parser Decl

-- | Parse type alias: type Name [Params] = Type
parseTypeAlias : Parser Decl
parseTypeAlias toks with anyWord toks
... | nothing = nothing
... | just (name , rest) = go rest []
  where
  go : List Token → List String → Maybe (Decl × List Token)
  go (TEquals ∷ rest') params with parseType rest'
  ... | just (ty , rest'') = just (DTypeAlias name (reverse params) ty , rest'')
  ... | nothing = nothing
  go (TWord p ∷ rest') params = go rest' (p ∷ params)
  go _ _ = nothing

-- | Parse primitive: primitive name : Type
parsePrimitive : Parser Decl
parsePrimitive toks with anyWord toks
... | nothing = nothing
... | just (name , rest) with (expect TColon >>= λ _ → parseType) rest
...   | just (ty , rest') = just (DPrimitive name ty , rest')
...   | nothing = nothing

-- | Try to parse an allocation annotation, returning the alloc and remaining tokens
tryAlloc : List Token → Maybe AllocStrategy × List Token
tryAlloc ts with parseAlloc ts
... | just (a , rest) = just a , rest
... | nothing = nothing , ts

-- | Parse body after = sign
parseFunBody : String → Maybe AllocStrategy → List String → Parser Decl
parseFunBody name alloc params (TEquals ∷ rest) with parseExpr rest
... | just (body , rest') = just (DFunDef name alloc (wrapLams params body) , rest')
... | nothing = nothing
parseFunBody _ _ _ _ = nothing

-- | Parse function definition: name [@alloc] [params] = body
parseFunDef : String → Parser Decl
parseFunDef name toks =
  let (alloc , toks') = tryAlloc toks
      (params , toks'') = parseParams toks'
  in parseFunBody name alloc params toks''

-- | After parsing an operator name, decide: type sig or fun def
tryOpDeclAfter : String → List Token → Maybe (Decl × List Token)
tryOpDeclAfter name (TColon ∷ rest) with parseType rest
... | just (ty , rest') = just (DTypeSig name ty , rest')
... | nothing = nothing
tryOpDeclAfter name rest = parseFunDef name rest

-- | Try to parse an operator-name declaration (type sig or fun def)
tryOpDecl : List Token → Maybe (Decl × List Token)
tryOpDecl toks with parseOperatorName toks
... | nothing = nothing
... | just (name , rest) = tryOpDeclAfter name rest

parseDecl [] = nothing
-- Import
parseDecl (TWord "import" ∷ rest) = parseImport rest
-- Type alias
parseDecl (TWord "type" ∷ rest) = parseTypeAlias rest
-- Primitive
parseDecl (TWord "primitive" ∷ rest) = parsePrimitive rest
-- Operator definition: (op) ...
parseDecl (TLParen ∷ rest) = tryOpDecl (TLParen ∷ rest)
-- Type signature: name : Type
-- Note: if followed by '=' this is a syntax error (use separate lines)
parseDecl (TWord name ∷ TColon ∷ rest) with parseType rest
... | nothing = nothing
... | just (ty , TEquals ∷ _) = nothing  -- reject inline syntax: use separate lines
... | just (ty , rest') = just (DTypeSig name ty , rest')
-- Function definition: name ...
parseDecl (TWord name ∷ rest) = parseFunDef name rest
parseDecl (_ ∷ _) = nothing

------------------------------------------------------------------------
-- Module Parser
------------------------------------------------------------------------

-- | Parse all declarations (separated by newlines)
{-# TERMINATING #-}
parseDecls : Parser (List Decl)

-- | Parse remaining declarations after one successful parse
parseDeclsAfter : Decl → Parser (List Decl)
parseDeclsAfter d rest with parseDecls rest
... | just (ds , rest') = just (d ∷ ds , rest')
... | nothing = just (d ∷ [] , rest)

parseDecls toks with skipNewlines toks
... | nothing = just ([] , toks)
... | just (_ , toks') with parseDecl toks'
...   | nothing = just ([] , toks')
...   | just (d , rest) = parseDeclsAfter d rest

-- | Parse a complete module
parseModule : Parser Module
parseModule toks with parseDecls toks
... | just (ds , rest) = just (mkModule ds , rest)
... | nothing = just (mkModule [] , toks)