-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Parser.Module
--
-- Module-level parser: declarations, imports, type aliases.
-- Produces a Module record containing all declarations.
------------------------------------------------------------------------

module Once.Parser.Module where

open import Data.List using (List; []; _∷_; _++_; reverse; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂; Σ-syntax)
open import Data.String using (String; _≟_)
open import Data.Char using (Char)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n<1+n; n≤1+n;
                                        <-trans; ≤-<-trans; <-≤-trans;
                                        <⇒≤; m≤n⇒m≤1+n)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (Type)
open import Once.TypeCheck.Raw using (RawExpr; RLam)
open import Once.Parser.Token
open import Once.Parser.Core
open import Once.Parser.Type using (parseType; parseTypeWF; stripType)
open import Once.Parser.TypeRelation using (ParsesType-shrinks)
open import Once.Parser.Expr using (parseExpr; parseExprWF)

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
-- Length-bound wrappers for sub-parsers.
--
-- These lift `parseTypeWF` and `parseExprWF` to Σ-bounded Maybe results,
-- which lets every declaration-level helper expose its own length bound
-- without special-casing every token constructor.
------------------------------------------------------------------------

ParseAtB : ∀ {A : Set} → List Token → Set
ParseAtB {A} toks =
  Maybe (Σ[ a ∈ A ] Σ[ rest ∈ List Token ] length rest < length toks)

ParseAtB≤ : ∀ {A : Set} → List Token → Set
ParseAtB≤ {A} toks =
  Maybe (Σ[ a ∈ A ] Σ[ rest ∈ List Token ] length rest ≤ length toks)

parseTypeB : (toks : List Token) → ParseAtB {Type} toks
parseTypeB toks with parseTypeWF toks (<-wellFounded (length toks))
... | nothing = nothing
... | just (T , rest , d) = just (T , rest , ParsesType-shrinks d)

parseExprB : (toks : List Token) → ParseAtB {RawExpr} toks
parseExprB toks with parseExprWF toks (<-wellFounded (length toks))
... | nothing = nothing
... | just (e , rest , lt) = just (e , rest , lt)

------------------------------------------------------------------------
-- Bounded token consumers
------------------------------------------------------------------------

-- | Bounded version of anyWord: on success the remainder is strictly
-- shorter than the input.
anyWordB : (toks : List Token) → ParseAtB {String} toks
anyWordB (TWord s ∷ rest) = just (s , rest , s≤s ≤-refl)
anyWordB [] = nothing
anyWordB (TLParen ∷ _) = nothing
anyWordB (TRParen ∷ _) = nothing
anyWordB (TLBrace ∷ _) = nothing
anyWordB (TRBrace ∷ _) = nothing
anyWordB (TColon ∷ _) = nothing
anyWordB (TEquals ∷ _) = nothing
anyWordB (TArrow ∷ _) = nothing
anyWordB (TLambda ∷ _) = nothing
anyWordB (TComma ∷ _) = nothing
anyWordB (TSemicolon ∷ _) = nothing
anyWordB (TAt ∷ _) = nothing
anyWordB (TPipe ∷ _) = nothing
anyWordB (TDot ∷ _) = nothing
anyWordB (TPlus ∷ _) = nothing
anyWordB (TMinus ∷ _) = nothing
anyWordB (TStar ∷ _) = nothing
anyWordB (TSlash ∷ _) = nothing
anyWordB (TPercent ∷ _) = nothing
anyWordB (TAmpersand ∷ _) = nothing
anyWordB (TLt ∷ _) = nothing
anyWordB (TLe ∷ _) = nothing
anyWordB (TGt ∷ _) = nothing
anyWordB (TGe ∷ _) = nothing
anyWordB (TEqEq ∷ _) = nothing
anyWordB (TNeq ∷ _) = nothing
anyWordB (TCaret1 ∷ _) = nothing
anyWordB (TCaret0 ∷ _) = nothing
anyWordB (TCaretW ∷ _) = nothing
anyWordB (TInt _ ∷ _) = nothing
anyWordB (TString _ ∷ _) = nothing
anyWordB (TNewline ∷ _) = nothing
anyWordB (TEOF ∷ _) = nothing

------------------------------------------------------------------------
-- Import Parser
------------------------------------------------------------------------

-- | Parse a dotted module path via well-founded recursion. Each step
-- consumes one identifier via `anyWordB`.
parseModulePath-WFB : (toks : List Token) → Acc _<_ (length toks) →
                      ParseAtB {List String} toks
parseModulePath-WFB toks (acc rec) with anyWordB toks
... | nothing = nothing
... | just (name , TDot ∷ rest , bnd) with
         parseModulePath-WFB rest (rec (<-trans (s≤s ≤-refl) bnd))
...   | just (path , rest' , bnd') =
        just (name ∷ path , rest' ,
              <-trans bnd' (<-trans (s≤s ≤-refl) bnd))
...   | nothing = just (name ∷ [] , (TDot ∷ rest) , bnd)
parseModulePath-WFB toks (acc rec) | just (name , rest , bnd) =
      just (name ∷ [] , rest , bnd)

parseModulePathB : (toks : List Token) → ParseAtB {List String} toks
parseModulePathB toks = parseModulePath-WFB toks (<-wellFounded (length toks))

-- | Parse a dotted module path (plain `Parser`).
parseModulePath : Parser (List String)
parseModulePath toks with parseModulePathB toks
... | just (p , rest , _) = just (p , rest)
... | nothing = nothing

-- | Bounded variant of `as Alias`: residual ≤ input (the parser may
-- no-op and return the unchanged input).
parseImportAliasB : List String → (toks : List Token) → ParseAtB≤ {Decl} toks
parseImportAliasB path (TWord "as" ∷ rest) with anyWordB rest
... | just (alias , rest' , bnd) =
      just (DImport (mkImport path (just alias)) , rest' ,
            <⇒≤ (<-trans bnd (s≤s ≤-refl)))
... | nothing = nothing
parseImportAliasB path [] =
      just (DImport (mkImport path nothing) , [] , ≤-refl)
parseImportAliasB path (TLParen ∷ rest) =
      just (DImport (mkImport path nothing) , TLParen ∷ rest , ≤-refl)
parseImportAliasB path (TRParen ∷ rest) =
      just (DImport (mkImport path nothing) , TRParen ∷ rest , ≤-refl)
parseImportAliasB path (TLBrace ∷ rest) =
      just (DImport (mkImport path nothing) , TLBrace ∷ rest , ≤-refl)
parseImportAliasB path (TRBrace ∷ rest) =
      just (DImport (mkImport path nothing) , TRBrace ∷ rest , ≤-refl)
parseImportAliasB path (TColon ∷ rest) =
      just (DImport (mkImport path nothing) , TColon ∷ rest , ≤-refl)
parseImportAliasB path (TEquals ∷ rest) =
      just (DImport (mkImport path nothing) , TEquals ∷ rest , ≤-refl)
parseImportAliasB path (TArrow ∷ rest) =
      just (DImport (mkImport path nothing) , TArrow ∷ rest , ≤-refl)
parseImportAliasB path (TLambda ∷ rest) =
      just (DImport (mkImport path nothing) , TLambda ∷ rest , ≤-refl)
parseImportAliasB path (TComma ∷ rest) =
      just (DImport (mkImport path nothing) , TComma ∷ rest , ≤-refl)
parseImportAliasB path (TSemicolon ∷ rest) =
      just (DImport (mkImport path nothing) , TSemicolon ∷ rest , ≤-refl)
parseImportAliasB path (TAt ∷ rest) =
      just (DImport (mkImport path nothing) , TAt ∷ rest , ≤-refl)
parseImportAliasB path (TPipe ∷ rest) =
      just (DImport (mkImport path nothing) , TPipe ∷ rest , ≤-refl)
parseImportAliasB path (TDot ∷ rest) =
      just (DImport (mkImport path nothing) , TDot ∷ rest , ≤-refl)
parseImportAliasB path (TPlus ∷ rest) =
      just (DImport (mkImport path nothing) , TPlus ∷ rest , ≤-refl)
parseImportAliasB path (TMinus ∷ rest) =
      just (DImport (mkImport path nothing) , TMinus ∷ rest , ≤-refl)
parseImportAliasB path (TStar ∷ rest) =
      just (DImport (mkImport path nothing) , TStar ∷ rest , ≤-refl)
parseImportAliasB path (TSlash ∷ rest) =
      just (DImport (mkImport path nothing) , TSlash ∷ rest , ≤-refl)
parseImportAliasB path (TPercent ∷ rest) =
      just (DImport (mkImport path nothing) , TPercent ∷ rest , ≤-refl)
parseImportAliasB path (TAmpersand ∷ rest) =
      just (DImport (mkImport path nothing) , TAmpersand ∷ rest , ≤-refl)
parseImportAliasB path (TLt ∷ rest) =
      just (DImport (mkImport path nothing) , TLt ∷ rest , ≤-refl)
parseImportAliasB path (TLe ∷ rest) =
      just (DImport (mkImport path nothing) , TLe ∷ rest , ≤-refl)
parseImportAliasB path (TGt ∷ rest) =
      just (DImport (mkImport path nothing) , TGt ∷ rest , ≤-refl)
parseImportAliasB path (TGe ∷ rest) =
      just (DImport (mkImport path nothing) , TGe ∷ rest , ≤-refl)
parseImportAliasB path (TEqEq ∷ rest) =
      just (DImport (mkImport path nothing) , TEqEq ∷ rest , ≤-refl)
parseImportAliasB path (TNeq ∷ rest) =
      just (DImport (mkImport path nothing) , TNeq ∷ rest , ≤-refl)
parseImportAliasB path (TCaret1 ∷ rest) =
      just (DImport (mkImport path nothing) , TCaret1 ∷ rest , ≤-refl)
parseImportAliasB path (TCaret0 ∷ rest) =
      just (DImport (mkImport path nothing) , TCaret0 ∷ rest , ≤-refl)
parseImportAliasB path (TCaretW ∷ rest) =
      just (DImport (mkImport path nothing) , TCaretW ∷ rest , ≤-refl)
parseImportAliasB path (TInt n ∷ rest) =
      just (DImport (mkImport path nothing) , TInt n ∷ rest , ≤-refl)
parseImportAliasB path (TString s ∷ rest) =
      just (DImport (mkImport path nothing) , TString s ∷ rest , ≤-refl)
parseImportAliasB path (TNewline ∷ rest) =
      just (DImport (mkImport path nothing) , TNewline ∷ rest , ≤-refl)
parseImportAliasB path (TEOF ∷ rest) =
      just (DImport (mkImport path nothing) , TEOF ∷ rest , ≤-refl)
parseImportAliasB path (TWord s ∷ rest) with s ≟ "as"
... | yes _ = nothing  -- unreachable: handled above
... | no _ = just (DImport (mkImport path nothing) , TWord s ∷ rest , ≤-refl)

-- | Parse optional 'as Alias' after import path
parseImportAlias : List String → Parser Decl
parseImportAlias path toks with parseImportAliasB path toks
... | just (d , rest , _) = just (d , rest)
... | nothing = nothing

-- | Bounded parse of `import Module.Path [as Alias]`: consumes at
-- least the leading identifier (via parseModulePathB), so the residual
-- is strictly shorter than the input.
parseImportB : (toks : List Token) → ParseAtB {Decl} toks
parseImportB toks with parseModulePathB toks
... | nothing = nothing
... | just (path , rest , bnd) with parseImportAliasB path rest
...   | just (d , rest' , bnd') = just (d , rest' , ≤-<-trans bnd' bnd)
...   | nothing = nothing

-- | Parse: import Module.Path [as Alias]
parseImport : Parser Decl
parseImport toks with parseImportB toks
... | just (d , rest , _) = just (d , rest)
... | nothing = nothing

------------------------------------------------------------------------
-- Allocation Annotation Parser
------------------------------------------------------------------------

-- | Bounded variant: on success consumes 2 tokens (`@` + keyword).
parseAllocB : (toks : List Token) → ParseAtB {AllocStrategy} toks
parseAllocB (TAt ∷ TWord w ∷ rest) with w ≟ "stack"
... | yes _ = just (Stack , rest , s≤s (n≤1+n _))
... | no _ with w ≟ "heap"
...   | yes _ = just (Heap , rest , s≤s (n≤1+n _))
...   | no _ with w ≟ "pool"
...     | yes _ = just (Pool , rest , s≤s (n≤1+n _))
...     | no _ with w ≟ "arena"
...       | yes _ = just (Arena , rest , s≤s (n≤1+n _))
...       | no _ with w ≟ "const"
...         | yes _ = just (Const , rest , s≤s (n≤1+n _))
...         | no _ = nothing
parseAllocB [] = nothing
parseAllocB (TAt ∷ []) = nothing
parseAllocB (TAt ∷ TLParen ∷ _) = nothing
parseAllocB (TAt ∷ TRParen ∷ _) = nothing
parseAllocB (TAt ∷ TLBrace ∷ _) = nothing
parseAllocB (TAt ∷ TRBrace ∷ _) = nothing
parseAllocB (TAt ∷ TColon ∷ _) = nothing
parseAllocB (TAt ∷ TEquals ∷ _) = nothing
parseAllocB (TAt ∷ TArrow ∷ _) = nothing
parseAllocB (TAt ∷ TLambda ∷ _) = nothing
parseAllocB (TAt ∷ TComma ∷ _) = nothing
parseAllocB (TAt ∷ TSemicolon ∷ _) = nothing
parseAllocB (TAt ∷ TAt ∷ _) = nothing
parseAllocB (TAt ∷ TPipe ∷ _) = nothing
parseAllocB (TAt ∷ TDot ∷ _) = nothing
parseAllocB (TAt ∷ TPlus ∷ _) = nothing
parseAllocB (TAt ∷ TMinus ∷ _) = nothing
parseAllocB (TAt ∷ TStar ∷ _) = nothing
parseAllocB (TAt ∷ TSlash ∷ _) = nothing
parseAllocB (TAt ∷ TPercent ∷ _) = nothing
parseAllocB (TAt ∷ TAmpersand ∷ _) = nothing
parseAllocB (TAt ∷ TLt ∷ _) = nothing
parseAllocB (TAt ∷ TLe ∷ _) = nothing
parseAllocB (TAt ∷ TGt ∷ _) = nothing
parseAllocB (TAt ∷ TGe ∷ _) = nothing
parseAllocB (TAt ∷ TEqEq ∷ _) = nothing
parseAllocB (TAt ∷ TNeq ∷ _) = nothing
parseAllocB (TAt ∷ TCaret1 ∷ _) = nothing
parseAllocB (TAt ∷ TCaret0 ∷ _) = nothing
parseAllocB (TAt ∷ TCaretW ∷ _) = nothing
parseAllocB (TAt ∷ TInt _ ∷ _) = nothing
parseAllocB (TAt ∷ TString _ ∷ _) = nothing
parseAllocB (TAt ∷ TNewline ∷ _) = nothing
parseAllocB (TAt ∷ TEOF ∷ _) = nothing
parseAllocB (TWord _ ∷ _) = nothing
parseAllocB (TLParen ∷ _) = nothing
parseAllocB (TRParen ∷ _) = nothing
parseAllocB (TLBrace ∷ _) = nothing
parseAllocB (TRBrace ∷ _) = nothing
parseAllocB (TColon ∷ _) = nothing
parseAllocB (TEquals ∷ _) = nothing
parseAllocB (TArrow ∷ _) = nothing
parseAllocB (TLambda ∷ _) = nothing
parseAllocB (TComma ∷ _) = nothing
parseAllocB (TSemicolon ∷ _) = nothing
parseAllocB (TPipe ∷ _) = nothing
parseAllocB (TDot ∷ _) = nothing
parseAllocB (TPlus ∷ _) = nothing
parseAllocB (TMinus ∷ _) = nothing
parseAllocB (TStar ∷ _) = nothing
parseAllocB (TSlash ∷ _) = nothing
parseAllocB (TPercent ∷ _) = nothing
parseAllocB (TAmpersand ∷ _) = nothing
parseAllocB (TLt ∷ _) = nothing
parseAllocB (TLe ∷ _) = nothing
parseAllocB (TGt ∷ _) = nothing
parseAllocB (TGe ∷ _) = nothing
parseAllocB (TEqEq ∷ _) = nothing
parseAllocB (TNeq ∷ _) = nothing
parseAllocB (TCaret1 ∷ _) = nothing
parseAllocB (TCaret0 ∷ _) = nothing
parseAllocB (TCaretW ∷ _) = nothing
parseAllocB (TInt _ ∷ _) = nothing
parseAllocB (TString _ ∷ _) = nothing
parseAllocB (TNewline ∷ _) = nothing
parseAllocB (TEOF ∷ _) = nothing

-- | Parse: @stack | @heap | @pool | @arena | @const (plain Parser).
parseAlloc : Parser AllocStrategy
parseAlloc toks with parseAllocB toks
... | just (a , rest , _) = just (a , rest)
... | nothing = nothing

------------------------------------------------------------------------
-- Operator Name Parser
------------------------------------------------------------------------

-- | Bounded variant of `parseOpChars`: scans operator characters until
-- the closing paren. Each recursion shrinks by one token, so the
-- residual is strictly shorter than the input.
parseOpCharsB : (toks : List Token) → List Char → ParseAtB {String} toks
parseOpCharsB (TRParen ∷ rest) [] = nothing  -- empty operator
parseOpCharsB (TRParen ∷ rest) (c ∷ cs) =
  just (Data.String.fromList (reverse (c ∷ cs)) , rest , s≤s ≤-refl)
parseOpCharsB (TDot ∷ rest) cs with parseOpCharsB rest ('.' ∷ cs)
... | just (s , rest' , bnd) = just (s , rest' , <-trans bnd (s≤s ≤-refl))
... | nothing = nothing
parseOpCharsB (TPlus ∷ rest) cs with parseOpCharsB rest ('+' ∷ cs)
... | just (s , rest' , bnd) = just (s , rest' , <-trans bnd (s≤s ≤-refl))
... | nothing = nothing
parseOpCharsB (TMinus ∷ rest) cs with parseOpCharsB rest ('-' ∷ cs)
... | just (s , rest' , bnd) = just (s , rest' , <-trans bnd (s≤s ≤-refl))
... | nothing = nothing
parseOpCharsB (TStar ∷ rest) cs with parseOpCharsB rest ('*' ∷ cs)
... | just (s , rest' , bnd) = just (s , rest' , <-trans bnd (s≤s ≤-refl))
... | nothing = nothing
parseOpCharsB (TSlash ∷ rest) cs with parseOpCharsB rest ('/' ∷ cs)
... | just (s , rest' , bnd) = just (s , rest' , <-trans bnd (s≤s ≤-refl))
... | nothing = nothing
parseOpCharsB (TPercent ∷ rest) cs with parseOpCharsB rest ('%' ∷ cs)
... | just (s , rest' , bnd) = just (s , rest' , <-trans bnd (s≤s ≤-refl))
... | nothing = nothing
parseOpCharsB (TLt ∷ rest) cs with parseOpCharsB rest ('<' ∷ cs)
... | just (s , rest' , bnd) = just (s , rest' , <-trans bnd (s≤s ≤-refl))
... | nothing = nothing
parseOpCharsB (TGt ∷ rest) cs with parseOpCharsB rest ('>' ∷ cs)
... | just (s , rest' , bnd) = just (s , rest' , <-trans bnd (s≤s ≤-refl))
... | nothing = nothing
parseOpCharsB (TPipe ∷ rest) cs with parseOpCharsB rest ('|' ∷ cs)
... | just (s , rest' , bnd) = just (s , rest' , <-trans bnd (s≤s ≤-refl))
... | nothing = nothing
parseOpCharsB (TAmpersand ∷ rest) cs with parseOpCharsB rest ('&' ∷ cs)
... | just (s , rest' , bnd) = just (s , rest' , <-trans bnd (s≤s ≤-refl))
... | nothing = nothing
parseOpCharsB (TAt ∷ rest) cs with parseOpCharsB rest ('@' ∷ cs)
... | just (s , rest' , bnd) = just (s , rest' , <-trans bnd (s≤s ≤-refl))
... | nothing = nothing
parseOpCharsB [] _ = nothing
parseOpCharsB (TWord _ ∷ _) _ = nothing
parseOpCharsB (TLParen ∷ _) _ = nothing
parseOpCharsB (TLBrace ∷ _) _ = nothing
parseOpCharsB (TRBrace ∷ _) _ = nothing
parseOpCharsB (TColon ∷ _) _ = nothing
parseOpCharsB (TEquals ∷ _) _ = nothing
parseOpCharsB (TArrow ∷ _) _ = nothing
parseOpCharsB (TLambda ∷ _) _ = nothing
parseOpCharsB (TComma ∷ _) _ = nothing
parseOpCharsB (TSemicolon ∷ _) _ = nothing
parseOpCharsB (TLe ∷ _) _ = nothing
parseOpCharsB (TGe ∷ _) _ = nothing
parseOpCharsB (TEqEq ∷ _) _ = nothing
parseOpCharsB (TNeq ∷ _) _ = nothing
parseOpCharsB (TCaret1 ∷ _) _ = nothing
parseOpCharsB (TCaret0 ∷ _) _ = nothing
parseOpCharsB (TCaretW ∷ _) _ = nothing
parseOpCharsB (TInt _ ∷ _) _ = nothing
parseOpCharsB (TString _ ∷ _) _ = nothing
parseOpCharsB (TNewline ∷ _) _ = nothing
parseOpCharsB (TEOF ∷ _) _ = nothing

-- | Collect operator characters between parens (plain).
parseOpChars : List Token → List Char → Maybe (String × List Token)
parseOpChars toks cs with parseOpCharsB toks cs
... | just (s , rest , _) = just (s , rest)
... | nothing = nothing

-- | Bounded variant: on success consumes `(` + operator chars + `)`.
parseOperatorNameB : (toks : List Token) → ParseAtB {String} toks
parseOperatorNameB (TLParen ∷ rest) with parseOpCharsB rest []
... | just (s , rest' , bnd) = just (s , rest' , <-trans bnd (s≤s ≤-refl))
... | nothing = nothing
parseOperatorNameB [] = nothing
parseOperatorNameB (TWord _ ∷ _) = nothing
parseOperatorNameB (TRParen ∷ _) = nothing
parseOperatorNameB (TLBrace ∷ _) = nothing
parseOperatorNameB (TRBrace ∷ _) = nothing
parseOperatorNameB (TColon ∷ _) = nothing
parseOperatorNameB (TEquals ∷ _) = nothing
parseOperatorNameB (TArrow ∷ _) = nothing
parseOperatorNameB (TLambda ∷ _) = nothing
parseOperatorNameB (TComma ∷ _) = nothing
parseOperatorNameB (TSemicolon ∷ _) = nothing
parseOperatorNameB (TAt ∷ _) = nothing
parseOperatorNameB (TPipe ∷ _) = nothing
parseOperatorNameB (TDot ∷ _) = nothing
parseOperatorNameB (TPlus ∷ _) = nothing
parseOperatorNameB (TMinus ∷ _) = nothing
parseOperatorNameB (TStar ∷ _) = nothing
parseOperatorNameB (TSlash ∷ _) = nothing
parseOperatorNameB (TPercent ∷ _) = nothing
parseOperatorNameB (TAmpersand ∷ _) = nothing
parseOperatorNameB (TLt ∷ _) = nothing
parseOperatorNameB (TLe ∷ _) = nothing
parseOperatorNameB (TGt ∷ _) = nothing
parseOperatorNameB (TGe ∷ _) = nothing
parseOperatorNameB (TEqEq ∷ _) = nothing
parseOperatorNameB (TNeq ∷ _) = nothing
parseOperatorNameB (TCaret1 ∷ _) = nothing
parseOperatorNameB (TCaret0 ∷ _) = nothing
parseOperatorNameB (TCaretW ∷ _) = nothing
parseOperatorNameB (TInt _ ∷ _) = nothing
parseOperatorNameB (TString _ ∷ _) = nothing
parseOperatorNameB (TNewline ∷ _) = nothing
parseOperatorNameB (TEOF ∷ _) = nothing

-- | Parse an operator name: (.) (&) (|>) etc.
parseOperatorName : Parser String
parseOperatorName toks with parseOperatorNameB toks
... | just (s , rest , _) = just (s , rest)
... | nothing = nothing

------------------------------------------------------------------------
-- Declaration Parser
------------------------------------------------------------------------

-- | Wrap body in lambdas for each parameter
wrapLams : List String → RawExpr → RawExpr
wrapLams [] body = body
wrapLams (p ∷ ps) body = RLam p (wrapLams ps body)

-- | Bounded parse of function parameters before `=`. This always
-- succeeds (returns the empty list for no params) and is weakly
-- shrinking: the residual is ≤ the input. Structurally recursive on
-- the token list, with the `(TWord _ ∷ TWord _ ∷ _)` case recursing on
-- a strictly smaller tail.
parseParamsB : (toks : List Token) →
               Σ[ ps ∈ List String ] Σ[ rest ∈ List Token ]
                 length rest ≤ length toks
parseParamsB [] = [] , [] , ≤-refl
parseParamsB (TWord name ∷ TEquals ∷ rest) = name ∷ [] , TEquals ∷ rest , n≤1+n _
parseParamsB (TWord name ∷ TWord m ∷ rest)
  with parseParamsB (TWord m ∷ rest)
... | params , rest' , bnd =
      name ∷ params , rest' , ≤-trans bnd (n≤1+n _)
parseParamsB (TWord name ∷ []) = [] , TWord name ∷ [] , ≤-refl
parseParamsB (TWord name ∷ TLParen ∷ rest) = [] , TWord name ∷ TLParen ∷ rest , ≤-refl
parseParamsB (TWord name ∷ TRParen ∷ rest) = [] , TWord name ∷ TRParen ∷ rest , ≤-refl
parseParamsB (TWord name ∷ TLBrace ∷ rest) = [] , TWord name ∷ TLBrace ∷ rest , ≤-refl
parseParamsB (TWord name ∷ TRBrace ∷ rest) = [] , TWord name ∷ TRBrace ∷ rest , ≤-refl
parseParamsB (TWord name ∷ TColon ∷ rest) = [] , TWord name ∷ TColon ∷ rest , ≤-refl
parseParamsB (TWord name ∷ TArrow ∷ rest) = [] , TWord name ∷ TArrow ∷ rest , ≤-refl
parseParamsB (TWord name ∷ TLambda ∷ rest) = [] , TWord name ∷ TLambda ∷ rest , ≤-refl
parseParamsB (TWord name ∷ TComma ∷ rest) = [] , TWord name ∷ TComma ∷ rest , ≤-refl
parseParamsB (TWord name ∷ TSemicolon ∷ rest) = [] , TWord name ∷ TSemicolon ∷ rest , ≤-refl
parseParamsB (TWord name ∷ TAt ∷ rest) = [] , TWord name ∷ TAt ∷ rest , ≤-refl
parseParamsB (TWord name ∷ TPipe ∷ rest) = [] , TWord name ∷ TPipe ∷ rest , ≤-refl
parseParamsB (TWord name ∷ TDot ∷ rest) = [] , TWord name ∷ TDot ∷ rest , ≤-refl
parseParamsB (TWord name ∷ TPlus ∷ rest) = [] , TWord name ∷ TPlus ∷ rest , ≤-refl
parseParamsB (TWord name ∷ TMinus ∷ rest) = [] , TWord name ∷ TMinus ∷ rest , ≤-refl
parseParamsB (TWord name ∷ TStar ∷ rest) = [] , TWord name ∷ TStar ∷ rest , ≤-refl
parseParamsB (TWord name ∷ TSlash ∷ rest) = [] , TWord name ∷ TSlash ∷ rest , ≤-refl
parseParamsB (TWord name ∷ TPercent ∷ rest) = [] , TWord name ∷ TPercent ∷ rest , ≤-refl
parseParamsB (TWord name ∷ TAmpersand ∷ rest) = [] , TWord name ∷ TAmpersand ∷ rest , ≤-refl
parseParamsB (TWord name ∷ TLt ∷ rest) = [] , TWord name ∷ TLt ∷ rest , ≤-refl
parseParamsB (TWord name ∷ TLe ∷ rest) = [] , TWord name ∷ TLe ∷ rest , ≤-refl
parseParamsB (TWord name ∷ TGt ∷ rest) = [] , TWord name ∷ TGt ∷ rest , ≤-refl
parseParamsB (TWord name ∷ TGe ∷ rest) = [] , TWord name ∷ TGe ∷ rest , ≤-refl
parseParamsB (TWord name ∷ TEqEq ∷ rest) = [] , TWord name ∷ TEqEq ∷ rest , ≤-refl
parseParamsB (TWord name ∷ TNeq ∷ rest) = [] , TWord name ∷ TNeq ∷ rest , ≤-refl
parseParamsB (TWord name ∷ TCaret1 ∷ rest) = [] , TWord name ∷ TCaret1 ∷ rest , ≤-refl
parseParamsB (TWord name ∷ TCaret0 ∷ rest) = [] , TWord name ∷ TCaret0 ∷ rest , ≤-refl
parseParamsB (TWord name ∷ TCaretW ∷ rest) = [] , TWord name ∷ TCaretW ∷ rest , ≤-refl
parseParamsB (TWord name ∷ TInt n ∷ rest) = [] , TWord name ∷ TInt n ∷ rest , ≤-refl
parseParamsB (TWord name ∷ TString s ∷ rest) = [] , TWord name ∷ TString s ∷ rest , ≤-refl
parseParamsB (TWord name ∷ TNewline ∷ rest) = [] , TWord name ∷ TNewline ∷ rest , ≤-refl
parseParamsB (TWord name ∷ TEOF ∷ rest) = [] , TWord name ∷ TEOF ∷ rest , ≤-refl
parseParamsB (TLParen ∷ rest) = [] , TLParen ∷ rest , ≤-refl
parseParamsB (TRParen ∷ rest) = [] , TRParen ∷ rest , ≤-refl
parseParamsB (TLBrace ∷ rest) = [] , TLBrace ∷ rest , ≤-refl
parseParamsB (TRBrace ∷ rest) = [] , TRBrace ∷ rest , ≤-refl
parseParamsB (TColon ∷ rest) = [] , TColon ∷ rest , ≤-refl
parseParamsB (TEquals ∷ rest) = [] , TEquals ∷ rest , ≤-refl
parseParamsB (TArrow ∷ rest) = [] , TArrow ∷ rest , ≤-refl
parseParamsB (TLambda ∷ rest) = [] , TLambda ∷ rest , ≤-refl
parseParamsB (TComma ∷ rest) = [] , TComma ∷ rest , ≤-refl
parseParamsB (TSemicolon ∷ rest) = [] , TSemicolon ∷ rest , ≤-refl
parseParamsB (TAt ∷ rest) = [] , TAt ∷ rest , ≤-refl
parseParamsB (TPipe ∷ rest) = [] , TPipe ∷ rest , ≤-refl
parseParamsB (TDot ∷ rest) = [] , TDot ∷ rest , ≤-refl
parseParamsB (TPlus ∷ rest) = [] , TPlus ∷ rest , ≤-refl
parseParamsB (TMinus ∷ rest) = [] , TMinus ∷ rest , ≤-refl
parseParamsB (TStar ∷ rest) = [] , TStar ∷ rest , ≤-refl
parseParamsB (TSlash ∷ rest) = [] , TSlash ∷ rest , ≤-refl
parseParamsB (TPercent ∷ rest) = [] , TPercent ∷ rest , ≤-refl
parseParamsB (TAmpersand ∷ rest) = [] , TAmpersand ∷ rest , ≤-refl
parseParamsB (TLt ∷ rest) = [] , TLt ∷ rest , ≤-refl
parseParamsB (TLe ∷ rest) = [] , TLe ∷ rest , ≤-refl
parseParamsB (TGt ∷ rest) = [] , TGt ∷ rest , ≤-refl
parseParamsB (TGe ∷ rest) = [] , TGe ∷ rest , ≤-refl
parseParamsB (TEqEq ∷ rest) = [] , TEqEq ∷ rest , ≤-refl
parseParamsB (TNeq ∷ rest) = [] , TNeq ∷ rest , ≤-refl
parseParamsB (TCaret1 ∷ rest) = [] , TCaret1 ∷ rest , ≤-refl
parseParamsB (TCaret0 ∷ rest) = [] , TCaret0 ∷ rest , ≤-refl
parseParamsB (TCaretW ∷ rest) = [] , TCaretW ∷ rest , ≤-refl
parseParamsB (TInt n ∷ rest) = [] , TInt n ∷ rest , ≤-refl
parseParamsB (TString s ∷ rest) = [] , TString s ∷ rest , ≤-refl
parseParamsB (TNewline ∷ rest) = [] , TNewline ∷ rest , ≤-refl
parseParamsB (TEOF ∷ rest) = [] , TEOF ∷ rest , ≤-refl

parseParams : List Token → List String × List Token
parseParams toks = let (ps , rest , _) = parseParamsB toks in (ps , rest)

-- | Try to parse an allocation annotation, returning alloc + remaining
-- tokens; the residual is ≤ the input length.
tryAllocB : (toks : List Token) →
            Maybe AllocStrategy × Σ[ rest ∈ List Token ]
              length rest ≤ length toks
tryAllocB toks with parseAllocB toks
... | just (a , rest , bnd) = just a , rest , <⇒≤ bnd
... | nothing = nothing , toks , ≤-refl

tryAlloc : List Token → Maybe AllocStrategy × List Token
tryAlloc toks = let (a , rest , _) = tryAllocB toks in (a , rest)

-- | Bounded parse of function body after `=`: consumes `=` plus a
-- non-empty expression, so the residual is strictly shorter.
parseFunBodyB : String → Maybe AllocStrategy → List String →
                (toks : List Token) → ParseAtB {Decl} toks
parseFunBodyB name alloc params (TEquals ∷ rest) with parseExprB rest
... | just (body , rest' , bnd) =
      just (DFunDef name alloc (wrapLams params body) , rest' ,
            <-trans bnd (s≤s ≤-refl))
... | nothing = nothing
parseFunBodyB _ _ _ [] = nothing
parseFunBodyB _ _ _ (TWord _ ∷ _) = nothing
parseFunBodyB _ _ _ (TLParen ∷ _) = nothing
parseFunBodyB _ _ _ (TRParen ∷ _) = nothing
parseFunBodyB _ _ _ (TLBrace ∷ _) = nothing
parseFunBodyB _ _ _ (TRBrace ∷ _) = nothing
parseFunBodyB _ _ _ (TColon ∷ _) = nothing
parseFunBodyB _ _ _ (TArrow ∷ _) = nothing
parseFunBodyB _ _ _ (TLambda ∷ _) = nothing
parseFunBodyB _ _ _ (TComma ∷ _) = nothing
parseFunBodyB _ _ _ (TSemicolon ∷ _) = nothing
parseFunBodyB _ _ _ (TAt ∷ _) = nothing
parseFunBodyB _ _ _ (TPipe ∷ _) = nothing
parseFunBodyB _ _ _ (TDot ∷ _) = nothing
parseFunBodyB _ _ _ (TPlus ∷ _) = nothing
parseFunBodyB _ _ _ (TMinus ∷ _) = nothing
parseFunBodyB _ _ _ (TStar ∷ _) = nothing
parseFunBodyB _ _ _ (TSlash ∷ _) = nothing
parseFunBodyB _ _ _ (TPercent ∷ _) = nothing
parseFunBodyB _ _ _ (TAmpersand ∷ _) = nothing
parseFunBodyB _ _ _ (TLt ∷ _) = nothing
parseFunBodyB _ _ _ (TLe ∷ _) = nothing
parseFunBodyB _ _ _ (TGt ∷ _) = nothing
parseFunBodyB _ _ _ (TGe ∷ _) = nothing
parseFunBodyB _ _ _ (TEqEq ∷ _) = nothing
parseFunBodyB _ _ _ (TNeq ∷ _) = nothing
parseFunBodyB _ _ _ (TCaret1 ∷ _) = nothing
parseFunBodyB _ _ _ (TCaret0 ∷ _) = nothing
parseFunBodyB _ _ _ (TCaretW ∷ _) = nothing
parseFunBodyB _ _ _ (TInt _ ∷ _) = nothing
parseFunBodyB _ _ _ (TString _ ∷ _) = nothing
parseFunBodyB _ _ _ (TNewline ∷ _) = nothing
parseFunBodyB _ _ _ (TEOF ∷ _) = nothing

parseFunBody : String → Maybe AllocStrategy → List String → Parser Decl
parseFunBody name alloc params toks with parseFunBodyB name alloc params toks
... | just (d , rest , _) = just (d , rest)
... | nothing = nothing

-- | Bounded parse of a function definition: `name [@alloc] [params] = body`.
-- The total shrink is (parseFunBody strict) × (parseParams weak) ×
-- (tryAlloc weak), giving an overall strict decrease.
parseFunDefB : String → (toks : List Token) → ParseAtB {Decl} toks
parseFunDefB name toks with tryAllocB toks
... | alloc , toks' , allocBnd with parseParamsB toks'
...   | params , toks'' , paramsBnd
      with parseFunBodyB name alloc params toks''
...     | just (d , rest , bodyBnd) =
          just (d , rest , <-≤-trans (<-≤-trans bodyBnd paramsBnd) allocBnd)
...     | nothing = nothing

parseFunDef : String → Parser Decl
parseFunDef name toks with parseFunDefB name toks
... | just (d , rest , _) = just (d , rest)
... | nothing = nothing

-- | After parsing an operator name, decide: type sig or fun def.
-- Weak shrink: residual ≤ input.
tryOpDeclAfterB : String → (toks : List Token) → ParseAtB≤ {Decl} toks
tryOpDeclAfterB name (TColon ∷ rest) with parseTypeB rest
... | just (ty , rest' , bnd) =
      just (DTypeSig name ty , rest' , <⇒≤ (<-trans bnd (s≤s ≤-refl)))
... | nothing = nothing
tryOpDeclAfterB name [] with parseFunDefB name []
... | just (d , rest , bnd) = just (d , rest , <⇒≤ bnd)
... | nothing = nothing
tryOpDeclAfterB name (TWord w ∷ rest) with parseFunDefB name (TWord w ∷ rest)
... | just (d , rest' , bnd) = just (d , rest' , <⇒≤ bnd)
... | nothing = nothing
tryOpDeclAfterB name (TLParen ∷ rest) with parseFunDefB name (TLParen ∷ rest)
... | just (d , rest' , bnd) = just (d , rest' , <⇒≤ bnd)
... | nothing = nothing
tryOpDeclAfterB name (TRParen ∷ rest) with parseFunDefB name (TRParen ∷ rest)
... | just (d , rest' , bnd) = just (d , rest' , <⇒≤ bnd)
... | nothing = nothing
tryOpDeclAfterB name (TLBrace ∷ rest) with parseFunDefB name (TLBrace ∷ rest)
... | just (d , rest' , bnd) = just (d , rest' , <⇒≤ bnd)
... | nothing = nothing
tryOpDeclAfterB name (TRBrace ∷ rest) with parseFunDefB name (TRBrace ∷ rest)
... | just (d , rest' , bnd) = just (d , rest' , <⇒≤ bnd)
... | nothing = nothing
tryOpDeclAfterB name (TEquals ∷ rest) with parseFunDefB name (TEquals ∷ rest)
... | just (d , rest' , bnd) = just (d , rest' , <⇒≤ bnd)
... | nothing = nothing
tryOpDeclAfterB name (TArrow ∷ rest) with parseFunDefB name (TArrow ∷ rest)
... | just (d , rest' , bnd) = just (d , rest' , <⇒≤ bnd)
... | nothing = nothing
tryOpDeclAfterB name (TLambda ∷ rest) with parseFunDefB name (TLambda ∷ rest)
... | just (d , rest' , bnd) = just (d , rest' , <⇒≤ bnd)
... | nothing = nothing
tryOpDeclAfterB name (TComma ∷ rest) with parseFunDefB name (TComma ∷ rest)
... | just (d , rest' , bnd) = just (d , rest' , <⇒≤ bnd)
... | nothing = nothing
tryOpDeclAfterB name (TSemicolon ∷ rest) with parseFunDefB name (TSemicolon ∷ rest)
... | just (d , rest' , bnd) = just (d , rest' , <⇒≤ bnd)
... | nothing = nothing
tryOpDeclAfterB name (TAt ∷ rest) with parseFunDefB name (TAt ∷ rest)
... | just (d , rest' , bnd) = just (d , rest' , <⇒≤ bnd)
... | nothing = nothing
tryOpDeclAfterB name (TPipe ∷ rest) with parseFunDefB name (TPipe ∷ rest)
... | just (d , rest' , bnd) = just (d , rest' , <⇒≤ bnd)
... | nothing = nothing
tryOpDeclAfterB name (TDot ∷ rest) with parseFunDefB name (TDot ∷ rest)
... | just (d , rest' , bnd) = just (d , rest' , <⇒≤ bnd)
... | nothing = nothing
tryOpDeclAfterB name (TPlus ∷ rest) with parseFunDefB name (TPlus ∷ rest)
... | just (d , rest' , bnd) = just (d , rest' , <⇒≤ bnd)
... | nothing = nothing
tryOpDeclAfterB name (TMinus ∷ rest) with parseFunDefB name (TMinus ∷ rest)
... | just (d , rest' , bnd) = just (d , rest' , <⇒≤ bnd)
... | nothing = nothing
tryOpDeclAfterB name (TStar ∷ rest) with parseFunDefB name (TStar ∷ rest)
... | just (d , rest' , bnd) = just (d , rest' , <⇒≤ bnd)
... | nothing = nothing
tryOpDeclAfterB name (TSlash ∷ rest) with parseFunDefB name (TSlash ∷ rest)
... | just (d , rest' , bnd) = just (d , rest' , <⇒≤ bnd)
... | nothing = nothing
tryOpDeclAfterB name (TPercent ∷ rest) with parseFunDefB name (TPercent ∷ rest)
... | just (d , rest' , bnd) = just (d , rest' , <⇒≤ bnd)
... | nothing = nothing
tryOpDeclAfterB name (TAmpersand ∷ rest) with parseFunDefB name (TAmpersand ∷ rest)
... | just (d , rest' , bnd) = just (d , rest' , <⇒≤ bnd)
... | nothing = nothing
tryOpDeclAfterB name (TLt ∷ rest) with parseFunDefB name (TLt ∷ rest)
... | just (d , rest' , bnd) = just (d , rest' , <⇒≤ bnd)
... | nothing = nothing
tryOpDeclAfterB name (TLe ∷ rest) with parseFunDefB name (TLe ∷ rest)
... | just (d , rest' , bnd) = just (d , rest' , <⇒≤ bnd)
... | nothing = nothing
tryOpDeclAfterB name (TGt ∷ rest) with parseFunDefB name (TGt ∷ rest)
... | just (d , rest' , bnd) = just (d , rest' , <⇒≤ bnd)
... | nothing = nothing
tryOpDeclAfterB name (TGe ∷ rest) with parseFunDefB name (TGe ∷ rest)
... | just (d , rest' , bnd) = just (d , rest' , <⇒≤ bnd)
... | nothing = nothing
tryOpDeclAfterB name (TEqEq ∷ rest) with parseFunDefB name (TEqEq ∷ rest)
... | just (d , rest' , bnd) = just (d , rest' , <⇒≤ bnd)
... | nothing = nothing
tryOpDeclAfterB name (TNeq ∷ rest) with parseFunDefB name (TNeq ∷ rest)
... | just (d , rest' , bnd) = just (d , rest' , <⇒≤ bnd)
... | nothing = nothing
tryOpDeclAfterB name (TCaret1 ∷ rest) with parseFunDefB name (TCaret1 ∷ rest)
... | just (d , rest' , bnd) = just (d , rest' , <⇒≤ bnd)
... | nothing = nothing
tryOpDeclAfterB name (TCaret0 ∷ rest) with parseFunDefB name (TCaret0 ∷ rest)
... | just (d , rest' , bnd) = just (d , rest' , <⇒≤ bnd)
... | nothing = nothing
tryOpDeclAfterB name (TCaretW ∷ rest) with parseFunDefB name (TCaretW ∷ rest)
... | just (d , rest' , bnd) = just (d , rest' , <⇒≤ bnd)
... | nothing = nothing
tryOpDeclAfterB name (TInt n ∷ rest) with parseFunDefB name (TInt n ∷ rest)
... | just (d , rest' , bnd) = just (d , rest' , <⇒≤ bnd)
... | nothing = nothing
tryOpDeclAfterB name (TString s ∷ rest) with parseFunDefB name (TString s ∷ rest)
... | just (d , rest' , bnd) = just (d , rest' , <⇒≤ bnd)
... | nothing = nothing
tryOpDeclAfterB name (TNewline ∷ rest) with parseFunDefB name (TNewline ∷ rest)
... | just (d , rest' , bnd) = just (d , rest' , <⇒≤ bnd)
... | nothing = nothing
tryOpDeclAfterB name (TEOF ∷ rest) with parseFunDefB name (TEOF ∷ rest)
... | just (d , rest' , bnd) = just (d , rest' , <⇒≤ bnd)
... | nothing = nothing

tryOpDeclAfter : String → List Token → Maybe (Decl × List Token)
tryOpDeclAfter name toks with tryOpDeclAfterB name toks
... | just (d , rest , _) = just (d , rest)
... | nothing = nothing

-- | Try to parse an operator-name declaration (type sig or fun def).
-- Strictly shrinks (consumes at least `(op)`).
tryOpDeclB : (toks : List Token) → ParseAtB {Decl} toks
tryOpDeclB toks with parseOperatorNameB toks
... | nothing = nothing
... | just (name , rest , bnd) with tryOpDeclAfterB name rest
...   | just (d , rest' , bnd') = just (d , rest' , ≤-<-trans bnd' bnd)
...   | nothing = nothing

tryOpDecl : List Token → Maybe (Decl × List Token)
tryOpDecl toks with tryOpDeclB toks
... | just (d , rest , _) = just (d , rest)
... | nothing = nothing

-- | Parameter-scanning helper inside parseTypeAlias. Consumes `=`
-- plus a type, so the residual is strictly shorter. Recursion shrinks
-- by one token when scanning a `TWord` parameter.
goTypeAliasB : String → (toks : List Token) → List String →
               ParseAtB {Decl} toks
goTypeAliasB name (TEquals ∷ rest') params with parseTypeB rest'
... | just (ty , rest'' , bnd) =
      just (DTypeAlias name (reverse params) ty , rest'' ,
            <-trans bnd (s≤s ≤-refl))
... | nothing = nothing
goTypeAliasB name (TWord p ∷ rest') params with goTypeAliasB name rest' (p ∷ params)
... | just (d , rest'' , bnd) = just (d , rest'' , <-trans bnd (s≤s ≤-refl))
... | nothing = nothing
goTypeAliasB _ [] _ = nothing
goTypeAliasB _ (TLParen ∷ _) _ = nothing
goTypeAliasB _ (TRParen ∷ _) _ = nothing
goTypeAliasB _ (TLBrace ∷ _) _ = nothing
goTypeAliasB _ (TRBrace ∷ _) _ = nothing
goTypeAliasB _ (TColon ∷ _) _ = nothing
goTypeAliasB _ (TArrow ∷ _) _ = nothing
goTypeAliasB _ (TLambda ∷ _) _ = nothing
goTypeAliasB _ (TComma ∷ _) _ = nothing
goTypeAliasB _ (TSemicolon ∷ _) _ = nothing
goTypeAliasB _ (TAt ∷ _) _ = nothing
goTypeAliasB _ (TPipe ∷ _) _ = nothing
goTypeAliasB _ (TDot ∷ _) _ = nothing
goTypeAliasB _ (TPlus ∷ _) _ = nothing
goTypeAliasB _ (TMinus ∷ _) _ = nothing
goTypeAliasB _ (TStar ∷ _) _ = nothing
goTypeAliasB _ (TSlash ∷ _) _ = nothing
goTypeAliasB _ (TPercent ∷ _) _ = nothing
goTypeAliasB _ (TAmpersand ∷ _) _ = nothing
goTypeAliasB _ (TLt ∷ _) _ = nothing
goTypeAliasB _ (TLe ∷ _) _ = nothing
goTypeAliasB _ (TGt ∷ _) _ = nothing
goTypeAliasB _ (TGe ∷ _) _ = nothing
goTypeAliasB _ (TEqEq ∷ _) _ = nothing
goTypeAliasB _ (TNeq ∷ _) _ = nothing
goTypeAliasB _ (TCaret1 ∷ _) _ = nothing
goTypeAliasB _ (TCaret0 ∷ _) _ = nothing
goTypeAliasB _ (TCaretW ∷ _) _ = nothing
goTypeAliasB _ (TInt _ ∷ _) _ = nothing
goTypeAliasB _ (TString _ ∷ _) _ = nothing
goTypeAliasB _ (TNewline ∷ _) _ = nothing
goTypeAliasB _ (TEOF ∷ _) _ = nothing

parseTypeAliasB : (toks : List Token) → ParseAtB {Decl} toks
parseTypeAliasB toks with anyWordB toks
... | nothing = nothing
... | just (name , rest , bnd) with goTypeAliasB name rest []
...   | just (d , rest' , bnd') = just (d , rest' , <-trans bnd' bnd)
...   | nothing = nothing

parseTypeAlias : Parser Decl
parseTypeAlias toks with parseTypeAliasB toks
... | just (d , rest , _) = just (d , rest)
... | nothing = nothing

parsePrimitiveB : (toks : List Token) → ParseAtB {Decl} toks
parsePrimitiveB toks with anyWordB toks
... | nothing = nothing
... | just (name , TColon ∷ rest , bnd) with parseTypeB rest
...   | just (ty , rest' , bnd') =
        just (DPrimitive name ty , rest' ,
              <-trans (<-trans bnd' (s≤s ≤-refl)) bnd)
...   | nothing = nothing
parsePrimitiveB toks | just (_ , [] , _) = nothing
parsePrimitiveB toks | just (_ , TWord _ ∷ _ , _) = nothing
parsePrimitiveB toks | just (_ , TLParen ∷ _ , _) = nothing
parsePrimitiveB toks | just (_ , TRParen ∷ _ , _) = nothing
parsePrimitiveB toks | just (_ , TLBrace ∷ _ , _) = nothing
parsePrimitiveB toks | just (_ , TRBrace ∷ _ , _) = nothing
parsePrimitiveB toks | just (_ , TEquals ∷ _ , _) = nothing
parsePrimitiveB toks | just (_ , TArrow ∷ _ , _) = nothing
parsePrimitiveB toks | just (_ , TLambda ∷ _ , _) = nothing
parsePrimitiveB toks | just (_ , TComma ∷ _ , _) = nothing
parsePrimitiveB toks | just (_ , TSemicolon ∷ _ , _) = nothing
parsePrimitiveB toks | just (_ , TAt ∷ _ , _) = nothing
parsePrimitiveB toks | just (_ , TPipe ∷ _ , _) = nothing
parsePrimitiveB toks | just (_ , TDot ∷ _ , _) = nothing
parsePrimitiveB toks | just (_ , TPlus ∷ _ , _) = nothing
parsePrimitiveB toks | just (_ , TMinus ∷ _ , _) = nothing
parsePrimitiveB toks | just (_ , TStar ∷ _ , _) = nothing
parsePrimitiveB toks | just (_ , TSlash ∷ _ , _) = nothing
parsePrimitiveB toks | just (_ , TPercent ∷ _ , _) = nothing
parsePrimitiveB toks | just (_ , TAmpersand ∷ _ , _) = nothing
parsePrimitiveB toks | just (_ , TLt ∷ _ , _) = nothing
parsePrimitiveB toks | just (_ , TLe ∷ _ , _) = nothing
parsePrimitiveB toks | just (_ , TGt ∷ _ , _) = nothing
parsePrimitiveB toks | just (_ , TGe ∷ _ , _) = nothing
parsePrimitiveB toks | just (_ , TEqEq ∷ _ , _) = nothing
parsePrimitiveB toks | just (_ , TNeq ∷ _ , _) = nothing
parsePrimitiveB toks | just (_ , TCaret1 ∷ _ , _) = nothing
parsePrimitiveB toks | just (_ , TCaret0 ∷ _ , _) = nothing
parsePrimitiveB toks | just (_ , TCaretW ∷ _ , _) = nothing
parsePrimitiveB toks | just (_ , TInt _ ∷ _ , _) = nothing
parsePrimitiveB toks | just (_ , TString _ ∷ _ , _) = nothing
parsePrimitiveB toks | just (_ , TNewline ∷ _ , _) = nothing
parsePrimitiveB toks | just (_ , TEOF ∷ _ , _) = nothing

parsePrimitive : Parser Decl
parsePrimitive toks with parsePrimitiveB toks
... | just (d , rest , _) = just (d , rest)
... | nothing = nothing

-- | Bounded parse of a single declaration. On success the residual is
-- strictly shorter than the input, which gives us the measure to do
-- well-founded recursion in `parseDeclsWF` below.
parseDeclB : (toks : List Token) → ParseAtB {Decl} toks
parseDeclB [] = nothing
parseDeclB (TWord w ∷ rest) with w ≟ "import"
... | yes _ with parseImportB rest
...   | just (d , rest' , bnd) = just (d , rest' , <-trans bnd (s≤s ≤-refl))
...   | nothing = nothing
parseDeclB (TWord w ∷ rest) | no _ with w ≟ "type"
... | yes _ with parseTypeAliasB rest
...   | just (d , rest' , bnd) = just (d , rest' , <-trans bnd (s≤s ≤-refl))
...   | nothing = nothing
parseDeclB (TWord w ∷ rest) | no _ | no _ with w ≟ "primitive"
... | yes _ with parsePrimitiveB rest
...   | just (d , rest' , bnd) = just (d , rest' , <-trans bnd (s≤s ≤-refl))
...   | nothing = nothing
parseDeclB (TWord w ∷ TColon ∷ rest) | no _ | no _ | no _ with parseTypeB rest
... | nothing = nothing
... | just (ty , TEquals ∷ _ , _) = nothing
... | just (ty , rest' , bnd) =
      just (DTypeSig w ty , rest' ,
            <-trans (<-trans bnd (s≤s ≤-refl)) (s≤s ≤-refl))
parseDeclB (TWord w ∷ rest) | no _ | no _ | no _
  with parseFunDefB w rest
... | just (d , rest' , bnd) = just (d , rest' , <-trans bnd (s≤s ≤-refl))
... | nothing = nothing
parseDeclB (TLParen ∷ rest) = tryOpDeclB (TLParen ∷ rest)
parseDeclB (TRParen ∷ _) = nothing
parseDeclB (TLBrace ∷ _) = nothing
parseDeclB (TRBrace ∷ _) = nothing
parseDeclB (TColon ∷ _) = nothing
parseDeclB (TEquals ∷ _) = nothing
parseDeclB (TArrow ∷ _) = nothing
parseDeclB (TLambda ∷ _) = nothing
parseDeclB (TComma ∷ _) = nothing
parseDeclB (TSemicolon ∷ _) = nothing
parseDeclB (TAt ∷ _) = nothing
parseDeclB (TPipe ∷ _) = nothing
parseDeclB (TDot ∷ _) = nothing
parseDeclB (TPlus ∷ _) = nothing
parseDeclB (TMinus ∷ _) = nothing
parseDeclB (TStar ∷ _) = nothing
parseDeclB (TSlash ∷ _) = nothing
parseDeclB (TPercent ∷ _) = nothing
parseDeclB (TAmpersand ∷ _) = nothing
parseDeclB (TLt ∷ _) = nothing
parseDeclB (TLe ∷ _) = nothing
parseDeclB (TGt ∷ _) = nothing
parseDeclB (TGe ∷ _) = nothing
parseDeclB (TEqEq ∷ _) = nothing
parseDeclB (TNeq ∷ _) = nothing
parseDeclB (TCaret1 ∷ _) = nothing
parseDeclB (TCaret0 ∷ _) = nothing
parseDeclB (TCaretW ∷ _) = nothing
parseDeclB (TInt _ ∷ _) = nothing
parseDeclB (TString _ ∷ _) = nothing
parseDeclB (TNewline ∷ _) = nothing
parseDeclB (TEOF ∷ _) = nothing

parseDecl : Parser Decl
parseDecl toks with parseDeclB toks
... | just (d , rest , _) = just (d , rest)
... | nothing = nothing

------------------------------------------------------------------------
-- Module Parser
------------------------------------------------------------------------

-- | Length bound for `skipNewlines`: the emitted residual is ≤ the
-- input. This is proved structurally: each step either passes through
-- unchanged (equal length) or drops a `TNewline` (strictly smaller).
skipNewlines-≤ : (toks : List Token) →
                 ∀ {ns rest} → skipNewlines toks ≡ just (ns , rest) →
                 length rest ≤ length toks
skipNewlines-≤ [] refl = ≤-refl
skipNewlines-≤ (TNewline ∷ rest) eq with skipNewlines rest | skipNewlines-≤ rest
... | just (_ , _) | rec with eq
...   | refl = ≤-trans (rec refl) (n≤1+n _)
skipNewlines-≤ (TNewline ∷ rest) eq | nothing | _ with eq
...   | refl = n≤1+n _
skipNewlines-≤ (TWord _ ∷ rest) refl = ≤-refl
skipNewlines-≤ (TLParen ∷ rest) refl = ≤-refl
skipNewlines-≤ (TRParen ∷ rest) refl = ≤-refl
skipNewlines-≤ (TLBrace ∷ rest) refl = ≤-refl
skipNewlines-≤ (TRBrace ∷ rest) refl = ≤-refl
skipNewlines-≤ (TColon ∷ rest) refl = ≤-refl
skipNewlines-≤ (TEquals ∷ rest) refl = ≤-refl
skipNewlines-≤ (TArrow ∷ rest) refl = ≤-refl
skipNewlines-≤ (TLambda ∷ rest) refl = ≤-refl
skipNewlines-≤ (TComma ∷ rest) refl = ≤-refl
skipNewlines-≤ (TSemicolon ∷ rest) refl = ≤-refl
skipNewlines-≤ (TAt ∷ rest) refl = ≤-refl
skipNewlines-≤ (TPipe ∷ rest) refl = ≤-refl
skipNewlines-≤ (TDot ∷ rest) refl = ≤-refl
skipNewlines-≤ (TPlus ∷ rest) refl = ≤-refl
skipNewlines-≤ (TMinus ∷ rest) refl = ≤-refl
skipNewlines-≤ (TStar ∷ rest) refl = ≤-refl
skipNewlines-≤ (TSlash ∷ rest) refl = ≤-refl
skipNewlines-≤ (TPercent ∷ rest) refl = ≤-refl
skipNewlines-≤ (TAmpersand ∷ rest) refl = ≤-refl
skipNewlines-≤ (TLt ∷ rest) refl = ≤-refl
skipNewlines-≤ (TLe ∷ rest) refl = ≤-refl
skipNewlines-≤ (TGt ∷ rest) refl = ≤-refl
skipNewlines-≤ (TGe ∷ rest) refl = ≤-refl
skipNewlines-≤ (TEqEq ∷ rest) refl = ≤-refl
skipNewlines-≤ (TNeq ∷ rest) refl = ≤-refl
skipNewlines-≤ (TCaret1 ∷ rest) refl = ≤-refl
skipNewlines-≤ (TCaret0 ∷ rest) refl = ≤-refl
skipNewlines-≤ (TCaretW ∷ rest) refl = ≤-refl
skipNewlines-≤ (TInt _ ∷ rest) refl = ≤-refl
skipNewlines-≤ (TString _ ∷ rest) refl = ≤-refl
skipNewlines-≤ (TEOF ∷ rest) refl = ≤-refl

-- | Well-founded parse of a list of declarations. Always succeeds,
-- returning `[]` plus the unchanged input when no declaration parses.
-- Each recursive call is on a strictly shorter residual, proved via
-- `parseDeclB`'s Σ-bound composed with `skipNewlines-≤`.
parseDeclsWF : (toks : List Token) → Acc _<_ (length toks) →
               Σ[ ds ∈ List Decl ] Σ[ rest ∈ List Token ]
                 length rest ≤ length toks
parseDeclsWF toks (acc rec) with skipNewlines toks in skipEq
... | nothing = [] , toks , ≤-refl
... | just (_ , toks') with parseDeclB toks' | skipNewlines-≤ toks skipEq
...   | nothing | skipBnd = [] , toks' , skipBnd
...   | just (d , rest , declBnd) | skipBnd
        with parseDeclsWF rest (rec (<-≤-trans declBnd skipBnd))
...     | (ds , rest' , restBnd) =
          d ∷ ds , rest' , ≤-trans restBnd (≤-trans (<⇒≤ declBnd) skipBnd)

-- | Parse all declarations (separated by newlines).
-- Termination: via well-founded recursion on token length. Each
-- successful `parseDecl` strictly shrinks the residual (`parseDeclB`'s
-- Σ-bound), while `skipNewlines` is weakly shrinking (≤). No
-- TERMINATING pragma is needed.
parseDecls : Parser (List Decl)
parseDecls toks with parseDeclsWF toks (<-wellFounded (length toks))
... | (ds , rest , _) = just (ds , rest)

-- | Parse a complete module
parseModule : Parser Module
parseModule toks with parseDecls toks
... | just (ds , rest) = just (mkModule ds , rest)
... | nothing = just (mkModule [] , toks)
