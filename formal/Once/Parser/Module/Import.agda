-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Parser.Module.Import
--
-- Import-declaration parser: dotted module path plus optional
-- `as Alias` suffix.
------------------------------------------------------------------------

module Once.Parser.Module.Import where

open import Once.Parser.Module.Core

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
parseImportAliasB path (TWord s ∷ rest) with s ≟ "as"
... | yes _ with anyWordB rest
...   | just (alias , rest' , bnd) =
        just (DImport (mkImport path (just alias)) , rest' ,
              <⇒≤ (<-trans bnd (s≤s ≤-refl)))
...   | nothing = nothing
parseImportAliasB path (TWord s ∷ rest) | no _ =
      just (DImport (mkImport path nothing) , TWord s ∷ rest , ≤-refl)
parseImportAliasB path toks =
      just (DImport (mkImport path nothing) , toks , ≤-refl)

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
