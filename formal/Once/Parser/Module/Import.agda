-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Parser.Module.Import
--
-- Import-declaration parser: dotted module path plus optional
-- `as Alias` suffix.
------------------------------------------------------------------------

module Once.Parser.Module.Import where

open import Relation.Nullary using (Dec)
open import Once.Parser.Module.Core

-- | Parse a dotted module path via well-founded recursion. Each step
-- consumes one identifier via `anyWordB`. De-`with`'d through `pmp-aw`/`pmp-dot`
-- (the `anyWordB` and recursion results are PARAMETERS) so the adequacy bridge
-- (`Once.Adequacy.DeclBridge`) can case them without an internal-`with` clash.
parseModulePath-WFB : (toks : List Token) → Acc _<_ (length toks) →
                      ParseAtB {List String} toks
pmp-aw : (toks : List Token) (rec : ∀ {y} → y < length toks → Acc _<_ y)
         (aw : ParseAtB {String} toks) → anyWordB toks ≡ aw → ParseAtB {List String} toks
pmp-dot : (toks : List Token) (rec : ∀ {y} → y < length toks → Acc _<_ y)
          (name : String) (rest : List Token) (bnd : length (TDot ∷ rest) < length toks)
          (sub : ParseAtB {List String} rest) → ParseAtB {List String} toks

parseModulePath-WFB toks (acc rec) = pmp-aw toks rec (anyWordB toks) refl

pmp-aw toks rec nothing eq = nothing
pmp-aw toks rec (just (name , TDot ∷ rest , bnd)) eq =
  pmp-dot toks rec name rest bnd (parseModulePath-WFB rest (rec (<-trans (s≤s ≤-refl) bnd)))
pmp-aw toks rec (just (name , rest , bnd)) eq = just (name ∷ [] , rest , bnd)

pmp-dot toks rec name rest bnd (just (path , rest' , bnd')) =
  just (name ∷ path , rest' , <-trans bnd' (<-trans (s≤s ≤-refl) bnd))
pmp-dot toks rec name rest bnd nothing = just (name ∷ [] , (TDot ∷ rest) , bnd)

parseModulePathB : (toks : List Token) → ParseAtB {List String} toks
parseModulePathB toks = parseModulePath-WFB toks (<-wellFounded (length toks))

-- | Parse a dotted module path (plain `Parser`).
parseModulePath : Parser (List String)
parseModulePath toks with parseModulePathB toks
... | just (p , rest , _) = just (p , rest)
... | nothing = nothing

-- | Bounded variant of `as Alias`: residual ≤ input (the parser may
-- no-op and return the unchanged input). De-`with`'d through `pia-as`/`pia-w`.
parseImportAliasB : List String → (toks : List Token) → ParseAtB≤ {Decl} toks
pia-as : (path : List String) (s : String) (rest : List Token) → Dec (s ≡ "as") →
         ParseAtB≤ {Decl} (TWord s ∷ rest)
pia-w  : (path : List String) (s : String) (rest : List Token) → ParseAtB {String} rest →
         ParseAtB≤ {Decl} (TWord s ∷ rest)

parseImportAliasB path (TWord s ∷ rest) = pia-as path s rest (s ≟ "as")
parseImportAliasB path toks =
      just (DImport (mkImport path nothing) , toks , ≤-refl)

pia-as path s rest (yes _) = pia-w path s rest (anyWordB rest)
pia-as path s rest (no  _) = just (DImport (mkImport path nothing) , TWord s ∷ rest , ≤-refl)

pia-w path s rest (just (alias , rest' , bnd)) =
  just (DImport (mkImport path (just alias)) , rest' , <⇒≤ (<-trans bnd (s≤s ≤-refl)))
pia-w path s rest nothing = nothing

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
