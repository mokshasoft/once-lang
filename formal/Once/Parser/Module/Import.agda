-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Parser.Module.Import
--
-- Import-declaration parser: dotted module path plus optional
-- `as Alias` suffix.
------------------------------------------------------------------------

module Once.Parser.Module.Import where

open import Relation.Nullary using (Dec)
open import Data.Bool using (Bool; true; false)
open import Once.Parser.Module.Core

-- | Drop the first token (used to recurse past a `.` separator). `dropDot-≤`
-- bounds it. CLASSIFIER-ROUTED (Plan 0.52 bridge-readiness): the head dispatch
-- goes through `dotHead` (a 1-token classifier) + `dropDot`, NOT a positional
-- `TDot ∷ _` pattern — so the adequacy bridge can step the parser for a VARIABLE
-- tail (the relation shares `dropDot tail`/`dotHead tail` symbolically; a
-- positional catch-all would not reduce). Mirrors the lexer's `headK` routing.
dropDot : List Token → List Token
dropDot []       = []
dropDot (_ ∷ xs) = xs

dropDot-≤ : (xs : List Token) → length (dropDot xs) ≤ length xs
dropDot-≤ []       = ≤-refl
dropDot-≤ (_ ∷ xs) = m≤n⇒m≤1+n ≤-refl

-- `dotHead tail ≡ true` ⇔ `tail` begins with a `.` separator (the path may
-- continue; `parseModulePath-WFB (dropDot tail)` then decides cons vs stop).
dotHead : List Token → Bool
dotHead (TDot ∷ _) = true
dotHead _          = false

-- | Parse a dotted module path via well-founded recursion. Each step consumes
-- one identifier via `anyWordB`. De-`with`'d + classifier-routed through
-- `pmp-aw`/`pmp-tail`/`pmp-dot`.
parseModulePath-WFB : (toks : List Token) → Acc _<_ (length toks) →
                      ParseAtB {List String} toks
pmp-aw : (toks : List Token) (rec : ∀ {y} → y < length toks → Acc _<_ y)
         (aw : ParseAtB {String} toks) → ParseAtB {List String} toks
pmp-tail : (toks : List Token) (rec : ∀ {y} → y < length toks → Acc _<_ y)
           (name : String) (tail : List Token) (bnd : length tail < length toks)
           (cont : Bool) → ParseAtB {List String} toks
pmp-dot : (toks : List Token) (rec : ∀ {y} → y < length toks → Acc _<_ y)
          (name : String) (tail : List Token) (bnd : length tail < length toks)
          (sub : ParseAtB {List String} (dropDot tail)) → ParseAtB {List String} toks

parseModulePath-WFB toks (acc rec) = pmp-aw toks rec (anyWordB toks)

pmp-aw toks rec nothing = nothing
pmp-aw toks rec (just (name , tail , bnd)) = pmp-tail toks rec name tail bnd (dotHead tail)

pmp-tail toks rec name tail bnd true =
  pmp-dot toks rec name tail bnd (parseModulePath-WFB (dropDot tail) (rec (≤-<-trans (dropDot-≤ tail) bnd)))
pmp-tail toks rec name tail bnd false = just (name ∷ [] , tail , bnd)

pmp-dot toks rec name tail bnd (just (path , rest' , bnd')) =
  just (name ∷ path , rest' , <-trans bnd' (≤-<-trans (dropDot-≤ tail) bnd))
pmp-dot toks rec name tail bnd nothing = just (name ∷ [] , tail , bnd)  -- unreachable when cont ≡ true

parseModulePathB : (toks : List Token) → ParseAtB {List String} toks
parseModulePathB toks = parseModulePath-WFB toks (<-wellFounded (length toks))

-- | Parse a dotted module path (plain `Parser`).
parseModulePath : Parser (List String)
parseModulePath toks with parseModulePathB toks
... | just (p , rest , _) = just (p , rest)
... | nothing = nothing

-- | Bounded variant of `as Alias`: residual ≤ input (the parser may no-op and
-- return the unchanged input). CLASSIFIER-ROUTED through `anyWordB` (head
-- dispatch) + de-`with`'d via `pia-head`/`pia-as`/`pia-w`, all typed over `toks`,
-- so the adequacy bridge steps it for a variable tail.
parseImportAliasB : List String → (toks : List Token) → ParseAtB≤ {Decl} toks
pia-head : (path : List String) (toks : List Token) (aw : ParseAtB {String} toks) → ParseAtB≤ {Decl} toks
pia-as : (path : List String) (toks : List Token) (s : String) (rest : List Token)
         (bnd : length rest < length toks) → Dec (s ≡ "as") → ParseAtB≤ {Decl} toks
pia-w  : (path : List String) (toks : List Token) (rest : List Token)
         (bnd : length rest < length toks) → ParseAtB {String} rest → ParseAtB≤ {Decl} toks

parseImportAliasB path toks = pia-head path toks (anyWordB toks)

pia-head path toks nothing                = just (DImport (mkImport path nothing) , toks , ≤-refl)
pia-head path toks (just (s , rest , bnd)) = pia-as path toks s rest bnd (s ≟ "as")

pia-as path toks s rest bnd (yes _) = pia-w path toks rest bnd (anyWordB rest)
pia-as path toks s rest bnd (no  _) = just (DImport (mkImport path nothing) , toks , ≤-refl)

pia-w path toks rest bnd (just (alias , rest' , bnd')) =
  just (DImport (mkImport path (just alias)) , rest' , <⇒≤ (<-trans bnd' bnd))
pia-w path toks rest bnd nothing = nothing

-- | Parse optional 'as Alias' after import path
parseImportAlias : List String → Parser Decl
parseImportAlias path toks with parseImportAliasB path toks
... | just (d , rest , _) = just (d , rest)
... | nothing = nothing

-- | Bounded parse of `import Module.Path [as Alias]`: consumes at least the
-- leading identifier (via parseModulePathB), so the residual is strictly shorter
-- than the input. De-`with`'d through `pib-path`/`pib-alias` for the bridge.
parseImportB : (toks : List Token) → ParseAtB {Decl} toks
pib-path : (toks : List Token) (mp : ParseAtB {List String} toks) → ParseAtB {Decl} toks
pib-alias : (toks : List Token) (path : List String) (rest : List Token)
            (bnd : length rest < length toks) (al : ParseAtB≤ {Decl} rest) → ParseAtB {Decl} toks

parseImportB toks = pib-path toks (parseModulePathB toks)

pib-path toks nothing                  = nothing
pib-path toks (just (path , rest , bnd)) = pib-alias toks path rest bnd (parseImportAliasB path rest)

pib-alias toks path rest bnd (just (d , rest' , bnd')) = just (d , rest' , ≤-<-trans bnd' bnd)
pib-alias toks path rest bnd nothing                   = nothing

-- | Parse: import Module.Path [as Alias]
parseImport : Parser Decl
parseImport toks with parseImportB toks
... | just (d , rest , _) = just (d , rest)
... | nothing = nothing
