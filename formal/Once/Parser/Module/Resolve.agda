-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Parser.Module.Resolve
--
-- AST-level import resolver.
--
-- Given a `ModuleMap` (dictionary of already-resolved modules, keyed by
-- their dotted import path) and a user's `Module`, replaces every
-- `DImport path (just alias)` in the user's decls with the primitives
-- of the imported module, tagged with owner=`alias`. A `DImport path
-- nothing` (unaliased import) inlines primitives under owner=nothing
-- (same as if the user had written them directly).
--
-- Haskell drives the I/O: it walks the user's module, recursively
-- loads + parses each imported `.once` file, topo-sorts them so
-- already-resolved modules go into the map, then calls this function
-- for the final one-level substitution. Import cycles are detected by
-- Haskell before the map is built, so this resolver doesn't need a
-- termination measure beyond structural recursion on `decls`.
--
-- Why this matters: the previous design did text-level string
-- splicing in Haskell (`primitive S.exit : ...`), outside the
-- verified pipeline. That produced source that the Agda parser
-- couldn't handle (dotted names) and silently dropped declarations.
-- Moving the substitution to the AST eliminates the entire class of
-- "inserted text doesn't round-trip through the parser" bugs.
------------------------------------------------------------------------

module Once.Parser.Module.Resolve where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; map) renaming (_++_ to _++L_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; _≟_; _++_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)

open import Once.Parser.Module.Core

------------------------------------------------------------------------
-- ModuleMap: path → resolved Module
------------------------------------------------------------------------

-- | Import path (e.g. ["I", "Foo", "Bar"]) paired with its
-- already-resolved module. Haskell builds this by topo-sorting and
-- resolving bottom-up.
ModuleMap : Set
ModuleMap = List (List String × Module)

-- | String-equality over dotted paths.
_path≟_ : List String → List String → Bool
[]         path≟ []         = true
[]         path≟ (_ ∷ _)    = false
(_ ∷ _)    path≟ []         = false
(x ∷ xs)   path≟ (y ∷ ys)   with x ≟ y
... | yes _ = xs path≟ ys
... | no  _ = false

-- | Look up a module by path. Returns `nothing` if the path isn't in
-- the map (Haskell should have pre-populated the map with every
-- transitive dependency before calling us).
lookupModule : ModuleMap → List String → Maybe Module
lookupModule []                _    = nothing
lookupModule ((p , m) ∷ rest)  path with p path≟ path
... | true  = just m
... | false = lookupModule rest path

------------------------------------------------------------------------
-- Primitive extraction with owner tagging
------------------------------------------------------------------------

-- | Pull out just the DSignature decls from a module, retagging each
-- with the given owner alias. Non-primitive decls are dropped — they
-- belong to the imported module's own scope, not the importer's.
signaturesWithOwner : Maybe String → List Decl → List Decl
signaturesWithOwner _     []                                   = []
signaturesWithOwner owner (DSignature name _ ty eff ∷ rest)   =
  DSignature name owner ty eff ∷ signaturesWithOwner owner rest
signaturesWithOwner owner (_ ∷ rest)                           =
  signaturesWithOwner owner rest

------------------------------------------------------------------------
-- resolveImports
------------------------------------------------------------------------

-- | For each DImport in `ds`, substitute the imported module's
-- primitives (owner-tagged by the import's alias). Drop the DImport
-- itself. All non-import decls pass through unchanged.
--
-- Returns `inj₁ err` only if a referenced module path is missing from
-- the map — a Haskell-layer bug, since the map should contain every
-- transitive dependency.
resolveDecls : ModuleMap → List Decl → String ⊎ List Decl
resolveDecls _      []                             = inj₂ []
resolveDecls modMap (DImport imp ∷ rest) with lookupModule modMap (Import.path imp)
... | nothing =
        inj₁ ("Internal error: import path not in ModuleMap: " ++ showPath (Import.path imp))
  where
    showPath : List String → String
    showPath []          = ""
    showPath (x ∷ [])    = x
    showPath (x ∷ xs)    = x ++ "." ++ showPath xs
... | just (mkModule impDs) with resolveDecls modMap rest
...   | inj₁ err = inj₁ err
...   | inj₂ tailDs =
        inj₂ (signaturesWithOwner (Import.alias imp) impDs ++L tailDs)
resolveDecls modMap (d ∷ rest) with resolveDecls modMap rest
... | inj₁ err = inj₁ err
... | inj₂ tailDs = inj₂ (d ∷ tailDs)

-- | Public entry. Haskell populates the map, calls this, and feeds
-- the resolved module to `compileResolved`.
resolveImports : ModuleMap → Module → String ⊎ Module
resolveImports modMap (mkModule ds) with resolveDecls modMap ds
... | inj₁ err   = inj₁ err
... | inj₂ ds'   = inj₂ (mkModule ds')
