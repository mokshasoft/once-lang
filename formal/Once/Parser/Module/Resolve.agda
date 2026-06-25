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
open import Once.CanonicalName using (CanonicalName; canonical)
open import Once.TypeCheck.Raw
  using (RawExpr; RVar; RQualified; RResolved; RApp; RLam; RLet; RPair;
         RDestruct; RUnit; RInt; RStringLit; RAnnot; RBinOp; RUnaryOp; RAna)

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

-- | Dotted rendering of an import path — `["Cars","All"] ↦ "Cars.All"`.
-- The canonical key joins this with the name (`Cars.All.exit`), which
-- equals `showCanonical (canonical (path ++ [name]))`.
showPath : List String → String
showPath []          = ""
showPath (x ∷ [])    = x
showPath (x ∷ xs)    = x ++ "." ++ showPath xs

------------------------------------------------------------------------
-- Canonical resolution (Plan 0.50)
--
-- A qualified ref `name@alias` is unstable: the same import can be
-- aliased `A`, `All`, or `Cars.All`. Resolution rewrites it to its
-- RESOLVED canonical identity `RResolved (canonical (path ++ [name]))`,
-- where `path` is the import's full module path. The owner-tag of the
-- inlined signatures is retagged to the SAME dotted path, so the import
-- table key (`owner.name`) coincides with `showCanonical cn` — the
-- typechecker's `t-var-resolved` lookup hits it by construction.
------------------------------------------------------------------------

-- | alias → full module path, collected from the user's `DImport`s.
-- Unaliased imports contribute nothing (their refs stay bare `RVar` —
-- the milestone-1 / `m-named` case).
AliasMap : Set
AliasMap = List (String × List String)

collectAliases : List Decl → AliasMap
collectAliases []                                            = []
collectAliases (DImport (mkImport path (just alias)) ∷ rest) =
  (alias , path) ∷ collectAliases rest
collectAliases (_ ∷ rest)                                    = collectAliases rest

lookupImportAlias : AliasMap → String → Maybe (List String)
lookupImportAlias []              _ = nothing
lookupImportAlias ((a , p) ∷ rest) x with a ≟ x
... | yes _ = just p
... | no  _ = lookupImportAlias rest x

-- | Rewrite every `RQualified name alias` whose alias resolves to a
-- canonical `RResolved (canonical (path ++ [name]))`. An unresolved
-- alias is left untouched (the typechecker rejects it as unbound).
-- All other nodes recurse structurally.
canonExpr : AliasMap → RawExpr → RawExpr
canonExpr am (RQualified name alias) with lookupImportAlias am alias
... | just path = RResolved (canonical (path ++L (name ∷ [])))
... | nothing   = RQualified name alias
canonExpr am (RVar x)            = RVar x
canonExpr am (RResolved cn)      = RResolved cn
canonExpr am (RApp f x)          = RApp (canonExpr am f) (canonExpr am x)
canonExpr am (RLam x b)          = RLam x (canonExpr am b)
canonExpr am (RLet x e₁ e₂)      = RLet x (canonExpr am e₁) (canonExpr am e₂)
canonExpr am (RPair a b)         = RPair (canonExpr am a) (canonExpr am b)
canonExpr am (RDestruct s xl el xr er) =
  RDestruct (canonExpr am s) xl (canonExpr am el) xr (canonExpr am er)
canonExpr am RUnit               = RUnit
canonExpr am (RInt n)            = RInt n
canonExpr am (RStringLit s)      = RStringLit s
canonExpr am (RAnnot e t)        = RAnnot (canonExpr am e) t
canonExpr am (RBinOp op a b)     = RBinOp op (canonExpr am a) (canonExpr am b)
canonExpr am (RUnaryOp op e)     = RUnaryOp op (canonExpr am e)
canonExpr am (RAna F c)          = RAna F (canonExpr am c)

-- | Apply `canonExpr` to a decl's function body; everything else is
-- untouched (signatures/imports/type-aliases carry no expression refs).
canonDecl : AliasMap → Decl → Decl
canonDecl am (DFunDef name alloc body) = DFunDef name alloc (canonExpr am body)
canonDecl am d                         = d

------------------------------------------------------------------------
-- Primitive extraction with owner tagging
------------------------------------------------------------------------

-- | Pull out just the DSignature decls from a module, retagging each
-- with the given owner. Non-primitive decls are dropped — they
-- belong to the imported module's own scope, not the importer's.
signaturesWithOwner : Maybe String → List Decl → List Decl
signaturesWithOwner _     []                                   = []
signaturesWithOwner owner (DSignature name _ ty eff ∷ rest)   =
  DSignature name owner ty eff ∷ signaturesWithOwner owner rest
signaturesWithOwner owner (_ ∷ rest)                           =
  signaturesWithOwner owner rest

-- | Owner tag for an import's inlined signatures. An ALIASED import is
-- keyed by its full dotted path (matching the resolved canonical names);
-- an UNALIASED import stays `nothing` (bare, milestone-1).
ownerOf : Import → Maybe String
ownerOf (mkImport path (just _)) = just (showPath path)
ownerOf (mkImport _    nothing)  = nothing

------------------------------------------------------------------------
-- resolveImports
------------------------------------------------------------------------

-- | For each DImport in `ds`, substitute the imported module's
-- primitives (owner-tagged by the import's canonical path). Drop the
-- DImport itself. Non-import decls pass through, with `RQualified`
-- refs in function bodies rewritten to `RResolved` via `am`.
--
-- Returns `inj₁ err` only if a referenced module path is missing from
-- the map — a Haskell-layer bug, since the map should contain every
-- transitive dependency.
resolveDecls : AliasMap → ModuleMap → List Decl → String ⊎ List Decl
resolveDecls _  _      []                             = inj₂ []
resolveDecls am modMap (DImport imp ∷ rest) with lookupModule modMap (Import.path imp)
... | nothing =
        inj₁ ("Internal error: import path not in ModuleMap: " ++ showPath (Import.path imp))
... | just (mkModule impDs) with resolveDecls am modMap rest
...   | inj₁ err = inj₁ err
...   | inj₂ tailDs =
        inj₂ (signaturesWithOwner (ownerOf imp) impDs ++L tailDs)
resolveDecls am modMap (d ∷ rest) with resolveDecls am modMap rest
... | inj₁ err = inj₁ err
... | inj₂ tailDs = inj₂ (canonDecl am d ∷ tailDs)

-- | Public entry. Haskell populates the map, calls this, and feeds
-- the resolved module to `compileResolved`.
resolveImports : ModuleMap → Module → String ⊎ Module
resolveImports modMap (mkModule ds) with resolveDecls (collectAliases ds) modMap ds
... | inj₁ err   = inj₁ err
... | inj₂ ds'   = inj₂ (mkModule ds')
