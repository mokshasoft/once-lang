-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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

open import Data.Bool using (Bool; true; false; not; T)
open import Data.List using (List; []; _∷_; map) renaming (_++_ to _++L_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; _≟_; _++_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no; ¬_; does)
open import Data.List.Membership.DecPropositional _≟_ using (_∈?_)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse; isYes)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import Once.Parser.Module.Core
open import Once.Internal.Syntax using (RLam; RawExpr)
open import Once.Internal.ResolvedRefs using (GoodRefs; goodRefs?)
open import Once.Internal.Type.Poly using (extractGround)
open import Once.Type using (isGround)
open import Once.Functor.Decide using (isConcrete?)
-- D072 M3: the oracle's sig-less schema criterion (shared with Parser).
open import Once.Spec.Name using (canonical; gen; GenWord)
open import Once.CanonicalName using (genWord?)
open import Once.Internal.Syntax using (RVar; RQualified; RResolved; RApp; RLet; RPair; RDestruct; RUnit; RInt; RFloat; RAnnot; RBinOp; RUnaryOp; RAna; ClosedLiftShape; cls-var; cls-qual; cls-res; cls-let; cls-destr; cls-unit; cls-annot; cls-binop)

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
{-# CATCHALL #-}
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
{-# CATCHALL #-}
collectAliases (_ ∷ rest)                                    = collectAliases rest

lookupImportAlias : AliasMap → String → Maybe (List String)
lookupImportAlias []              _ = nothing
lookupImportAlias ((a , p) ∷ rest) x with a ≟ x
... | yes _ = just p
... | no  _ = lookupImportAlias rest x

-- | name → owning module path, for UNALIASED imports (`DImport path nothing`).
-- A bare reference to such a name resolves to the FULL path (clash-freedom):
-- two unaliased modules both exporting `foo`, or own `foo` vs unaliased `foo`,
-- get distinct canonical names. (Syscalls/primitives are ALIASED — `import … as
-- S`, `exit@S` — so they take the `RQualified` path and never appear here.)
UnaliasedMap : Set
UnaliasedMap = List (String × List String)

-- | The names a (resolved) module exports = its `DSignature` names (the same
-- primitives `signaturesWithOwner` inlines).
sigNames : List Decl → List String
sigNames []                          = []
sigNames (DSignature name _ _ ∷ r) = name ∷ sigNames r
{-# CATCHALL #-}
sigNames (_ ∷ r)                     = sigNames r

collectUnaliased : ModuleMap → List Decl → UnaliasedMap
collectUnaliased _      []                                       = []
collectUnaliased modMap (DImport (mkImport path nothing) ∷ rest) with lookupModule modMap path
... | just (mkModule impDs) = map (λ n → (n , path)) (sigNames impDs) ++L collectUnaliased modMap rest
... | nothing               = collectUnaliased modMap rest
{-# CATCHALL #-}
collectUnaliased modMap (_ ∷ rest)                              = collectUnaliased modMap rest

lookupUnaliased : UnaliasedMap → String → Maybe (List String)
lookupUnaliased []              _ = nothing
lookupUnaliased ((n , p) ∷ rest) x with x ≟ n
... | yes _ = just p
... | no  _ = lookupUnaliased rest x

-- | Names the elaborator special-cases on a bare `RVar` (point-free CCC
-- builtins + recursion schemes). These MUST stay `RVar` so the dedicated
-- typing rules fire — never canonicalize them to `RResolved`. Mirrors
-- `Elaborate.isPolyBuiltin` (+ `cata`/`ana`/`In`/`Out`); kept local to avoid a
-- Parser→TypeCheck import.
-- D134/D136: ONE definition. The RESERVED WORDS are the language-level
-- property `GenWord` (Once.CanonicalName); this is its boolean form, so the
-- resolver's decision and the typing rule's premise cannot drift apart.
isBuiltinName : String → Bool
isBuiltinName x = isYes (genWord? x)

-- The two bridges the canon proofs need: preservation refutes the generator
-- branch from the rule's `¬ GenWord x`, reflection supplies that premise from
-- the resolver's `false`.
isBuiltinName-sound : ∀ (x : String) → isBuiltinName x ≡ true → GenWord x
isBuiltinName-sound x eq = toWitness (subst T (sym eq) tt)

isBuiltinName-false : ∀ (x : String) → isBuiltinName x ≡ false → ¬ GenWord x
isBuiltinName-false x eq = toWitnessFalse (subst (λ b → T (not b)) (sym eq) tt)

¬GenWord-isBuiltinName : ∀ (x : String) → ¬ GenWord x → isBuiltinName x ≡ false
¬GenWord-isBuiltinName x ¬gw with genWord? x
... | yes gw = ⊥-elim (¬gw gw)
... | no  _  = refl

-- | Plan 0.50 (D064): a bare `RVar x` that is NOT a local binder and NOT a
-- builtin is a reference to a top-level definition (own-module or unaliased
-- import) — a MORPHISM. Resolve it to `RResolved (canonical [x])` so it takes
-- the `t-var-resolved` path (→ `lift-morphism` at arrow type) instead of
-- `t-var-import` (→ `sigOp` → closure). The import table keys own/unaliased
-- defs by their bare name, so `showCanonical (canonical [x]) = x` hits it.
-- (Full dotted path = clash-freedom, a separable refinement.)
-- A free (non-local, non-builtin) bare `RVar x`: an UNALIASED-import ref
-- (`just path`) resolves to the FULL path `canonical (path ++ [x])`; an
-- own-module ref (`nothing`) stays the single-component `canonical [x]` (the
-- own module has no path and its names are unique within it). Both take the
-- `t-var-resolved` → `lift-morphism` path (a MORPHISM, D064), and both are
-- clash-free: own `[x]` (length 1) vs import `[path…, x]` (length ≥ 2).
-- | The `I` import-path prefix is a SHORTHAND for the `Interpretations`
-- directory (mirrors the CLI's `I → Interpretations` disk rule, `Once.CLI`).
-- The CANONICAL name — and thus the `once-symbol-path` symbol — must use the
-- FULL resolved form, never the shorthand. So `canon` expands a leading `I` to
-- `Interpretations` when building a `CanonicalName`. (Module-map lookups keep
-- the ORIGINAL written path; only the identity/symbol uses the full form.)
expandPath : List String → List String
expandPath []         = []
expandPath (c ∷ rest) with c ≟ "I"
... | yes _ = "Interpretations" ∷ rest
... | no  _ = c ∷ rest

-- | D136: resolving a bare name is a THREE-way decision, so this takes the two
-- decisions rather than their disjunction. A lexical binder shadows; otherwise
-- a GENERATOR name is the generator, whatever else is in scope; and only a
-- non-generator falls through to import / own-module resolution. A definition
-- whose name a generator has taken is reached as `name@this`.
-- The own module's definitions come last, after generators and imports (the
-- Spec's order, `rn-gen`/`rn-import`/`rn-own`), polymorphic or not (R11, D330).
canonVar : Bool → Bool → Maybe (List String) → String → RawExpr
canonVar true  _     _           x = RVar x                                             -- lexical binder shadows
canonVar false true  _           x = RResolved (gen x)                                  -- a GENERATOR
canonVar false false (just path) x = RResolved (canonical (expandPath path ++L (x ∷ []))) -- unaliased import: full path
canonVar false false nothing     x = RResolved (canonical (x ∷ []))                     -- own-module ref

-- | Rewrite `RQualified` (via alias map) and bare top-level `RVar` refs to
-- `RResolved`; recurse structurally, threading the bound-variable set `bound`
-- (lambda/let/destruct binders) so LOCALS are never canonicalized. `um`
-- carries unaliased-import name→path for full-path resolution.
canonExpr : List String → UnaliasedMap → AliasMap → RawExpr → RawExpr
-- D136: `name@this` reaches the OWN module — the escape hatch for a definition
-- whose name a generator has taken. `this` is a RESERVED alias and is decided
-- BEFORE the alias table, so an `import … as this` cannot capture it.
canonExpr bound um am (RQualified name alias) with alias ≟ "this"
... | yes _ = RResolved (canonical (name ∷ []))
... | no  _ with lookupImportAlias am alias
...   | just path = RResolved (canonical (expandPath path ++L (name ∷ [])))
...   | nothing   = RResolved (canonical (alias ∷ name ∷ []))   -- an unknown alias is a path of one component
canonExpr bound um am (RVar x)            = canonVar (does (x ∈? bound)) (isBuiltinName x) (lookupUnaliased um x) x
canonExpr bound um am (RResolved cn)      = RResolved cn
canonExpr bound um am (RApp f x)          = RApp (canonExpr bound um am f) (canonExpr bound um am x)
canonExpr bound um am (RLam x b)          = RLam x (canonExpr (x ∷ bound) um am b)
canonExpr bound um am (RLet x e₁ e₂)      = RLet x (canonExpr bound um am e₁) (canonExpr (x ∷ bound) um am e₂)
canonExpr bound um am (RPair a b)         = RPair (canonExpr bound um am a) (canonExpr bound um am b)
canonExpr bound um am (RDestruct s xl el xr er) =
  RDestruct (canonExpr bound um am s) xl (canonExpr (xl ∷ bound) um am el) xr (canonExpr (xr ∷ bound) um am er)
canonExpr bound um am RUnit               = RUnit
canonExpr bound um am (RInt n)            = RInt n
canonExpr bound um am (RFloat i f l p)    = RFloat i f l p
canonExpr bound um am (RAnnot e t)        = RAnnot (canonExpr bound um am e) t
canonExpr bound um am (RBinOp op a b)     = RBinOp op (canonExpr bound um am a) (canonExpr bound um am b)
canonExpr bound um am (RUnaryOp op e)     = RUnaryOp op (canonExpr bound um am e)
canonExpr bound um am (RAna F c)          = RAna F (canonExpr bound um am c)

-- | D126: resolution PRESERVES the closed-lift side condition. It has to —
-- otherwise a derivation using the lift would not survive `canonExpr`. The two
-- shape-CHANGING cases are the interesting ones, and both land back in the set:
-- a bare `RVar` becomes `RResolved` (or stays), and `RQualified` always
-- becomes `RResolved`.
cls-canon : ∀ (bound : List String) (um : UnaliasedMap) (am : AliasMap)
              {e : RawExpr}
          → ClosedLiftShape e → ClosedLiftShape (canonExpr bound um am e)
cls-canon bound um am (cls-var {x = x})
  with does (x ∈? bound) | isBuiltinName x | lookupUnaliased um x
... | true  | _     | _       = cls-var
... | false | true  | _       = cls-res
... | false | false | just _  = cls-res
... | false | false | nothing = cls-res
cls-canon bound um am (cls-qual {a = alias}) with alias ≟ "this"
... | yes _ = cls-res
... | no  _ with lookupImportAlias am alias
...   | just _  = cls-res
...   | nothing = cls-res
cls-canon bound um am cls-res   = cls-res
cls-canon bound um am cls-let   = cls-let
cls-canon bound um am cls-destr = cls-destr
cls-canon bound um am cls-unit  = cls-unit
cls-canon bound um am cls-annot = cls-annot
cls-canon bound um am cls-binop = cls-binop

-- | …and REFLECTS it: `canonExpr` never turns a check-directed shape into a
-- liftable one, so the seven non-liftable shapes are absurd on the left.
cls-reflect : ∀ (bound : List String) (um : UnaliasedMap) (am : AliasMap)
                (e : RawExpr)
            → ClosedLiftShape (canonExpr bound um am e) → ClosedLiftShape e
cls-reflect bound um am (RVar _) _              = cls-var
cls-reflect bound um am (RQualified _ _) _      = cls-qual
cls-reflect bound um am (RResolved _) _         = cls-res
cls-reflect bound um am (RLet _ _ _) _          = cls-let
cls-reflect bound um am (RDestruct _ _ _ _ _) _ = cls-destr
cls-reflect bound um am RUnit _                 = cls-unit
cls-reflect bound um am (RAnnot _ _) _          = cls-annot
cls-reflect bound um am (RBinOp _ _ _) _        = cls-binop
cls-reflect bound um am (RApp _ _) ()
cls-reflect bound um am (RLam _ _) ()
cls-reflect bound um am (RPair _ _) ()
cls-reflect bound um am (RInt _) ()
cls-reflect bound um am (RFloat _ _ _ _) ()
cls-reflect bound um am (RUnaryOp _ _) ()
cls-reflect bound um am (RAna _ _) ()

-- | Apply `canonExpr` to a decl's function body; everything else is untouched
-- (signatures/imports/type-aliases carry no expression refs).
canonDecl : UnaliasedMap → AliasMap → Decl → Decl
canonDecl um am (DFunDef name body) = DFunDef name (canonExpr [] um am body)
{-# CATCHALL #-}
canonDecl um am d                   = d

------------------------------------------------------------------------
-- Primitive extraction with owner tagging
------------------------------------------------------------------------

-- | Pull out just the DSignature decls from a module, retagging each
-- with the given owner. Non-primitive decls are dropped — they
-- belong to the imported module's own scope, not the importer's.
signaturesWithOwner : Maybe (List String) → List Decl → List Decl
signaturesWithOwner _     []                                   = []
signaturesWithOwner owner (DSignature name _ ty ∷ rest)   =
  DSignature name owner ty ∷ signaturesWithOwner owner rest
{-# CATCHALL #-}
signaturesWithOwner owner (_ ∷ rest)                           =
  signaturesWithOwner owner rest

-- | Owner tag for an import's inlined signatures. An ALIASED import is
-- keyed by its full dotted path (matching the resolved canonical names);
-- an UNALIASED import stays `nothing` (bare, milestone-1).
-- Plan 0.50 (clash-freedom): BOTH aliased and unaliased imports key their
-- inlined signatures by the FULL dotted path, matching the canonical names
-- `canon` produces (`RQualified`/`RVar` → `RResolved (canonical (path++[name]))`).
-- So the import-table key = `showCanonical cn` by construction, and distinct
-- imported modules' same-named primitives get distinct symbols.
ownerOf : Import → Maybe (List String)
ownerOf (mkImport path (just _)) = just (expandPath path)
ownerOf (mkImport path nothing)  = just (expandPath path)

------------------------------------------------------------------------
-- resolveImports
------------------------------------------------------------------------

-- | For each DImport in `ds`, add the imported module's primitives
-- (owner-tagged by the import's canonical path) after it. The DImport
-- itself STAYS where it was written (R10, plan 0.121): a type signature
-- separated from its definition by an import is still separated, as the
-- Spec's walk reads it. Non-import decls pass through, with `RQualified`
-- refs in function bodies rewritten to `RResolved` via `am`.
--
-- Returns `inj₁ err` only if a referenced module path is missing from
-- the map — a Haskell-layer bug, since the map should contain every
-- transitive dependency.
-- DE-WITHED (plan 0.81). Both decisions — the module-table lookup and the
-- recursive call — are explicit PARAMETERS with their equations, instead of
-- `with` scrutinees. A `with` here is opaque to any proof whose hypothesis is
-- `resolveDecls … ≡ inj₂ ds'`: that type does not mention either scrutinee, so
-- nothing abstracts it and no `rewrite` fires. Same reason `inferElabV`'s
-- lookups were de-withed for Completeness.
resolveDecls : UnaliasedMap → AliasMap → ModuleMap → List Decl → String ⊎ List Decl
resolveDecls-import-aux :
  ∀ (um : UnaliasedMap) (am : AliasMap) (mm : ModuleMap)
    (imp : Import) (rest : List Decl)
  → (lm : Maybe Module) → lookupModule mm (Import.path imp) ≡ lm
  → (rr : String ⊎ List Decl) → resolveDecls um am mm rest ≡ rr
  → String ⊎ List Decl
consDecl : Decl → List Decl → String ⊎ List Decl
consDecl-at : (name : String) (body : RawExpr) → Dec (GoodRefs body) → List Decl → String ⊎ List Decl
resolveDecls-cons-aux :
  ∀ (um : UnaliasedMap) (am : AliasMap) (d : Decl)
  → (rr : String ⊎ List Decl) → String ⊎ List Decl

resolveDecls _  _  _      []                   = inj₂ []
resolveDecls um am modMap (DImport imp ∷ rest) =
  resolveDecls-import-aux um am modMap imp rest
    (lookupModule modMap (Import.path imp)) refl
    (resolveDecls um am modMap rest) refl
{-# CATCHALL #-}
resolveDecls um am modMap (d ∷ rest) =
  resolveDecls-cons-aux um am d (resolveDecls um am modMap rest)

resolveDecls-import-aux um am mm imp rest nothing _ _ _ =
  inj₁ ("Internal error: import path not in ModuleMap: " ++ showPath (Import.path imp))
resolveDecls-import-aux um am mm imp rest (just (mkModule impDs)) _ (inj₁ err) _ =
  inj₁ err
resolveDecls-import-aux um am mm imp rest (just (mkModule impDs)) _ (inj₂ tailDs) _ =
  inj₂ (DImport imp ∷ signaturesWithOwner (ownerOf imp) impDs ++L tailDs)

resolveDecls-cons-aux um am d (inj₁ err)    = inj₁ err
resolveDecls-cons-aux um am d (inj₂ tailDs) = consDecl (canonDecl um am d) tailDs

-- R11 (plan 0.121): a resolved definition does not name the entry `main`
-- (`ResolvedRefs`); the Spec's resolution never does (D324).
consDecl (DFunDef name body) tl = consDecl-at name body (goodRefs? body) tl
{-# CATCHALL #-}
consDecl d tl = inj₂ (d ∷ tl)

consDecl-at name body (yes _) tl = inj₂ (DFunDef name body ∷ tl)
consDecl-at name body (no _)  tl =
  inj₁ ("`" ++ name ++ "` refers to `main`, which no definition can refer to")

-- | Public entry. Haskell populates the map, calls this, and feeds
-- the resolved module to `compileResolved`.
resolveImports : ModuleMap → Module → String ⊎ Module
resolveImports modMap (mkModule ds)
  with resolveDecls (collectUnaliased modMap ds) (collectAliases ds) modMap ds
... | inj₁ err   = inj₁ err
... | inj₂ ds'   = inj₂ (mkModule ds')
