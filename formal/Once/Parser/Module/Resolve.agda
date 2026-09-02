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

open import Data.Bool using (Bool; true; false; _∨_; not; T)
open import Data.List using (List; []; _∷_; map) renaming (_++_ to _++L_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; _≟_; _++_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse; isYes)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import Once.Parser.Module.Core
open import Once.Type using (isGround; extractGround)
open import Once.Functor.Decide using (isConcrete?)
-- D072 M3: the oracle's sig-less schema criterion (shared with Parser).
open import Once.TypeCheck.Principal using (siglessSchema)
open import Once.CanonicalName using (CanonicalName; canonical; gen; GenWord; genWord?)
open import Once.TypeCheck.Raw
  using (RawExpr; RVar; RQualified; RResolved; RApp; RLam; RLet; RPair;
         RDestruct; RUnit; RInt; RFloat; RStringLit; RAnnot; RBinOp; RUnaryOp; RAna;
         ClosedLiftShape; cls-var; cls-qual; cls-res; cls-let; cls-destr;
         cls-unit; cls-str; cls-annot; cls-binop)

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
sigNames (DSignature name _ _ _ ∷ r) = name ∷ sigNames r
sigNames (_ ∷ r)                     = sigNames r

collectUnaliased : ModuleMap → List Decl → UnaliasedMap
collectUnaliased _      []                                       = []
collectUnaliased modMap (DImport (mkImport path nothing) ∷ rest) with lookupModule modMap path
... | just (mkModule impDs) = map (λ n → (n , path)) (sigNames impDs) ++L collectUnaliased modMap rest
... | nothing               = collectUnaliased modMap rest
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

elemStr : String → List String → Bool
elemStr _ []       = false
elemStr x (y ∷ ys) with x ≟ y
... | yes _ = true
... | no  _ = elemStr x ys

-- | Names of own-module POLYMORPHIC definitions — a `DTypeSig name ty` whose
-- `ty` is NON-ground (`isGround ty ≡ inj₂`), mirroring `extractFunctions`'
-- ground/poly split (Once.Parser): a non-ground sig routes its `DFunDef` into a
-- `PolyFunInfo`, i.e. the `polys` context, NOT the import table. Such a def is
-- INLINED at use sites by `t-var-poly-instantiate` (which fires only on a bare
-- `RVar`), so it has no monomorphic symbol to resolve to. Canonicalizing it to
-- `RResolved` would make the elaborator look it up in `imports` (where it is
-- absent) → "unbound/unspecialized". So these names must stay bare `RVar` — they
-- are threaded into `canonExpr`'s initial `bound`, kept by the SAME dispatch as
-- local binders. See tests/poly-bare-ref.once.
-- D072 M3: `polyDefNames` now threads the same pending-signature state
-- as `extractFunctions-go` so it can recognize SIG-LESS defs and apply
-- the oracle's `siglessSchema` criterion to them — the keep-bare set
-- and the FunInfo/PolyFunInfo routing must agree exactly.
pdn-go : List Decl → Maybe String → List String
pdn-go [] _ = []
-- Plan 0.58 / D071: keep a def BARE (→ the poly telescope, δ-reduced to its
-- body) unless it is ground AND concrete. A ground-but-non-concrete def (a cata
-- at `μNat → Int`, …) is a context projection, not an FFI symbol, so it must
-- NOT be canonicalized to `RResolved` (which would hit the concreteness gate).
-- Uses the SAME nested `isGround`/`isConcrete?` split as `extractFunctions-go`.
pdn-go (DTypeSig name ty ∷ rest) _       with isGround ty
... | inj₂ _ = name ∷ pdn-go rest (just name)          -- non-ground → keep bare
... | inj₁ g with isConcrete? (extractGround ty g)
...   | just _  = pdn-go rest (just name)               -- ground + concrete → mono (resolved as usual)
...   | nothing = name ∷ pdn-go rest (just name)        -- ground + non-concrete → keep bare
-- A DFunDef consumes (or drops, on name mismatch) the pending sig —
-- mirroring `extractFunctions-go`. Sig-less + schema-shaped body
-- (D072): keep bare (it routes to PolyFunInfo).
pdn-go (DFunDef name alloc body ∷ rest) (just _) = pdn-go rest nothing
pdn-go (DFunDef name alloc body ∷ rest) nothing with siglessSchema body
... | just _  = name ∷ pdn-go rest nothing
... | nothing = pdn-go rest nothing
-- A DSignature resets the pending (mirror of `extractFunctions-go`).
pdn-go (DSignature name owner ty se ∷ rest) _ = pdn-go rest nothing
pdn-go (_ ∷ rest) pending                = pdn-go rest pending

polyDefNames : List Decl → List String
polyDefNames ds = pdn-go ds nothing

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
canonVar : Bool → Bool → Maybe (List String) → String → RawExpr
canonVar true  _     _           x = RVar x                                             -- lexical binder shadows
canonVar false true  _           x = RResolved (gen x)                                  -- a GENERATOR
canonVar false false (just path) x = RResolved (canonical (expandPath path ++L (x ∷ []))) -- unaliased import: full path
canonVar false false nothing     x = RResolved (canonical (x ∷ []))                     -- own-module ref

-- | Rewrite `RQualified` (via alias map) and bare top-level `RVar` refs to
-- `RResolved`; recurse structurally, threading the bound-variable set `bound`
-- (lambda/let/destruct binders) so LOCALS are never canonicalized. `um` carries
-- unaliased-import name→path for full-path resolution.
canonExpr : List String → UnaliasedMap → AliasMap → RawExpr → RawExpr
canonExpr bound um am (RQualified name alias) with lookupImportAlias am alias
... | just path = RResolved (canonical (expandPath path ++L (name ∷ [])))
... | nothing   = RQualified name alias
canonExpr bound um am (RVar x)            = canonVar (elemStr x bound) (isBuiltinName x) (lookupUnaliased um x) x
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
canonExpr bound um am (RStringLit s)      = RStringLit s
canonExpr bound um am (RAnnot e t)        = RAnnot (canonExpr bound um am e) t
canonExpr bound um am (RBinOp op a b)     = RBinOp op (canonExpr bound um am a) (canonExpr bound um am b)
canonExpr bound um am (RUnaryOp op e)     = RUnaryOp op (canonExpr bound um am e)
canonExpr bound um am (RAna F c)          = RAna F (canonExpr bound um am c)

-- | D126: resolution PRESERVES the closed-lift side condition. It has to —
-- otherwise a derivation using the lift would not survive `canonExpr`. The two
-- shape-CHANGING cases are the interesting ones, and both land back in the set:
-- a bare `RVar` becomes `RResolved` (or stays), and `RQualified` becomes
-- `RResolved` (or stays).
cls-canon : ∀ (bound : List String) (um : UnaliasedMap) (am : AliasMap)
              {e : RawExpr}
          → ClosedLiftShape e → ClosedLiftShape (canonExpr bound um am e)
cls-canon bound um am (cls-var {x = x})
  with elemStr x bound | isBuiltinName x | lookupUnaliased um x
... | true  | _     | _       = cls-var
... | false | true  | _       = cls-res
... | false | false | just _  = cls-res
... | false | false | nothing = cls-res
cls-canon bound um am (cls-qual {a = alias}) with lookupImportAlias am alias
... | just _  = cls-res
... | nothing = cls-qual
cls-canon bound um am cls-res   = cls-res
cls-canon bound um am cls-let   = cls-let
cls-canon bound um am cls-destr = cls-destr
cls-canon bound um am cls-unit  = cls-unit
cls-canon bound um am cls-str   = cls-str
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
cls-reflect bound um am (RStringLit _) _        = cls-str
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
-- (signatures/imports/type-aliases carry no expression refs). The initial bound
-- set is `polys` — the own-module polymorphic-def names — so bare references to
-- them are KEPT as `RVar` (taking `t-var-poly-instantiate`), never canonicalized.
canonDecl : List String → UnaliasedMap → AliasMap → Decl → Decl
canonDecl polys um am (DFunDef name alloc body) = DFunDef name alloc (canonExpr polys um am body)
canonDecl polys um am d                         = d

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
-- Plan 0.50 (clash-freedom): BOTH aliased and unaliased imports key their
-- inlined signatures by the FULL dotted path, matching the canonical names
-- `canon` produces (`RQualified`/`RVar` → `RResolved (canonical (path++[name]))`).
-- So the import-table key = `showCanonical cn` by construction, and distinct
-- imported modules' same-named primitives get distinct symbols.
ownerOf : Import → Maybe String
ownerOf (mkImport path (just _)) = just (showPath (expandPath path))
ownerOf (mkImport path nothing)  = just (showPath (expandPath path))

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
-- DE-WITHED (plan 0.81). Both decisions — the module-table lookup and the
-- recursive call — are explicit PARAMETERS with their equations, instead of
-- `with` scrutinees. A `with` here is opaque to any proof whose hypothesis is
-- `resolveDecls … ≡ inj₂ ds'`: that type does not mention either scrutinee, so
-- nothing abstracts it and no `rewrite` fires. Same reason `inferElabV`'s
-- lookups were de-withed for Completeness.
resolveDecls : List String → UnaliasedMap → AliasMap → ModuleMap → List Decl → String ⊎ List Decl
resolveDecls-import-aux :
  ∀ (polys : List String) (um : UnaliasedMap) (am : AliasMap) (mm : ModuleMap)
    (imp : Import) (rest : List Decl)
  → (lm : Maybe Module) → lookupModule mm (Import.path imp) ≡ lm
  → (rr : String ⊎ List Decl) → resolveDecls polys um am mm rest ≡ rr
  → String ⊎ List Decl
resolveDecls-cons-aux :
  ∀ (polys : List String) (um : UnaliasedMap) (am : AliasMap) (d : Decl)
  → (rr : String ⊎ List Decl) → String ⊎ List Decl

resolveDecls _     _  _  _      []                   = inj₂ []
resolveDecls polys um am modMap (DImport imp ∷ rest) =
  resolveDecls-import-aux polys um am modMap imp rest
    (lookupModule modMap (Import.path imp)) refl
    (resolveDecls polys um am modMap rest) refl
resolveDecls polys um am modMap (d ∷ rest) =
  resolveDecls-cons-aux polys um am d (resolveDecls polys um am modMap rest)

resolveDecls-import-aux polys um am mm imp rest nothing _ _ _ =
  inj₁ ("Internal error: import path not in ModuleMap: " ++ showPath (Import.path imp))
resolveDecls-import-aux polys um am mm imp rest (just (mkModule impDs)) _ (inj₁ err) _ =
  inj₁ err
resolveDecls-import-aux polys um am mm imp rest (just (mkModule impDs)) _ (inj₂ tailDs) _ =
  inj₂ (signaturesWithOwner (ownerOf imp) impDs ++L tailDs)

resolveDecls-cons-aux polys um am d (inj₁ err)    = inj₁ err
resolveDecls-cons-aux polys um am d (inj₂ tailDs) = inj₂ (canonDecl polys um am d ∷ tailDs)

-- | Public entry. Haskell populates the map, calls this, and feeds
-- the resolved module to `compileResolved`.
resolveImports : ModuleMap → Module → String ⊎ Module
resolveImports modMap (mkModule ds)
  with resolveDecls (polyDefNames ds) (collectUnaliased modMap ds) (collectAliases ds) modMap ds
... | inj₁ err   = inj₁ err
... | inj₂ ds'   = inj₂ (mkModule ds')
