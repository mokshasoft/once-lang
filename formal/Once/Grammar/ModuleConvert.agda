-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Grammar.ModuleConvert — `GModule → Maybe Module`.
--
-- The structural conversion from the formal-grammar module AST
-- (`Once.Grammar.GModule`) to the parser's module AST
-- (`Once.Parser.Module.Core.Module`). Discharges the `gmoduleToModule`
-- postulate in `Once.Verified.Compile`.
--
-- Per-decl conversion:
--   - DTypeSig / DSignature : GType → PolyType (total; `TVar ↦ PTVar`).
--   - DTypeAlias            : GType → Type via `gtypeToType` (partial;
--                             fails on `TVar`, since `Decl.DTypeAlias`
--                             carries a monomorphic `Type`).
--   - DFunDef               : params are folded into lambdas, then the
--                             body is converted via `concrete?` +
--                             `gexprToRaw` (partial; fails outside the
--                             concrete domain).
--   - DImport               : direct (`ModulePath`/alias are `String`s).
------------------------------------------------------------------------

module Once.Grammar.ModuleConvert where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapMaybe)
open import Data.String using (String)

open import Once.Grammar as G
  using ( GExpr; GType; GDecl; GModule; ELam )
open import Once.Parser.Module.Core as P
  using ( Decl; Module; Import; mkImport; mkModule )
open import Once.Type
  using ( Type; PolyType
        ; PUnit; PVoid; _P*_; _P+_; _P⇒[_]_; PEff; PInt; PFloat; PStr
        ; PBuffer; PTVar )
open import Once.Grammar.Convert    using (gtypeToType)
open import Once.Grammar.ExprConvert using (gexprToRaw)
open import Once.Grammar.ConcreteDec using (concrete?)

------------------------------------------------------------------------
-- GType → PolyType (total: PolyType mirrors GType, incl. type vars).
------------------------------------------------------------------------

gtypeToPolyType : GType → PolyType
gtypeToPolyType G.TUnit          = PUnit
gtypeToPolyType G.TVoid          = PVoid
gtypeToPolyType G.TInt           = PInt
gtypeToPolyType G.TFloat         = PFloat
gtypeToPolyType G.TBuffer        = PBuffer
gtypeToPolyType G.TString        = PStr
gtypeToPolyType (G.TVar v)       = PTVar v
gtypeToPolyType (a G.⊗ b)        = gtypeToPolyType a P* gtypeToPolyType b
gtypeToPolyType (a G.⊕ b)        = gtypeToPolyType a P+ gtypeToPolyType b
gtypeToPolyType (a G.⇒[ q ] b)   = gtypeToPolyType a P⇒[ q ] gtypeToPolyType b
gtypeToPolyType (G.TEff a b)     = PEff (gtypeToPolyType a) (gtypeToPolyType b)

------------------------------------------------------------------------
-- AllocStrategy: the two enums have identical constructors in
-- different modules; map by name.
------------------------------------------------------------------------

gAllocToAlloc : G.AllocStrategy → P.AllocStrategy
gAllocToAlloc G.Stack = P.Stack
gAllocToAlloc G.Arena = P.Arena
gAllocToAlloc G.Pool  = P.Pool
gAllocToAlloc G.Heap  = P.Heap
gAllocToAlloc G.Const = P.Const

------------------------------------------------------------------------
-- Fold a function's parameter list into nested lambdas, so the body
-- converts to a `RawExpr` with the parameters lambda-bound (the
-- parser's `Decl.DFunDef` representation).
------------------------------------------------------------------------

wrapParams : List String → GExpr → GExpr
wrapParams []       body = body
wrapParams (p ∷ ps) body = ELam p (wrapParams ps body)

------------------------------------------------------------------------
-- Per-declaration conversion.
------------------------------------------------------------------------

gdeclToDecl : GDecl → Maybe Decl
gdeclToDecl (G.DTypeSig name ty)   = just (P.DTypeSig name (gtypeToPolyType ty))
gdeclToDecl (G.DSignature name ty) = just (P.DSignature name nothing (gtypeToPolyType ty))
gdeclToDecl (G.DImport path alias) = just (P.DImport (mkImport path alias))
gdeclToDecl (G.DTypeAlias name params ty) with gtypeToType ty
... | just t  = just (P.DTypeAlias name params t)
... | nothing = nothing
gdeclToDecl (G.DFunDef name params alloc body) with concrete? (wrapParams params body)
... | just c  = just (P.DFunDef name (mapMaybe gAllocToAlloc alloc) (gexprToRaw c))
... | nothing = nothing

------------------------------------------------------------------------
-- Module conversion: traverse the declaration list.
------------------------------------------------------------------------

mapDecls : List GDecl → Maybe (List Decl)
mapDecls []       = just []
mapDecls (d ∷ ds) with gdeclToDecl d | mapDecls ds
... | just d' | just ds' = just (d' ∷ ds')
... | _       | _        = nothing

gmoduleToModule : GModule → Maybe Module
gmoduleToModule gmod with mapDecls (GModule.decls gmod)
... | just ds = just (mkModule ds)
... | nothing = nothing
