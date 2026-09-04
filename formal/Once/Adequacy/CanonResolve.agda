-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CanonResolve — the IMPORT-FREE reduction of `resolveImports`.
--
-- For a module with NO `DImport` decls, `resolveImports` always SUCCEEDS and is
-- exactly the own-module canonicalization `mkModule (map (canonDecl …) ds)`
-- (`collectUnaliased`/`collectAliases` are empty, `resolveDecls` maps `canonDecl`
-- over every decl). This discharges `CanonModule.resolve-result` for the
-- import-free fragment; the import case routes to a residual (it needs the
-- ModuleMap to carry every dependency — a Haskell-layer / Plan-0.50 concern).
------------------------------------------------------------------------

module Once.Adequacy.CanonResolve where

open import Data.List using (List; []; _∷_; map)
open import Data.Sum using (inj₂)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Parser.Module.Core
  using (Decl; DTypeSig; DFunDef; DSignature; DImport; DTypeAlias; Module;
         mkModule)
open import Once.Parser.Module.Resolve
  using (ModuleMap; resolveImports; resolveDecls; canonDecl; collectAliases; collectUnaliased; polyDefNames)

------------------------------------------------------------------------
-- NoImports predicate (+ decision).
------------------------------------------------------------------------

NotImport : Decl → Set
NotImport (DImport _) = ⊥
NotImport _           = ⊤

NoImports : List Decl → Set
NoImports []        = ⊤
NoImports (d ∷ rest) = NotImport d × NoImports rest

noImports? : (ds : List Decl) → Dec (NoImports ds)
noImports? [] = yes tt
noImports? (DImport _ ∷ rest) = no (λ ())
noImports? (DTypeSig _ _ ∷ rest)        with noImports? rest
... | yes p = yes (tt , p)
... | no ¬p = no (λ { (_ , q) → ¬p q })
noImports? (DFunDef _ _ ∷ rest)       with noImports? rest
... | yes p = yes (tt , p)
... | no ¬p = no (λ { (_ , q) → ¬p q })
noImports? (DSignature _ _ _ _ ∷ rest)  with noImports? rest
... | yes p = yes (tt , p)
... | no ¬p = no (λ { (_ , q) → ¬p q })
noImports? (DTypeAlias _ _ _ ∷ rest)    with noImports? rest
... | yes p = yes (tt , p)
... | no ¬p = no (λ { (_ , q) → ¬p q })

------------------------------------------------------------------------
-- Import-free reductions.
------------------------------------------------------------------------

collectAliases-ni : ∀ (ds : List Decl) → NoImports ds → collectAliases ds ≡ []
collectAliases-ni [] _ = refl
collectAliases-ni (DTypeSig _ _ ∷ rest)       (_ , ni) = collectAliases-ni rest ni
collectAliases-ni (DFunDef _ _ ∷ rest)      (_ , ni) = collectAliases-ni rest ni
collectAliases-ni (DSignature _ _ _ _ ∷ rest) (_ , ni) = collectAliases-ni rest ni
collectAliases-ni (DTypeAlias _ _ _ ∷ rest)   (_ , ni) = collectAliases-ni rest ni

collectUnaliased-ni : ∀ (mm : ModuleMap) (ds : List Decl) → NoImports ds → collectUnaliased mm ds ≡ []
collectUnaliased-ni mm [] _ = refl
collectUnaliased-ni mm (DTypeSig _ _ ∷ rest)       (_ , ni) = collectUnaliased-ni mm rest ni
collectUnaliased-ni mm (DFunDef _ _ ∷ rest)      (_ , ni) = collectUnaliased-ni mm rest ni
collectUnaliased-ni mm (DSignature _ _ _ _ ∷ rest) (_ , ni) = collectUnaliased-ni mm rest ni
collectUnaliased-ni mm (DTypeAlias _ _ _ ∷ rest)   (_ , ni) = collectUnaliased-ni mm rest ni

resolveDecls-ni : ∀ polys um am (mm : ModuleMap) (ds : List Decl) → NoImports ds
  → resolveDecls polys um am mm ds ≡ inj₂ (map (canonDecl polys um am) ds)
resolveDecls-ni polys um am mm [] _ = refl
resolveDecls-ni polys um am mm (DTypeSig n ty ∷ rest) (_ , ni)
  rewrite resolveDecls-ni polys um am mm rest ni = refl
resolveDecls-ni polys um am mm (DFunDef n b ∷ rest) (_ , ni)
  rewrite resolveDecls-ni polys um am mm rest ni = refl
resolveDecls-ni polys um am mm (DSignature n o ty se ∷ rest) (_ , ni)
  rewrite resolveDecls-ni polys um am mm rest ni = refl
resolveDecls-ni polys um am mm (DTypeAlias n ps t ∷ rest) (_ , ni)
  rewrite resolveDecls-ni polys um am mm rest ni = refl

-- The CanonModule obligation `resolve-result`, for the import-free fragment.
resolveImports-ni : ∀ (mm : ModuleMap) (ds : List Decl) → NoImports ds
  → resolveImports mm (mkModule ds)
      ≡ inj₂ (mkModule (map (canonDecl (polyDefNames ds) [] []) ds))
resolveImports-ni mm ds ni
  rewrite collectUnaliased-ni mm ds ni
  rewrite collectAliases-ni ds ni
  rewrite resolveDecls-ni (polyDefNames ds) [] [] mm ds ni = refl
