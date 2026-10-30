-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Extract.Names.Proof — the imports the CLI reads are the module's
-- `import` declarations (plan 0.133 §6).
--
-- The Haskell side loads, before resolution, the modules `module-imports`
-- names (`Once.CLI.loadAndResolve`); the resolver then looks up the module's
-- own `DImport`s. They agree: an (path, alias) pair is listed exactly when the
-- module declares that import. (Which files the loader then reads for a path is
-- the Haskell side's, and trusted.)
------------------------------------------------------------------------

module Once.Extract.Names.Proof where

open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Function using (_⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality using (refl)

open import Once.Spec.Surface.Syntax
  using (Module; Decl; DImport; DTypeSig; DFunDef; DSignature; DTypeAlias; mkImport)
open import Once.Extract.Names using (imports-of; module-imports; import-path; import-alias)

private
  to : ∀ ds i → i ∈ imports-of ds → DImport (mkImport (import-path i) (import-alias i)) ∈ ds
  to (DImport _ ∷ ds)          i (here refl) = here refl
  to (DImport _ ∷ ds)          i (there p)   = there (to ds i p)
  to (DTypeSig _ _ ∷ ds)       i p           = there (to ds i p)
  to (DFunDef _ _ ∷ ds)        i p           = there (to ds i p)
  to (DSignature _ _ ∷ ds)     i p           = there (to ds i p)
  to (DTypeAlias _ _ _ ∷ ds)   i p           = there (to ds i p)

  from : ∀ ds i → DImport (mkImport (import-path i) (import-alias i)) ∈ ds → i ∈ imports-of ds
  from (DImport _ ∷ ds)          (p , a) (here refl) = here refl
  from (DImport _ ∷ ds)          i       (there q)   = there (from ds i q)
  from (DTypeSig _ _ ∷ ds)       i       (there q)   = from ds i q
  from (DFunDef _ _ ∷ ds)        i       (there q)   = from ds i q
  from (DSignature _ _ ∷ ds)     i       (there q)   = from ds i q
  from (DTypeAlias _ _ _ ∷ ds)   i       (there q)   = from ds i q

-- | A pair is listed exactly when the module declares that import.
imports-declared : ∀ (m : Module) (i : List String × Maybe String)
                 → i ∈ module-imports m ⇔ DImport (mkImport (import-path i) (import-alias i)) ∈ Module.decls m
imports-declared m i = mk⇔ (to (Module.decls m) i) (from (Module.decls m) i)

record VerifiedLoader : Set where
  field
    imports : ∀ (m : Module) (i : List String × Maybe String)
            → i ∈ module-imports m ⇔ DImport (mkImport (import-path i) (import-alias i)) ∈ Module.decls m

verifiedLoader : VerifiedLoader
verifiedLoader = record { imports = imports-declared }
