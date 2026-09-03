-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Grammar.Import — the RELATIONS for `import a.b.c [as alias]`,
-- and nothing else (Plan 0.84).
--
-- Reachable from `correct` via `ParsesDecl`, so a spec reviewer must read it.
-- `sound-import`/`complete-import`, the WF path-scanner proofs and the
-- inversion lemmas stay in `Once.Grammar.ImportBridge`.
------------------------------------------------------------------------

module Once.Spec.Grammar.Import where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.String using (String)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Once.Parser.Token
open import Once.Parser.Module.Core using (Decl; DImport; mkImport; wordHead)
open import Once.Parser.Module.Import using (dropDot; dotHead)

------------------------------------------------------------------------
-- The dotted module path.
------------------------------------------------------------------------

data ParsesModulePath : List Token → List String → List Token → Set where
  pmp-cons    : ∀ {name tail path rest'} → dotHead tail ≡ true →
                ParsesModulePath (dropDot tail) path rest' →
                ParsesModulePath (TWord name ∷ tail) (name ∷ path) rest'
  pmp-dotfail : ∀ {name tail} → dotHead tail ≡ true → wordHead (dropDot tail) ≡ false →
                ParsesModulePath (TWord name ∷ tail) (name ∷ []) tail
  pmp-nodot   : ∀ {name tail} → dotHead tail ≡ false →
                ParsesModulePath (TWord name ∷ tail) (name ∷ []) tail

------------------------------------------------------------------------
-- The optional `as alias` tail.
------------------------------------------------------------------------

data ParsesImportAlias (path : List String) : List Token → Decl → List Token → Set where
  pia-alias-r   : ∀ {alias rest} →
    ParsesImportAlias path (TWord "as" ∷ TWord alias ∷ rest) (DImport (mkImport path (just alias))) rest
  pia-neq-r     : ∀ {s rest} → s ≢ "as" →
    ParsesImportAlias path (TWord s ∷ rest) (DImport (mkImport path nothing)) (TWord s ∷ rest)
  pia-nonword-r : ∀ {toks} → wordHead toks ≡ false →
    ParsesImportAlias path toks (DImport (mkImport path nothing)) toks

------------------------------------------------------------------------
-- `ParsesImport` = dotted path then optional alias.
------------------------------------------------------------------------

data ParsesImport : List Token → Decl → List Token → Set where
  pi-mk : ∀ {toks path rest d rest'} →
    ParsesModulePath toks path rest → ParsesImportAlias path rest d rest' →
    ParsesImport toks d rest'
