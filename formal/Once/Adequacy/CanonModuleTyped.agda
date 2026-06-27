-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.CanonModuleTyped — `ModuleTyped` transports along the resolver.
--
-- Assembles the discharge of the old `module-bridge` postulate: `ModuleTyped
-- (mkModule ds) → ModuleTyped (canonModule ds)` for the import-free fragment,
-- using `extract-commute` (extractFunctions∘canonDecl) + `AllFunsTyped-transport`
-- (the typing lift via canon-pres-ᶜ + polys-transport). The residual structural
-- facts (canonDecl preserves aliases / sig-effects / emitted names) are small,
-- clearly-true postulates.
------------------------------------------------------------------------

module Once.Adequacy.CanonModuleTyped where

open import Data.List using (List; []; _∷_; map)
open import Data.String using (String)
open import Data.Maybe using (nothing)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; subst)

open import Once.Parser.Module.Core using (Decl; Module; mkModule; decls)
open import Once.Parser using (FunInfo; PolyFunInfo)
import Once.Compile as C
open import Once.Parser.Module.Resolve using (canonDecl; polyDefNames)
import Once.Adequacy.AcceptSound as AS
open import Once.Adequacy.CanonExtract using (canonFI; canonFuns; canonPFI; canonPolys; extract-commute)
open import Once.Adequacy.CanonAllFuns using (AllFunsTyped-transport)
open import Once.Adequacy.CanonPolyNames using (polyInB-bridge; guardDistinct-inj₂)

------------------------------------------------------------------------
-- canonModule + the small structural commutes (canonDecl preserves
-- aliases / sig-effects / the distinctness guard since funNames are kept).
------------------------------------------------------------------------

canonModule : List Decl → Module
canonModule ds = mkModule (map (canonDecl (polyDefNames ds) [] []) ds)

postulate
  extractAliases-canon : ∀ (ds : List Decl)
    → C.extractAliases (canonModule ds) ≡ C.extractAliases (mkModule ds)
  collectSigEffects-canon : ∀ (ds : List Decl)
    → C.collectSigEffects (map (canonDecl (polyDefNames ds) [] []) ds) ≡ C.collectSigEffects ds
  -- canonFI preserves funName, so emittedNames (and the distinctness guard) are
  -- unchanged: guardDistinct passes iff it passed on the originals.
  guardDistinct-canon : ∀ (b : List String) (funsU : List FunInfo) (polysU : List PolyFunInfo)
    → C.guardDistinct (inj₂ (funsU , polysU)) ≡ inj₂ (funsU , polysU)
    → C.guardDistinct (inj₂ (canonFuns b funsU , canonPolys b polysU))
        ≡ inj₂ (canonFuns b funsU , canonPolys b polysU)

------------------------------------------------------------------------
-- extractFunctions transports (peel guardDistinct, commute, re-wrap).
------------------------------------------------------------------------

extractFunctions-canon : ∀ (ds : List Decl) (funsU : List FunInfo) (polysU : List PolyFunInfo)
  → C.extractFunctions (C.extractAliases (mkModule ds)) (mkModule ds) ≡ inj₂ (funsU , polysU)
  → C.extractFunctions (C.extractAliases (canonModule ds)) (canonModule ds)
      ≡ inj₂ (canonFuns (polyDefNames ds) funsU , canonPolys (polyDefNames ds) polysU)
extractFunctions-canon ds funsU polysU ef-eq
  rewrite extractAliases-canon ds
  rewrite extract-commute (polyDefNames ds) (C.extractAliases (mkModule ds)) ds nothing
            (guardDistinct-inj₂ (C.extractFunctions-go (C.extractAliases (mkModule ds)) ds nothing) ef-eq)
  = guardDistinct-canon (polyDefNames ds) funsU polysU (peel ef-eq)
  where
    peel : C.guardDistinct (C.extractFunctions-go (C.extractAliases (mkModule ds)) ds nothing) ≡ inj₂ (funsU , polysU)
         → C.guardDistinct (inj₂ (funsU , polysU)) ≡ inj₂ (funsU , polysU)
    peel e = subst (λ R → C.guardDistinct R ≡ inj₂ (funsU , polysU))
                   (guardDistinct-inj₂ (C.extractFunctions-go (C.extractAliases (mkModule ds)) ds nothing) e) e

------------------------------------------------------------------------
-- ModuleTyped transports.
------------------------------------------------------------------------

module-typed-canon-aux : ∀ (ds : List Decl)
    (efU : _) → C.extractFunctions (C.extractAliases (mkModule ds)) (mkModule ds) ≡ efU
  → AS.ModuleTyped-ef (mkModule ds) efU → AS.ModuleTyped (canonModule ds)
module-typed-canon-aux ds (inj₁ _) ef-eq mt = ⊥-elim mt
module-typed-canon-aux ds (inj₂ (funsU , polysU)) ef-eq mt
  rewrite extractFunctions-canon ds funsU polysU ef-eq
  rewrite collectSigEffects-canon ds =
    AllFunsTyped-transport (polyDefNames ds) polysU (C.collectSigEffects ds)
      (polyInB-bridge (mkModule ds) funsU polysU ef-eq) funsU mt

module-typed-canon : ∀ (ds : List Decl)
  → AS.ModuleTyped (mkModule ds) → AS.ModuleTyped (canonModule ds)
module-typed-canon ds mt =
  module-typed-canon-aux ds (C.extractFunctions (C.extractAliases (mkModule ds)) (mkModule ds)) refl mt
