-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; subst)

open import Data.Maybe using (just)
open import Once.Parser.Module.Core
  using (Decl; DTypeSig; DFunDef; DSignature; DImport; DTypeAlias; Module; mkModule; decls)
open import Data.Bool using (true; false; _∧_)
open import Once.Parser using (FunInfo; PolyFunInfo)
open Once.Parser.FunInfo using (funIsPrimitive)
import Once.Compile as C
open import Once.Parser.Module.Resolve using (canonDecl; polyDefNames)
import Once.Adequacy.AcceptSound as AS
open import Once.Adequacy.CanonExtract using (canonFI; canonFuns; canonPFI; canonPolys; extract-commute)
open import Once.Adequacy.CanonAllFuns using (AllFunsTyped-transport; AllMainEffUU-transport; MainExists-transport)
open import Once.Adequacy.CanonPolyNames using (polyInB-bridge; guardDistinct-inj₂)
import Once.Adequacy.ModuleComplete as MC

------------------------------------------------------------------------
-- canonModule + the small structural commutes (canonDecl preserves
-- aliases / sig-effects / the distinctness guard since funNames are kept).
------------------------------------------------------------------------

canonModule : List Decl → Module
canonModule ds = mkModule (map (canonDecl (polyDefNames ds) [] []) ds)

-- canonDecl keeps DTypeAlias / DSignature, so aliases + sig-effects are unchanged
-- (independent of the bound `b`, which only affects DFunDef bodies — skipped here).
extractAliases-canonB : ∀ (b : List String) (ds : List Decl)
  → C.extractAliases (mkModule (map (canonDecl b [] []) ds)) ≡ C.extractAliases (mkModule ds)
extractAliases-canonB b [] = refl
extractAliases-canonB b (DTypeSig n ty ∷ rest)        = extractAliases-canonB b rest
extractAliases-canonB b (DFunDef n a bd ∷ rest)       = extractAliases-canonB b rest
extractAliases-canonB b (DSignature n o ty se ∷ rest) = extractAliases-canonB b rest
extractAliases-canonB b (DTypeAlias n p bd ∷ rest)    = cong (_ ∷_) (extractAliases-canonB b rest)
extractAliases-canonB b (DImport imp ∷ rest)          = extractAliases-canonB b rest

extractAliases-canon : ∀ (ds : List Decl)
  → C.extractAliases (canonModule ds) ≡ C.extractAliases (mkModule ds)
extractAliases-canon ds = extractAliases-canonB (polyDefNames ds) ds

collectSigEffects-canonB : ∀ (b : List String) (ds : List Decl)
  → C.collectSigEffects (map (canonDecl b [] []) ds) ≡ C.collectSigEffects ds
collectSigEffects-canonB b [] = refl
collectSigEffects-canonB b (DTypeSig n ty ∷ rest)                      = collectSigEffects-canonB b rest
collectSigEffects-canonB b (DFunDef n a bd ∷ rest)                     = collectSigEffects-canonB b rest
collectSigEffects-canonB b (DSignature n (just o) ty (just se) ∷ rest) = cong (_ ∷_) (collectSigEffects-canonB b rest)
collectSigEffects-canonB b (DSignature n nothing ty (just se) ∷ rest)  = cong (_ ∷_) (collectSigEffects-canonB b rest)
collectSigEffects-canonB b (DSignature n (just o) ty nothing ∷ rest)   = collectSigEffects-canonB b rest
collectSigEffects-canonB b (DSignature n nothing ty nothing ∷ rest)    = collectSigEffects-canonB b rest
collectSigEffects-canonB b (DTypeAlias n p bd ∷ rest)                  = collectSigEffects-canonB b rest
collectSigEffects-canonB b (DImport imp ∷ rest)                        = collectSigEffects-canonB b rest

collectSigEffects-canon : ∀ (ds : List Decl)
  → C.collectSigEffects (map (canonDecl (polyDefNames ds) [] []) ds) ≡ C.collectSigEffects ds
collectSigEffects-canon ds = collectSigEffects-canonB (polyDefNames ds) ds

-- canonFI preserves funName + funIsPrimitive (record update), so emittedNames —
-- and thus the distinctness guard — is unchanged.
emittedNames-canon : ∀ (b : List String) (funs : List FunInfo)
  → C.emittedNames (canonFuns b funs) ≡ C.emittedNames funs
emittedNames-canon b [] = refl
emittedNames-canon b (fi ∷ rest) with funIsPrimitive fi
... | true  = emittedNames-canon b rest
... | false = cong (_ ∷_) (emittedNames-canon b rest)

guardDistinct-canon : ∀ (b : List String) (funsU : List FunInfo) (polysU : List PolyFunInfo)
  → C.guardDistinct (inj₂ (funsU , polysU)) ≡ inj₂ (funsU , polysU)
  → C.guardDistinct (inj₂ (canonFuns b funsU , canonPolys b polysU))
      ≡ inj₂ (canonFuns b funsU , canonPolys b polysU)
guardDistinct-canon b funsU polysU hyp
  rewrite emittedNames-canon b funsU
  with C.namesDistinct (C.emittedNames funsU) ∧ C.allValidIdentB (C.emittedNames funsU) | hyp
... | true  | _  = refl
... | false | ()

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

------------------------------------------------------------------------
-- ModuleTyped + HasValidMain transport, BUNDLED so the validity predicates
-- compute over the clean `AllFunsTyped-transport` (not a subst): both
-- `extractFunctions(canonModule)` occurrences (in ModuleTyped and HasValidMain)
-- get rewritten together, so the whole Σ aligns in one scope.
------------------------------------------------------------------------

module-typed-and-valid-aux : ∀ (ds : List Decl)
    (efU : _) → C.extractFunctions (C.extractAliases (mkModule ds)) (mkModule ds) ≡ efU
  → (mt : AS.ModuleTyped-ef (mkModule ds) efU)
  → MC.ModuleMainEffUU-ef (mkModule ds) efU mt × MC.ModuleMainExists-ef (mkModule ds) efU mt
  → Σ-syntax (AS.ModuleTyped (canonModule ds)) (λ mt' → MC.HasValidMain-decl (canonModule ds) mt')
module-typed-and-valid-aux ds (inj₁ _) ef-eq mt vmain = ⊥-elim mt
module-typed-and-valid-aux ds (inj₂ (funsU , polysU)) ef-eq mt (amu , me)
  rewrite extractFunctions-canon ds funsU polysU ef-eq
  rewrite collectSigEffects-canon ds =
    AllFunsTyped-transport (polyDefNames ds) polysU (C.collectSigEffects ds)
      (polyInB-bridge (mkModule ds) funsU polysU ef-eq) funsU mt
    , (AllMainEffUU-transport (polyDefNames ds) polysU (C.collectSigEffects ds)
        (polyInB-bridge (mkModule ds) funsU polysU ef-eq) funsU mt amu
      , MainExists-transport (polyDefNames ds) polysU (C.collectSigEffects ds)
        (polyInB-bridge (mkModule ds) funsU polysU ef-eq) funsU mt me)

module-typed-and-valid : ∀ (ds : List Decl)
    (mt : AS.ModuleTyped (mkModule ds)) → MC.HasValidMain-decl (mkModule ds) mt
  → Σ-syntax (AS.ModuleTyped (canonModule ds)) (λ mt' → MC.HasValidMain-decl (canonModule ds) mt')
module-typed-and-valid ds mt vmain =
  module-typed-and-valid-aux ds (C.extractFunctions (C.extractAliases (mkModule ds)) (mkModule ds)) refl mt vmain
