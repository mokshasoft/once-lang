-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CanonReflectModule — Plan 0.51 module-level REVERSE wiring.
--
-- The mirror of `CanonModule.canon-preserves-typing`: a well-typed RESOLVED
-- module `mR` (with a valid main) reflects to a well-typed UN-resolved `mU`. This
-- discharges `ResolverBridge.resolver-reflects-typing` for the import-free
-- fragment; the import case routes to a residual `*-imports` postulate exactly as
-- `preserves-typing` does.
--
-- TOP-DOWN NOTE (the signature the apex actually needs):
-- `resolver-reflects-typing` cannot produce `HasValidMain mU` from `ModuleTyped
-- mR` ALONE (a main-less module is `ModuleTyped` but not `HasValidMain`). The
-- valid-main is threaded from the call site, where it is derived from the
-- compilation evidence via `MC.moduleToIR-sound mR MT mi`. So the judgment takes
-- `HasValidMain mR` as an input and reflects it to `HasValidMain mU` — a provable
-- theorem rather than the unprovable original postulate shape.
--
-- SCAFFOLD (feedback_scaffold_then_discharge): `module-typed-and-valid-reflect`
-- (the reverse of `CanonModuleTyped.module-typed-and-valid`) is a NAMED temporary
-- postulate, to be discharged via `CanonReflectMutual.canon-reflects-ᶜ` + the
-- reverse `AllFunsTyped`/`AllMainEffUU`/`MainExists` transports.
------------------------------------------------------------------------

module Once.Adequacy.CanonReflectModule where

open import Data.List using (List; map)
open import Data.String using (String)
open import Data.Product using (_×_; _,_; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

import Once.Parser.Module.Core as P
open import Once.Parser using (FunInfo; PolyFunInfo)
import Once.Compile as C
open import Once.Parser.Module.Resolve using (ModuleMap; resolveImports; canonDecl; polyDefNames)
import Once.Adequacy.CanonResolve as CR
import Once.Adequacy.AcceptSound as AS
import Once.Adequacy.ModuleComplete as MC
open import Once.Adequacy.CanonModuleTyped
  using (canonModule; extractFunctions-canon; collectSigEffects-canon)
open import Once.Adequacy.CanonExtract using (canonFuns; canonPolys)
open import Once.Adequacy.CanonPolyNames using (polyInB-bridge)
open import Once.Adequacy.CanonReflectAllFuns
  using (AllFunsTyped-reflect; AllMainEffUU-reflect; MainExists-reflect)
open import Once.Adequacy.CanonReflectExtract using (extractFunctions-canon-inj₁)

------------------------------------------------------------------------
-- The reverse of `CanonModuleTyped.module-typed-and-valid`, assembled from the
-- reverse `AllFunsTyped` transport. The bundle `P` carries `ModuleTyped-ef` with
-- its validity predicates over the SAME `ef`, so one `subst` along
-- `extractFunctions-canon` transports the whole Σ (the validity predicates ride).
------------------------------------------------------------------------

-- A bundle of `ModuleTyped-ef` + its two validity predicates over one `ef`.
HVBundle : ∀ (m : P.Module) (ef : _) → Set
HVBundle m ef = Σ-syntax (AS.ModuleTyped-ef m ef)
  (λ mt → MC.ModuleMainEffUU-ef m ef mt × MC.ModuleMainExists-ef m ef mt)

-- A bundle of an `AllFunsTyped` derivation + its two validity predicates,
-- indexed by the sig-effects (so one `subst` along `collectSigEffects-canon`
-- carries the validity predicates with the derivation).
VBundle : ∀ (b : List String) (funsU : List FunInfo) (polysU : List PolyFunInfo) (se : _) → Set
VBundle b funsU polysU se = Σ-syntax
  (AS.AllFunsTyped (C.buildPolyCtx (canonPolys b polysU)) se (canonFuns b funsU) C.emptyFunCtx)
  (λ mt → MC.AllMainEffUU mt × MC.MainExists mt)

module-typed-and-valid-reflect : ∀ (ds : List P.Decl)
    (mt : AS.ModuleTyped (canonModule ds)) → MC.HasValidMain-decl (canonModule ds) mt
  → Σ-syntax (AS.ModuleTyped (P.mkModule ds)) (λ mt' → MC.HasValidMain-decl (P.mkModule ds) mt')
module-typed-and-valid-reflect ds mt vmain =
  go (C.extractFunctions (C.extractAliases (P.mkModule ds)) (P.mkModule ds)) refl
  where
    go : ∀ efU → C.extractFunctions (C.extractAliases (P.mkModule ds)) (P.mkModule ds) ≡ efU
       → Σ-syntax (AS.ModuleTyped (P.mkModule ds)) (λ mt' → MC.HasValidMain-decl (P.mkModule ds) mt')
    go (inj₁ x) ef-eq =
      ⊥-elim (subst (AS.ModuleTyped-ef (canonModule ds)) (extractFunctions-canon-inj₁ ds ef-eq) mt)
    go (inj₂ (funsU , polysU)) ef-eq rewrite ef-eq =
      let b   = polyDefNames ds
          pib = polyInB-bridge (P.mkModule ds) funsU polysU ef-eq
          -- (ModuleTyped , valid) bundle transported to the canonFuns/canonPolys form
          bnd : HVBundle (canonModule ds) (inj₂ (canonFuns b funsU , canonPolys b polysU))
          bnd = subst (HVBundle (canonModule ds)) (extractFunctions-canon ds funsU polysU ef-eq)
                      (mt , proj₁ vmain , proj₂ vmain)
          -- then transported along collectSigEffects(canonModule) = collectSigEffects ds
          vb : VBundle b funsU polysU (C.collectSigEffects ds)
          vb = subst (VBundle b funsU polysU) (collectSigEffects-canon ds) bnd
          mt-c  = proj₁ vb
          amu-c = proj₁ (proj₂ vb)
          me-c  = proj₂ (proj₂ vb)
      in AllFunsTyped-reflect b polysU (C.collectSigEffects ds) pib funsU mt-c
       , (AllMainEffUU-reflect b polysU (C.collectSigEffects ds) pib funsU mt-c amu-c
         , MainExists-reflect b polysU (C.collectSigEffects ds) pib funsU mt-c me-c)

postulate
  -- The IMPORT residual (parallels `CanonModule.resolver-preserves-typing-imports`).
  resolver-reflects-typing-imports : ∀ (mm : ModuleMap) (mU mR : P.Module)
    → resolveImports mm mU ≡ inj₂ mR → (mt : AS.ModuleTyped mR) → MC.HasValidMain-decl mR mt
    → Σ-syntax (AS.ModuleTyped mU) (λ mt' → MC.HasValidMain-decl mU mt')

------------------------------------------------------------------------
-- The spine = `resolver-reflects-typing`, the reverse of `canon-preserves-typing`.
------------------------------------------------------------------------

inj₂-inj : ∀ {A B : Set} {a b : B} → (inj₂ {A = A} a) ≡ inj₂ b → a ≡ b
inj₂-inj refl = refl

resolver-reflects-typing : ∀ (mm : ModuleMap) (mU mR : P.Module)
  → resolveImports mm mU ≡ inj₂ mR → (mt : AS.ModuleTyped mR) → MC.HasValidMain-decl mR mt
  → Σ-syntax (AS.ModuleTyped mU) (λ mt' → MC.HasValidMain-decl mU mt')
resolver-reflects-typing mm mU mR res-eq mt hvm = go (CR.noImports? (P.Module.decls mU))
  where
    ds = P.Module.decls mU
    go : _ → Σ-syntax (AS.ModuleTyped mU) (λ mt' → MC.HasValidMain-decl mU mt')
    go (yes ni) = module-typed-and-valid-reflect ds (proj₁ bundle) (proj₂ bundle)
      where
        mR≡cm : mR ≡ canonModule ds
        mR≡cm = inj₂-inj (trans (sym res-eq) (CR.resolveImports-ni mm ds ni))
        bundle : Σ-syntax (AS.ModuleTyped (canonModule ds)) (MC.HasValidMain-decl (canonModule ds))
        bundle = subst (λ m → Σ-syntax (AS.ModuleTyped m) (MC.HasValidMain-decl m)) mR≡cm (mt , hvm)
    go (no _) = resolver-reflects-typing-imports mm mU mR res-eq mt hvm
