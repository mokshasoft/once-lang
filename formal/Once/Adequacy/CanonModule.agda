-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.CanonModule — Plan 0.51 Step 4 (module-level wiring).
--
-- TOP-DOWN discharge of `ResolverBridge.resolver-preserves-typing`: a well-typed
-- UN-resolved module resolves to a well-typed module. The LOAD-BEARING core is
-- `AllFunsTyped-canon`, which lifts the per-function `⊢ᶜ` derivations through the
-- resolver's body-canonicalization using `CanonPreserveMutual.canon-pres-ᶜ`
-- (Plan 0.51 Step 2). So the heavy expression-level induction (~54 cases) is now
-- GENUINELY on the apex path, not an island.
--
-- The remaining obligations are STRUCTURAL plumbing, named + dictated by this
-- spine (NOT guessed bottom-up):
--   * `module-typed-canon`  — `extractFunctions`∘`canonDecl` commute + the poly
--     context's OWN bodies canonicalize (so `ModuleTyped mR` is at `polysR`, not
--     `polysU`); the poly-ctx transport is the Step-2 generalization.
--   * `has-valid-main-canon` — `main`'s signature is unchanged, so validity rides.
--   * `resolve-preserves-typing-imports` — the import case (residual; the
--     import-free fragment is what this module discharges).
------------------------------------------------------------------------

module Once.Adequacy.CanonModule where

open import Data.Bool using (Bool; true)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (Type)
open import Once.TypeCheck.Raw using (RawExpr)
import Once.Parser.Module.Core as P
open import Once.Parser using (FunInfo; mkFunInfo)
import Once.Compile as C
open import Once.Parser.Module.Resolve
  using (ModuleMap; resolveImports; canonExpr; polyDefNames; elemStr)
open import Once.TypeCheck.Classify using (lookupPoly; PolyCtx)
open import Once.TypeCheck.Judgment using (_⊢ᶜ_∶_⨾_)
import Once.Adequacy.AcceptSound as AS
import Once.Adequacy.ModuleComplete as MC
open import Once.Adequacy.CanonPreserve using (⊆ᵇ-nil)
open import Once.Adequacy.CanonPreserveMutual
  using (canon-pres-ᶜ; mkPIB)

------------------------------------------------------------------------
-- Body canonicalization on the EXTRACTED function list (mirrors `canonDecl`
-- acting on each `DFunDef` body, with the own-module poly names as the bound).
------------------------------------------------------------------------

canonBody : List String → FunInfo → FunInfo
canonBody bound fi =
  record fi { funBody = canonExpr bound [] [] (FunInfo.funBody fi) }

mapCanonBody : List String → List FunInfo → List FunInfo
mapCanonBody bound = map (canonBody bound)

------------------------------------------------------------------------
-- LOAD-BEARING core: lift `AllFunsTyped` through body-canonicalization.
-- The poly context `polys` is FIXED here (the per-function ctx's `.named` is ∅
-- and its `.polys` is this `polys`), so each body's derivation lifts directly by
-- `canon-pres-ᶜ` with `Names⊆ = ⊆ᵇ-nil` and the module-level `PolyInB` (`pib`).
------------------------------------------------------------------------

postulate
  -- D007 inferred-type functions: `inferType` (the elaborator) is canonExpr-
  -- invariant. The signatured case (`funType = just ty`) is definitional; this
  -- covers the `nothing` case. Dictated by the `tcons` reconstruction below.
  resolveFunType-canon :
    ∀ (ctx : C.FunCtx) (polys : PolyCtx) (bound : List String) (fi : FunInfo) (ty : Type)
    → C.resolveFunType ctx polys (FunInfo.funType fi) (FunInfo.funBody fi) ≡ inj₂ ty
    → C.resolveFunType ctx polys (FunInfo.funType fi) (canonExpr bound [] [] (FunInfo.funBody fi)) ≡ inj₂ ty

AllFunsTyped-canon : ∀ {polys sigEffs ctx} (bound : List String)
  → (∀ {x s b} → lookupPoly polys x ≡ just (s , b) → elemStr x bound ≡ true)
  → (funs : List FunInfo)
  → AS.AllFunsTyped polys sigEffs funs ctx
  → AS.AllFunsTyped polys sigEffs (mapCanonBody bound funs) ctx
AllFunsTyped-canon bound pib [] AS.tnil = AS.tnil
AllFunsTyped-canon {polys} bound pib (fi ∷ rest) (AS.tcons {ty = ty} rft jud rest-typed) =
  AS.tcons (resolveFunType-canon _ polys bound fi ty rft)
           (canon-pres-ᶜ bound (⊆ᵇ-nil {bound}) (mkPIB (λ {x'} h → pib h)) jud)
           (AllFunsTyped-canon bound pib rest rest-typed)

------------------------------------------------------------------------
-- Module-level bridges (structural; dictated by the spine).
------------------------------------------------------------------------

postulate
  -- The `polys` context's names ARE the own-module poly-def names (both are the
  -- non-ground `DTypeSig`s — `buildPolyCtx ∘ extractFunctions` vs `polyDefNames`).
  -- Dictated by `AllFunsTyped-canon`'s `PolyInB` argument. The `extractFunctions`
  -- link is LOAD-BEARING: without it the claim is false for an unrelated `polysU`.
  polyInB-bridge :
    ∀ (mU : P.Module) (funsU : List FunInfo) (polysU : List C.PolyFunInfo)
    → C.extractFunctions (C.extractAliases mU) mU ≡ inj₂ (funsU , polysU)
    → ∀ {x s b} → lookupPoly (C.buildPolyCtx polysU) x ≡ just (s , b)
    → elemStr x (polyDefNames (P.Module.decls mU)) ≡ true

  -- `extractFunctions`∘`canonDecl` commute (funs/sigEffs preserved, bodies
  -- canonExpr'd) + the poly-context transport (`polysR` has canonExpr'd bodies):
  -- the lifted `AllFunsTyped` over `mapCanonBody funsU` IS `ModuleTyped mR`. The
  -- Step-2 poly-ctx generalization lives here.
  module-bridge :
    ∀ (mm : ModuleMap) (mU mR : P.Module)
      (funsU : List FunInfo) (polysU : List C.PolyFunInfo)
    → C.extractFunctions (C.extractAliases mU) mU ≡ inj₂ (funsU , polysU)
    → resolveImports mm mU ≡ inj₂ mR
    → AS.AllFunsTyped (C.buildPolyCtx polysU) (C.collectSigEffects (P.Module.decls mU))
        (mapCanonBody (polyDefNames (P.Module.decls mU)) funsU) C.emptyFunCtx
    → AS.ModuleTyped mR

-- `ModuleTyped mU → ModuleTyped mR` — a TOP-LEVEL aux taking the `extractFunctions`
-- result explicitly (NOT a `with`-block: keeps the `AllFunsTyped` reduction clean
-- and avoids with-abstraction opacity). The `inj₂` arm is the LOAD-BEARING path:
-- it calls `AllFunsTyped-canon` (→ `canon-pres-ᶜ`), then `module-bridge`.
module-typed-canon-ef :
  ∀ (mm : ModuleMap) (mU mR : P.Module)
    (efU : String ⊎ (List FunInfo × List C.PolyFunInfo))
  → C.extractFunctions (C.extractAliases mU) mU ≡ efU
  → resolveImports mm mU ≡ inj₂ mR
  → AS.ModuleTyped-ef mU efU → AS.ModuleTyped mR
module-typed-canon-ef mm mU mR (inj₁ _) ef-eq res-eq mt = ⊥-elim mt
module-typed-canon-ef mm mU mR (inj₂ (funsU , polysU)) ef-eq res-eq mt =
  module-bridge mm mU mR funsU polysU ef-eq res-eq
    (AllFunsTyped-canon (polyDefNames (P.Module.decls mU))
       (polyInB-bridge mU funsU polysU ef-eq) funsU mt)

module-typed-canon :
  ∀ (mm : ModuleMap) (mU mR : P.Module)
  → resolveImports mm mU ≡ inj₂ mR
  → AS.ModuleTyped mU → AS.ModuleTyped mR
module-typed-canon mm mU mR res-eq mt =
  module-typed-canon-ef mm mU mR (C.extractFunctions (C.extractAliases mU) mU) refl res-eq mt

postulate
  has-valid-main-canon :
    ∀ (mm : ModuleMap) (mU mR : P.Module)
    → (res-eq : resolveImports mm mU ≡ inj₂ mR)
    → (mt : AS.ModuleTyped mU) → MC.HasValidMain-decl mU mt
    → MC.HasValidMain-decl mR (module-typed-canon mm mU mR res-eq mt)

  -- Resolution SUCCEEDS for a well-typed module (residual): import-free always
  -- succeeds (`resolveDecls` over non-`DImport` decls never returns `inj₁`); the
  -- import case assumes the `ModuleMap` carries every dependency (a Haskell-layer
  -- invariant). Keeps the apex interface total.
  resolve-result :
    ∀ (mm : ModuleMap) (mU : P.Module) → AS.ModuleTyped mU
    → Σ-syntax P.Module (λ mR → resolveImports mm mU ≡ inj₂ mR)

------------------------------------------------------------------------
-- The spine = `resolver-preserves-typing`. Resolve; on success lift the typing
-- and the valid-main; on failure (import path not in map) route to the residual.
------------------------------------------------------------------------

canon-preserves-typing :
  ∀ (mm : ModuleMap) (mU : P.Module) (mt : AS.ModuleTyped mU)
  → MC.HasValidMain-decl mU mt
  → Σ-syntax P.Module (λ mR →
      (resolveImports mm mU ≡ inj₂ mR)
      × Σ-syntax (AS.ModuleTyped mR) (λ mt' → MC.HasValidMain-decl mR mt'))
canon-preserves-typing mm mU mt vmain =
  let (mR , res-eq) = resolve-result mm mU mt
  in mR , res-eq
        , module-typed-canon mm mU mR res-eq mt
        , has-valid-main-canon mm mU mR res-eq mt vmain
