-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (Type)
open import Once.TypeCheck.Raw using (RawExpr)
import Once.Parser.Module.Core as P
open import Once.Parser using (FunInfo; mkFunInfo)
import Once.Compile as C
open import Once.Parser.Module.Resolve
  using (ModuleMap; resolveImports; canonExpr; canonDecl; polyDefNames; elemStr)
import Once.Adequacy.CanonResolve as CR
open import Once.TypeCheck.Classify using (lookupPoly; PolyCtx)
open import Once.TypeCheck.Judgment using (_⊢ᶜ_∶_⨾_)
import Once.Adequacy.AcceptSound as AS
import Once.Adequacy.ModuleComplete as MC
open import Once.Adequacy.CanonModuleTyped using (canonModule; module-typed-and-valid)

------------------------------------------------------------------------
-- `ModuleTyped` transport is DISCHARGED (`Once.Adequacy.CanonModuleTyped`):
-- `module-typed-canon ds : ModuleTyped (mkModule ds) → ModuleTyped (canonModule ds)`,
-- via extract-commute + AllFunsTyped-transport (canon-pres-ᶜ + poly-ctx transport).
------------------------------------------------------------------------

postulate
  -- The IMPORT case (residual): a module with `DImport`s inlines its imports'
  -- signatures, so `extractFunctions mR` differs from the own-module
  -- canonicalization and resolution can fail if the `ModuleMap` is incomplete.
  -- The import-free fragment is fully discharged below; this residual needs the
  -- Plan-0.50 import-aware machinery.
  resolver-preserves-typing-imports :
    ∀ (mm : ModuleMap) (mU : P.Module) (mt : AS.ModuleTyped mU)
    → MC.HasValidMain-decl mU mt
    → Σ-syntax P.Module (λ mR →
        (resolveImports mm mU ≡ inj₂ mR)
        × Σ-syntax (AS.ModuleTyped mR) (λ mt' → MC.HasValidMain-decl mR mt'))

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
canon-preserves-typing mm mU mt vmain = go (CR.noImports? (P.Module.decls mU))
  where
    ds = P.Module.decls mU
    mR = P.mkModule (map (canonDecl (polyDefNames ds) [] []) ds)
    go : _ → Σ-syntax P.Module (λ mR' →
           (resolveImports mm mU ≡ inj₂ mR')
           × Σ-syntax (AS.ModuleTyped mR') (λ mt' → MC.HasValidMain-decl mR' mt'))
    go (yes ni) = canonModule ds , res-eq , module-typed-and-valid ds mt vmain
      where res-eq = CR.resolveImports-ni mm ds ni
    go (no _) = resolver-preserves-typing-imports mm mU mt vmain
