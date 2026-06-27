-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.CanonAllFuns — lift `AllFunsTyped` across the resolver.
--
-- Each function's `⊢ᶜ` derivation lifts from the original poly context to the
-- canonExpr'd one (`buildPolyCtx (canonPolys b polysU)`): USER bodies via
-- `canon-pres-ᶜ` (canonExpr) then `polys-transport-ᶜ` (move polys); PRIMITIVE
-- bodies (RVar name, unchanged) via `polys-transport-ᶜ` only. This makes the
-- whole poly-transport + canon-pres machinery load-bearing.
------------------------------------------------------------------------

module Once.Adequacy.CanonAllFuns where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Data.Sum using (inj₂)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Once.Type using (Type)
open import Once.Parser using (FunInfo; PolyFunInfo)
open Once.Parser.FunInfo using (funName; funType; funBody; funIsPrimitive)
import Once.Compile as C
open import Once.TypeCheck.Classify using (PolyCtx; ctxWithImportsAndSelfAndPolys)
open import Once.TypeCheck.Judgment using (_⊢ᶜ_∶_⨾_)
import Once.Adequacy.AcceptSound as AS
open import Once.Adequacy.CanonPreserve using (⊆ᵇ-nil)
open import Once.Adequacy.CanonPreserveMutual using (canon-pres-ᶜ; mkPIB)
open import Once.Adequacy.CanonPolyTransport using (canonPolysCtx; PInB; polys-transport-ᶜ)
open import Once.Adequacy.CanonExtract using (canonFI; canonFuns; canonPFI; canonPolys; canonBody)
open import Once.Parser.Module.Resolve using (canonExpr)

------------------------------------------------------------------------
-- buildPolyCtx commutes with canonPFI / canonPolysCtx.
------------------------------------------------------------------------

buildPolyCtx-canon : ∀ (b : List String) (ps : List PolyFunInfo)
  → C.buildPolyCtx (canonPolys b ps) ≡ canonPolysCtx b (C.buildPolyCtx ps)
buildPolyCtx-canon b [] = refl
buildPolyCtx-canon b (pfi ∷ rest) = cong (_ ∷_) (buildPolyCtx-canon b rest)

------------------------------------------------------------------------
-- resolveFunType transports (signatured = definitional; no-sig = inferType,
-- which is canonExpr+polys-invariant — the lone elaborator residual).
------------------------------------------------------------------------

postulate
  -- The lone elaborator residual: `inferType` is invariant under the resolver's
  -- body canonicalization + poly-context canonicalization (D007 no-sig functions).
  inferType-transport :
    ∀ (ctx : C.FunCtx) (polysU : List PolyFunInfo) (b : List String) (fi : FunInfo) (ty : Type)
    → C.inferType ctx (C.buildPolyCtx polysU) (funBody fi) ≡ inj₂ ty
    → C.inferType ctx (C.buildPolyCtx (canonPolys b polysU)) (funBody (canonFI b fi)) ≡ inj₂ ty

-- funType (canonFI b fi) = funType fi (record update). Signatured case ignores the
-- body + polys (definitional); no-sig case = inferType-transport.
resolveFunType-transport :
  ∀ (ctx : C.FunCtx) (polysU : List PolyFunInfo) (b : List String) (fi : FunInfo) (ty : Type)
  → C.resolveFunType ctx (C.buildPolyCtx polysU) (funType fi) (funBody fi) ≡ inj₂ ty
  → C.resolveFunType ctx (C.buildPolyCtx (canonPolys b polysU))
      (funType (canonFI b fi)) (funBody (canonFI b fi)) ≡ inj₂ ty
resolveFunType-transport ctx polysU b fi ty eq with funType fi
... | just ty' = eq
... | nothing  = inferType-transport ctx polysU b fi ty eq

------------------------------------------------------------------------
-- The AllFunsTyped transport.
------------------------------------------------------------------------

-- Lift one function body's derivation to the canonExpr'd poly context.
body-transport :
  ∀ (b : List String) (polysU : List PolyFunInfo) (sigEffs : _) (ctx : C.FunCtx)
    (pib : PInB (C.buildPolyCtx polysU) b) (fi : FunInfo) (ty : Type) {Ψ}
  → ctxWithImportsAndSelfAndPolys ctx (C.buildPolyCtx polysU) sigEffs (funName fi) ty
      ⊢ᶜ funBody fi ∶ ty ⨾ Ψ
  → ctxWithImportsAndSelfAndPolys ctx (C.buildPolyCtx (canonPolys b polysU)) sigEffs (funName (canonFI b fi)) ty
      ⊢ᶜ funBody (canonFI b fi) ∶ ty ⨾ Ψ
body-transport b polysU sigEffs ctx pib fi ty jud
  rewrite buildPolyCtx-canon b polysU with funIsPrimitive fi
... | true  = polys-transport-ᶜ b (C.buildPolyCtx polysU) pib jud
... | false = polys-transport-ᶜ b (C.buildPolyCtx polysU) pib
                (canon-pres-ᶜ {ctx = ctxWithImportsAndSelfAndPolys ctx (C.buildPolyCtx polysU) sigEffs (funName fi) ty}
                  b (⊆ᵇ-nil {b}) (mkPIB pib) jud)

AllFunsTyped-transport :
  ∀ {ctx : C.FunCtx} (b : List String) (polysU : List PolyFunInfo) (sigEffs : _)
  → PInB (C.buildPolyCtx polysU) b → (funs : List FunInfo)
  → AS.AllFunsTyped (C.buildPolyCtx polysU) sigEffs funs ctx
  → AS.AllFunsTyped (C.buildPolyCtx (canonPolys b polysU)) sigEffs (canonFuns b funs) ctx
AllFunsTyped-transport b polysU sigEffs pib [] AS.tnil = AS.tnil
AllFunsTyped-transport {ctx} b polysU sigEffs pib (fi ∷ rest) (AS.tcons {ty = ty} rft jud rest-typed) =
  AS.tcons (resolveFunType-transport ctx polysU b fi ty rft)
           (body-transport b polysU sigEffs ctx pib fi ty jud)
           (AllFunsTyped-transport b polysU sigEffs pib rest rest-typed)

------------------------------------------------------------------------
-- The main-validity predicates transport (they read only funName /
-- funIsPrimitive / ty, all preserved by canonFI).
------------------------------------------------------------------------

open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Once.Adequacy.ModuleComplete using (AllMainEffUU; MainExists)

AllMainEffUU-transport :
  ∀ {ctx : C.FunCtx} (b : List String) (polysU : List PolyFunInfo) (sigEffs : _)
    (pib : PInB (C.buildPolyCtx polysU) b) (funs : List FunInfo)
    (mt : AS.AllFunsTyped (C.buildPolyCtx polysU) sigEffs funs ctx)
  → AllMainEffUU mt → AllMainEffUU (AllFunsTyped-transport b polysU sigEffs pib funs mt)
AllMainEffUU-transport b polysU sigEffs pib [] AS.tnil amu = amu
AllMainEffUU-transport b polysU sigEffs pib (fi ∷ rest) (AS.tcons rft jud rest-typed) (main-ok , prest) =
  main-ok , AllMainEffUU-transport b polysU sigEffs pib rest rest-typed prest

MainExists-transport :
  ∀ {ctx : C.FunCtx} (b : List String) (polysU : List PolyFunInfo) (sigEffs : _)
    (pib : PInB (C.buildPolyCtx polysU) b) (funs : List FunInfo)
    (mt : AS.AllFunsTyped (C.buildPolyCtx polysU) sigEffs funs ctx)
  → MainExists mt → MainExists (AllFunsTyped-transport b polysU sigEffs pib funs mt)
MainExists-transport b polysU sigEffs pib (fi ∷ rest) (AS.tcons rft jud rest-typed) (inj₁ x) = inj₁ x
MainExists-transport b polysU sigEffs pib (fi ∷ rest) (AS.tcons rft jud rest-typed) (inj₂ y) =
  inj₂ (MainExists-transport b polysU sigEffs pib rest rest-typed y)
