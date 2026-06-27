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
open import Data.Product using (_,_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

open import Once.Type using (Type)
open import Once.Parser using (FunInfo; PolyFunInfo)
open Once.Parser.FunInfo using (funName; funType; funBody; funIsPrimitive)
import Once.Compile as C
open import Once.TypeCheck.Classify using (PolyCtx; ctxWithImportsAndSelfAndPolys; ctxWithImportsAndPolys)
open import Once.TypeCheck.Judgment using (_⊢ᶜ_∶_⨾_; _⊢ᵢ_∶_⨾_)
open import Once.TypeCheck.Elaborate using (inferElab; InferElabResult; success; failure)
open import Once.TypeCheck.Error using (renderError)
open import Once.TypeCheck.Soundness using (infer-sound)
open import Once.TypeCheck.Completeness using (infer-complete)
import Once.Adequacy.AcceptSound as AS
open import Once.Adequacy.CanonPreserve using (⊆ᵇ-nil)
open import Once.Adequacy.CanonPreserveMutual using (canon-pres-ᶜ; canon-pres-ᵢ; mkPIB)
open import Once.Adequacy.CanonPolyTransport using (canonPolysCtx; PInB; polys-transport-ᶜ; polys-transport-ᵢ)
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

-- The lone elaborator residual, DISCHARGED via the relational bridge: `inferType`
-- wraps `inferElab`, which agrees with the declarative `⊢ᵢ` (infer-sound /
-- infer-complete). `⊢ᵢ` is preserved by the resolver's body-canonicalization
-- (canon-pres-ᵢ) and poly-context canonicalization (polys-transport-ᵢ), so the
-- inferred TYPE rides. `result-extract` mirrors `inferType`'s RHS so we reason about
-- a plain function instead of fighting its `with inferElab` opacity.

⊎-clash : ∀ {x : String} {y : Type} {Z : Set} → inj₁ x ≡ inj₂ y → Z
⊎-clash ()

result-extract : ∀ {n} {Δ} → InferElabResult {n} Δ → String ⊎ Type
result-extract (success A _ _ _ _) = inj₂ A
result-extract (failure err)       = inj₁ ("Cannot infer type: " ++ renderError err)

inferType≡extract : ∀ (ctx : C.FunCtx) (polys : PolyCtx) (body : _)
  → C.inferType ctx polys body ≡ result-extract (inferElab (ctxWithImportsAndPolys ctx polys) body)
inferType≡extract ctx polys body with inferElab (ctxWithImportsAndPolys ctx polys) body
... | success A Ψ eE d f = refl
... | failure err       = refl

-- Invert `inferType … ≡ inj₂ ty` to the underlying `inferElab` success. Convert to
-- a `result-extract` statement FIRST (so `inferElab` appears transparently), THEN case.
inferType→inferElab : ∀ (ctx : C.FunCtx) (polys : PolyCtx) (body : _) (ty : Type)
  → C.inferType ctx polys body ≡ inj₂ ty
  → ∃[ Ψ ] ∃[ eE ] ∃[ d ] ∃[ f ] inferElab (ctxWithImportsAndPolys ctx polys) body ≡ success ty Ψ eE d f
inferType→inferElab ctx polys body ty eq =
  go (inferElab (ctxWithImportsAndPolys ctx polys) body) (trans (sym (inferType≡extract ctx polys body)) eq)
  where
    go : ∀ {n} {Δ} (r : InferElabResult {n} Δ)
       → result-extract r ≡ inj₂ ty
       → ∃[ Ψ ] ∃[ eE ] ∃[ d ] ∃[ f ] r ≡ success ty Ψ eE d f
    go (success A Ψ eE d f) re with re
    ... | refl = Ψ , eE , d , f , refl
    go (failure err) re = ⊎-clash re

-- `inferElab` success at the canonExpr'd body + canonPolys'd ctx ⇒ `inferType ≡ inj₂ ty`.
inferElab→inferType : ∀ (ctx : C.FunCtx) (polys : PolyCtx) (body : _) (ty : Type) {Ψ eE d f}
  → inferElab (ctxWithImportsAndPolys ctx polys) body ≡ success ty Ψ eE d f
  → C.inferType ctx polys body ≡ inj₂ ty
inferElab→inferType ctx polys body ty eqs =
  trans (inferType≡extract ctx polys body) (cong result-extract eqs)

inferType-transport :
  ∀ (ctx : C.FunCtx) (polysU : List PolyFunInfo) (b : List String)
    (pib : PInB (C.buildPolyCtx polysU) b) (fi : FunInfo) (ty : Type)
  → C.inferType ctx (C.buildPolyCtx polysU) (funBody fi) ≡ inj₂ ty
  → C.inferType ctx (C.buildPolyCtx (canonPolys b polysU)) (funBody (canonFI b fi)) ≡ inj₂ ty
inferType-transport ctx polysU b pib fi ty eq
  rewrite buildPolyCtx-canon b polysU with funIsPrimitive fi | inferType→inferElab ctx (C.buildPolyCtx polysU) (funBody fi) ty eq
-- PRIMITIVE body unchanged: only the poly context canonicalizes.
... | true  | Ψ , eE , d , f , eqU =
        inferElab→inferType ctx (canonPolysCtx b (C.buildPolyCtx polysU)) (funBody fi) ty
          (let _ , _ , _ , eqR = infer-complete
                 (polys-transport-ᵢ b (C.buildPolyCtx polysU) pib (infer-sound _ (funBody fi) eqU))
           in eqR)
-- USER body: canonExpr on the body, then the poly context canonicalizes.
... | false | Ψ , eE , d , f , eqU =
        inferElab→inferType ctx (canonPolysCtx b (C.buildPolyCtx polysU)) (canonExpr b [] [] (funBody fi)) ty
          (let _ , _ , _ , eqR = infer-complete
                 (polys-transport-ᵢ b (C.buildPolyCtx polysU) pib
                   (canon-pres-ᵢ b (⊆ᵇ-nil {b}) (mkPIB pib)
                     (infer-sound _ (funBody fi) eqU)))
           in eqR)

-- funType (canonFI b fi) = funType fi (record update). Signatured case ignores the
-- body + polys (definitional); no-sig case = inferType-transport.
resolveFunType-transport :
  ∀ (ctx : C.FunCtx) (polysU : List PolyFunInfo) (b : List String)
    (pib : PInB (C.buildPolyCtx polysU) b) (fi : FunInfo) (ty : Type)
  → C.resolveFunType ctx (C.buildPolyCtx polysU) (funType fi) (funBody fi) ≡ inj₂ ty
  → C.resolveFunType ctx (C.buildPolyCtx (canonPolys b polysU))
      (funType (canonFI b fi)) (funBody (canonFI b fi)) ≡ inj₂ ty
resolveFunType-transport ctx polysU b pib fi ty eq with funType fi
... | just ty' = eq
... | nothing  = inferType-transport ctx polysU b pib fi ty eq

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
  AS.tcons (resolveFunType-transport ctx polysU b pib fi ty rft)
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
