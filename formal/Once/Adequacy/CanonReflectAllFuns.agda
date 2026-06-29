-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.CanonReflectAllFuns — Plan 0.51 reverse `AllFunsTyped` transport.
--
-- The mirror of `CanonAllFuns.AllFunsTyped-transport`: each function's `⊢ᶜ`
-- derivation REFLECTS from the canonExpr'd poly context back to the original.
-- `body-reflect` = `polys-reflect-ᶜ` (move polys back) then `canon-reflects-ᶜ`
-- (un-canonicalize the body). This is where the load-bearing
-- `CanonReflectMutual.canon-reflects-ᶜ` is CONSUMED — so it is no longer an
-- island: the typechecker enforces that its signature plugs into the reverse
-- `body-transport` slot.
--
-- SCAFFOLD (feedback_scaffold_then_discharge): `polys-reflect-ᶜ` (reverse of
-- `CanonPolyTransport.polys-transport-ᶜ`) and `inferType-reflect` (reverse of
-- `CanonAllFuns.inferType-transport`) are NAMED temporary postulates — the
-- poly-context-transport reversals, to be discharged by mirroring those forwards.
------------------------------------------------------------------------

module Once.Adequacy.CanonReflectAllFuns where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Once.Type using (Type)
open import Once.Parser using (FunInfo; PolyFunInfo)
open Once.Parser.FunInfo using (funName; funType; funBody; funIsPrimitive)
import Once.Compile as C
open import Once.TypeCheck.Classify
  using (PolyCtx; NamedCtx; mkCtx; ctxWithImportsAndSelfAndPolys)
open import Once.TypeCheck.Judgment using (_⊢ᶜ_∶_⨾_; _⊢ᵢ_∶_⨾_)
open import Once.TypeCheck.Soundness using (infer-sound)
open import Once.TypeCheck.Completeness using (infer-complete)
open import Once.Parser.Module.Resolve using (canonExpr)
import Once.Adequacy.AcceptSound as AS
open import Once.Adequacy.CanonPreserve using (⊆ᵇ-nil)
open import Once.Adequacy.CanonPolyTransport using (canonPolysCtx; PInB)
open import Once.Adequacy.CanonExtract using (canonFI; canonFuns; canonPolys)
open import Once.Adequacy.CanonAllFuns using (buildPolyCtx-canon; inferType→inferElab; inferElab→inferType)
open import Once.Adequacy.CanonReflectMutual using (canon-reflects-ᶜ; canon-reflects-ᵢ)
open import Once.Adequacy.CanonReflectPolyTransport using (polys-reflect-ᶜ; polys-reflect-ᵢ)
open import Once.Adequacy.ModuleComplete using (AllMainEffUU; MainExists)

------------------------------------------------------------------------
-- Reverse of `CanonAllFuns.inferType-transport`: invert to inferElab, run
-- infer-sound, REFLECT the `⊢ᵢ` (polys-reflect-ᵢ then, for user bodies,
-- canon-reflects-ᵢ), then infer-complete back. Reuses the forward inferElab
-- bridge helpers (inferType→inferElab / inferElab→inferType).
------------------------------------------------------------------------

inferType-reflect : ∀ (ctx : C.FunCtx) (polysU : List PolyFunInfo) (b : List String)
  → PInB (C.buildPolyCtx polysU) b → (fi : FunInfo) (ty : Type)
  → C.inferType ctx (C.buildPolyCtx (canonPolys b polysU)) (funBody (canonFI b fi)) ≡ inj₂ ty
  → C.inferType ctx (C.buildPolyCtx polysU) (funBody fi) ≡ inj₂ ty
inferType-reflect ctx polysU b pib fi ty eq
  with funIsPrimitive fi
     | inferType→inferElab ctx (canonPolysCtx b (C.buildPolyCtx polysU)) (funBody (canonFI b fi)) ty
         (subst (λ P → C.inferType ctx P (funBody (canonFI b fi)) ≡ inj₂ ty) (buildPolyCtx-canon b polysU) eq)
... | true  | _ , _ , _ , _ , eqC =
        inferElab→inferType ctx (C.buildPolyCtx polysU) (funBody fi) ty
          (let _ , _ , _ , eqU = infer-complete
                 (polys-reflect-ᵢ b (C.buildPolyCtx polysU) pib (infer-sound _ (funBody fi) eqC))
           in eqU)
... | false | _ , _ , _ , _ , eqC =
        inferElab→inferType ctx (C.buildPolyCtx polysU) (funBody fi) ty
          (let _ , _ , _ , eqU = infer-complete
                 (canon-reflects-ᵢ b (funBody fi) (⊆ᵇ-nil {b})
                   (polys-reflect-ᵢ b (C.buildPolyCtx polysU) pib
                     (infer-sound _ (canonExpr b [] [] (funBody fi)) eqC)))
           in eqU)

------------------------------------------------------------------------
-- resolveFunType / body reflect (mirror of the forward transports).
------------------------------------------------------------------------

resolveFunType-reflect :
  ∀ (ctx : C.FunCtx) (polysU : List PolyFunInfo) (b : List String)
    (pib : PInB (C.buildPolyCtx polysU) b) (fi : FunInfo) (ty : Type)
  → C.resolveFunType ctx (C.buildPolyCtx (canonPolys b polysU))
      (funType (canonFI b fi)) (funBody (canonFI b fi)) ≡ inj₂ ty
  → C.resolveFunType ctx (C.buildPolyCtx polysU) (funType fi) (funBody fi) ≡ inj₂ ty
resolveFunType-reflect ctx polysU b pib fi ty eq with funType fi
... | just ty' = eq
... | nothing  = inferType-reflect ctx polysU b pib fi ty eq

body-reflect :
  ∀ (b : List String) (polysU : List PolyFunInfo) (sigEffs : _) (ctx : C.FunCtx)
    (pib : PInB (C.buildPolyCtx polysU) b) (fi : FunInfo) (ty : Type) {Ψ}
  → ctxWithImportsAndSelfAndPolys ctx (C.buildPolyCtx (canonPolys b polysU)) sigEffs (funName (canonFI b fi)) ty
      ⊢ᶜ funBody (canonFI b fi) ∶ ty ⨾ Ψ
  → ctxWithImportsAndSelfAndPolys ctx (C.buildPolyCtx polysU) sigEffs (funName fi) ty
      ⊢ᶜ funBody fi ∶ ty ⨾ Ψ
body-reflect b polysU sigEffs ctx pib fi ty jud
  rewrite buildPolyCtx-canon b polysU with funIsPrimitive fi
... | true  = polys-reflect-ᶜ b (C.buildPolyCtx polysU) pib jud
... | false = canon-reflects-ᶜ b (funBody fi) (⊆ᵇ-nil {b})
                (polys-reflect-ᶜ b (C.buildPolyCtx polysU) pib jud)

------------------------------------------------------------------------
-- The AllFunsTyped reflect + the main-validity predicates reflect.
------------------------------------------------------------------------

AllFunsTyped-reflect :
  ∀ {ctx : C.FunCtx} (b : List String) (polysU : List PolyFunInfo) (sigEffs : _)
  → PInB (C.buildPolyCtx polysU) b → (funs : List FunInfo)
  → AS.AllFunsTyped (C.buildPolyCtx (canonPolys b polysU)) sigEffs (canonFuns b funs) ctx
  → AS.AllFunsTyped (C.buildPolyCtx polysU) sigEffs funs ctx
AllFunsTyped-reflect b polysU sigEffs pib [] AS.tnil = AS.tnil
AllFunsTyped-reflect {ctx} b polysU sigEffs pib (fi ∷ rest) (AS.tcons {ty = ty} rft jud rest-typed) =
  AS.tcons (resolveFunType-reflect ctx polysU b pib fi ty rft)
           (body-reflect b polysU sigEffs ctx pib fi ty jud)
           (AllFunsTyped-reflect b polysU sigEffs pib rest rest-typed)

AllMainEffUU-reflect :
  ∀ {ctx : C.FunCtx} (b : List String) (polysU : List PolyFunInfo) (sigEffs : _)
    (pib : PInB (C.buildPolyCtx polysU) b) (funs : List FunInfo)
    (mt : AS.AllFunsTyped (C.buildPolyCtx (canonPolys b polysU)) sigEffs (canonFuns b funs) ctx)
  → AllMainEffUU mt → AllMainEffUU (AllFunsTyped-reflect b polysU sigEffs pib funs mt)
AllMainEffUU-reflect b polysU sigEffs pib [] AS.tnil amu = amu
AllMainEffUU-reflect b polysU sigEffs pib (fi ∷ rest) (AS.tcons rft jud rest-typed) (main-ok , prest) =
  main-ok , AllMainEffUU-reflect b polysU sigEffs pib rest rest-typed prest

MainExists-reflect :
  ∀ {ctx : C.FunCtx} (b : List String) (polysU : List PolyFunInfo) (sigEffs : _)
    (pib : PInB (C.buildPolyCtx polysU) b) (funs : List FunInfo)
    (mt : AS.AllFunsTyped (C.buildPolyCtx (canonPolys b polysU)) sigEffs (canonFuns b funs) ctx)
  → MainExists mt → MainExists (AllFunsTyped-reflect b polysU sigEffs pib funs mt)
MainExists-reflect b polysU sigEffs pib [] AS.tnil ()
MainExists-reflect b polysU sigEffs pib (fi ∷ rest) (AS.tcons rft jud rest-typed) (inj₁ x) = inj₁ x
MainExists-reflect b polysU sigEffs pib (fi ∷ rest) (AS.tcons rft jud rest-typed) (inj₂ y) =
  inj₂ (MainExists-reflect b polysU sigEffs pib rest rest-typed y)
