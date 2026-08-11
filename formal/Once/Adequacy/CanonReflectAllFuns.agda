-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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
-- (Historical note: `polys-reflect-ᶜ` and `inferType-reflect` began as
-- scaffold postulates; both are REAL PROOFS now — the latter including
-- the D072 oracle branch. No postulates remain in this module.)
------------------------------------------------------------------------

module Once.Adequacy.CanonReflectAllFuns where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Once.Type using (Type)
open import Once.Parser using (FunInfo; PolyFunInfo)
open Once.Parser.FunInfo using (funName; funType; funBody; funIsPrimitive)
import Once.Compile as C
open import Once.TypeCheck.Classify
  using (PolyCtx; NamedCtx; mkCtx; ctxWithImportsAndSelfAndPolys; ctxWithImportsAndPolys)
open import Once.TypeCheck.Elaborate
  using (inferElab; InferElabResult; checkElab; success; failure)
open import Once.TypeCheck.Error using (renderError)
open import Once.TypeCheck.Judgment using (_⊢ᶜ_∶_⨾_; _⊢ᵢ_∶_⨾_)
open import Once.TypeCheck.Soundness using (infer-sound; check-sound)
open import Once.TypeCheck.Completeness using (infer-complete; check-complete)
open import Once.Parser.Module.Resolve using (canonExpr)
import Once.Adequacy.AcceptSound as AS
open import Once.Adequacy.CanonPreserve using (⊆ᵇ-nil)
open import Once.Adequacy.CanonExtract using (canonFI; canonFuns; canonPolys)
open import Once.Adequacy.CanonAllFuns
  using (buildPolyCtx-canon; inferElab→inferType;
         inferType-inv; InferTypeInv; via-elab; via-oracle; itv-intro)
open import Once.Adequacy.CanonPreserveMutual using (canon-pres-ᶜ; canon-pres-ᵢ; mkPIB)
open import Once.Adequacy.CanonPolyTransport
  using (canonPolysCtx; PInB; polys-transport-ᶜ; polys-transport-ᵢ)
import Once.TypeCheck.Principal as Principal
open import Once.Adequacy.CanonPrincipal using (principalGround-canon; principalGround-polys)
open import Once.Adequacy.CanonReflectMutual using (canon-reflects-ᶜ; canon-reflects-ᵢ)
open import Once.Adequacy.CanonReflectPolyTransport using (polys-reflect-ᶜ; polys-reflect-ᵢ)
open import Once.Adequacy.ModuleComplete using (AllMainEffUU; MainExists)

------------------------------------------------------------------------
-- Reverse of `CanonAllFuns.inferType-transport`: invert to inferElab, run
-- infer-sound, REFLECT the `⊢ᵢ` (polys-reflect-ᵢ then, for user bodies,
-- canon-reflects-ᵢ), then infer-complete back. Reuses the forward inferElab
-- bridge helpers (inferType→inferElab / inferElab→inferType).
------------------------------------------------------------------------

-- D072 oracle-branch reflect helpers (mirrors of
-- CanonAllFuns.oracle-transport-*; hoisted for the same where-scope
-- reason).
module _ (ctx : C.FunCtx) (polysU : List PolyFunInfo) (b : List String)
         (pib : PInB (C.buildPolyCtx polysU) b) (fi : FunInfo) (ty : Type) where

  private
    polysB = C.buildPolyCtx polysU
    polysC = canonPolysCtx b polysB
    nctxS = ctxWithImportsAndPolys ctx polysB
    nctxC = ctxWithImportsAndPolys ctx polysC
    wf = <-wellFounded (length polysB)

    clashC : ∀ (body : _) {A Ψ₁ eE₁ d₁ f₁ err} {Z : Set}
      → inferElab nctxC body ≡ success A Ψ₁ eE₁ d₁ f₁
      → inferElab nctxC body ≡ failure err → Z
    clashC body eqS eqF with trans (sym eqS) eqF
    ... | ()

  oracle-reflect-prim : ∀ {err Ψ eE d f}
    → inferElab nctxC (funBody fi) ≡ failure err
    → Principal.principalGround nctxC (funBody fi) ≡ just ty
    → checkElab nctxC (funBody fi) ty ≡ success Ψ eE d f
    → C.inferType ctx polysB (funBody fi) ≡ inj₂ ty
  oracle-reflect-prim eqF eqO eqC with inferElab nctxS (funBody fi) in eqI'
  ... | success A Ψ' eE' d' f' =
        clashC (funBody fi)
          (let _ , _ , _ , eqR = infer-complete
                 (polys-transport-ᵢ b polysB pib wf
                   (infer-sound _ (funBody fi) eqI'))
           in eqR) eqF
  ... | failure err' =
        trans
          (cong (C.inferType-validate nctxS (funBody fi)
                  ("Cannot infer type: " ++ renderError err'))
            (trans (sym (principalGround-polys ctx polysB b (funBody fi))) eqO))
          (itv-intro nctxS (funBody fi) _ ty
            (let _ , _ , _ , eqC' = check-complete
                   (polys-reflect-ᶜ b polysB pib wf
                     (check-sound nctxC (funBody fi) ty eqC))
             in eqC'))

  oracle-reflect-user : ∀ {err Ψ eE d f}
    → inferElab nctxC (canonExpr b [] [] (funBody fi)) ≡ failure err
    → Principal.principalGround nctxC (canonExpr b [] [] (funBody fi)) ≡ just ty
    → checkElab nctxC (canonExpr b [] [] (funBody fi)) ty ≡ success Ψ eE d f
    → C.inferType ctx polysB (funBody fi) ≡ inj₂ ty
  oracle-reflect-user eqF eqO eqC with inferElab nctxS (funBody fi) in eqI'
  ... | success A Ψ' eE' d' f' =
        clashC (canonExpr b [] [] (funBody fi))
          (let _ , _ , _ , eqR = infer-complete
                 (polys-transport-ᵢ b polysB pib wf
                   (canon-pres-ᵢ b (⊆ᵇ-nil {b}) (mkPIB pib)
                     (infer-sound _ (funBody fi) eqI')))
           in eqR) eqF
  ... | failure err' =
        trans
          (cong (C.inferType-validate nctxS (funBody fi)
                  ("Cannot infer type: " ++ renderError err'))
            (trans (sym (principalGround-canon ctx polysB b (funBody fi))) eqO))
          (itv-intro nctxS (funBody fi) _ ty
            (let _ , _ , _ , eqC' = check-complete
                   (canon-reflects-ᶜ b (funBody fi) (⊆ᵇ-nil {b})
                     (polys-reflect-ᶜ b polysB pib wf
                       (check-sound nctxC (canonExpr b [] [] (funBody fi)) ty eqC)))
             in eqC'))

inferType-reflect : ∀ (ctx : C.FunCtx) (polysU : List PolyFunInfo) (b : List String)
  → PInB (C.buildPolyCtx polysU) b → (fi : FunInfo) (ty : Type)
  → C.inferType ctx (C.buildPolyCtx (canonPolys b polysU)) (funBody (canonFI b fi)) ≡ inj₂ ty
  → C.inferType ctx (C.buildPolyCtx polysU) (funBody fi) ≡ inj₂ ty
inferType-reflect ctx polysU b pib fi ty eq
  with funIsPrimitive fi
     | inferType-inv ctx (canonPolysCtx b (C.buildPolyCtx polysU)) (funBody (canonFI b fi)) ty
         (subst (λ P → C.inferType ctx P (funBody (canonFI b fi)) ≡ inj₂ ty) (buildPolyCtx-canon b polysU) eq)
... | true  | via-elab eqCS =
        inferElab→inferType ctx (C.buildPolyCtx polysU) (funBody fi) ty
          (let _ , _ , _ , eqU = infer-complete
                 (polys-reflect-ᵢ b (C.buildPolyCtx polysU) pib
                   (<-wellFounded (length (C.buildPolyCtx polysU))) (infer-sound _ (funBody fi) eqCS))
           in eqU)
... | false | via-elab eqCS =
        inferElab→inferType ctx (C.buildPolyCtx polysU) (funBody fi) ty
          (let _ , _ , _ , eqU = infer-complete
                 (canon-reflects-ᵢ b (funBody fi) (⊆ᵇ-nil {b})
                   (polys-reflect-ᵢ b (C.buildPolyCtx polysU) pib
                     (<-wellFounded (length (C.buildPolyCtx polysU)))
                     (infer-sound _ (canonExpr b [] [] (funBody fi)) eqCS)))
           in eqU)
... | true  | via-oracle eqF eqO eqC =
        oracle-reflect-prim ctx polysU b pib fi ty eqF eqO eqC
... | false | via-oracle eqF eqO eqC =
        oracle-reflect-user ctx polysU b pib fi ty eqF eqO eqC

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
... | true  = polys-reflect-ᶜ b (C.buildPolyCtx polysU) pib
                (<-wellFounded (length (C.buildPolyCtx polysU))) jud
... | false = canon-reflects-ᶜ b (funBody fi) (⊆ᵇ-nil {b})
                (polys-reflect-ᶜ b (C.buildPolyCtx polysU) pib
                  (<-wellFounded (length (C.buildPolyCtx polysU))) jud)

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
