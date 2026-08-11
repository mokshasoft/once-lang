-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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
open import Data.List using (List; []; _∷_; map; length)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_; _×_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)

open import Once.Type using (Type)
open import Once.Parser using (FunInfo; PolyFunInfo)
open Once.Parser.FunInfo using (funName; funType; funBody; funIsPrimitive)
import Once.Compile as C
open import Once.TypeCheck.Classify using (PolyCtx; ctxWithImportsAndSelfAndPolys; ctxWithImportsAndPolys; NamedCtx)
open import Once.TypeCheck.Judgment using (_⊢ᶜ_∶_⨾_; _⊢ᵢ_∶_⨾_)
open import Once.TypeCheck.Elaborate using (inferElab; InferElabResult; checkElab; CheckElabResult; success; failure)
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.TypeCheck.Error using (renderError)
open import Once.TypeCheck.Soundness using (infer-sound; check-sound)
open import Once.TypeCheck.Completeness using (infer-complete; check-complete)
import Once.Adequacy.AcceptSound as AS
open import Once.Adequacy.CanonPreserve using (⊆ᵇ-nil)
open import Once.Adequacy.CanonPreserveMutual using (canon-pres-ᶜ; canon-pres-ᵢ; mkPIB)
open import Once.Adequacy.CanonPolyTransport using (canonPolysCtx; PInB; polys-transport-ᶜ; polys-transport-ᵢ)
open import Once.Adequacy.CanonExtract using (canonFI; canonFuns; canonPFI; canonPolys; canonBody)
-- D072: the oracle branch of `inferType` (reflect pieces used for the
-- source/canon inferElab-failure correspondence; CanonPrincipal for the
-- oracle's own invariance).
open import Once.Adequacy.CanonReflectMutual using (canon-reflects-ᵢ)
open import Once.Adequacy.CanonReflectPolyTransport using (polys-reflect-ᵢ)
import Once.TypeCheck.Principal as Principal
open import Once.Adequacy.CanonPrincipal using (principalGround-canon; principalGround-polys)
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
-- wraps `inferElab` (with, since D072, an oracle+checkElab fallback on failure),
-- and both components transport: `inferElab` via infer-sound/-complete around the
-- `⊢ᵢ` transports, the oracle via CanonPrincipal (pointwise invariance), and the
-- validating `checkElab` via check-sound/-complete around the `⊢ᶜ` transports.
-- `result-extract` mirrors `inferType`'s RHS so we reason about a plain function
-- instead of fighting its `with inferElab` opacity.

⊎-clash : ∀ {x : String} {y : Type} {Z : Set} → inj₁ x ≡ inj₂ y → Z
⊎-clash ()

inj₂-inj : ∀ {x y : Type} → _≡_ {A = String ⊎ Type} (inj₂ x) (inj₂ y) → x ≡ y
inj₂-inj refl = refl

result-extract : (nctx : NamedCtx) (body : RawExpr)
  → InferElabResult (NamedCtx.debruijn nctx) → String ⊎ Type
result-extract nctx body (success A _ _ _ _) = inj₂ A
result-extract nctx body (failure err) =
  C.inferType-validate nctx body ("Cannot infer type: " ++ renderError err)
    (Principal.principalGround nctx body)

inferType≡extract : ∀ (ctx : C.FunCtx) (polys : PolyCtx) (body : _)
  → C.inferType ctx polys body
    ≡ result-extract (ctxWithImportsAndPolys ctx polys) body
        (inferElab (ctxWithImportsAndPolys ctx polys) body)
inferType≡extract ctx polys body with inferElab (ctxWithImportsAndPolys ctx polys) body
... | success A Ψ eE d f = refl
... | failure err       = refl

-- Invert an `inferType-validate … ≡ inj₂ ty` (the D072 oracle branch).
itv-inv : ∀ (nctx : NamedCtx) (body : RawExpr) (msg : String)
    (m : Maybe Type) (ty : Type)
  → C.inferType-validate nctx body msg m ≡ inj₂ ty
  → m ≡ just ty ×
    ∃[ Ψ ] ∃[ eE ] ∃[ d ] ∃[ f ] checkElab nctx body ty ≡ success Ψ eE d f
itv-inv nctx body msg nothing ty ()
itv-inv nctx body msg (just T) ty eq with checkElab nctx body T in eqC
... | failure _ = ⊎-clash eq
... | success Ψ eE d f with eq
...   | refl = refl , Ψ , eE , d , f , eqC

-- Rebuild an `inferType ≡ inj₂ ty` from oracle-branch evidence.
itv-intro : ∀ (nctx : NamedCtx) (body : RawExpr) (msg : String) (ty : Type)
    {Ψ eE d f}
  → checkElab nctx body ty ≡ success Ψ eE d f
  → C.inferType-validate nctx body msg (just ty) ≡ inj₂ ty
itv-intro nctx body msg ty eqC rewrite eqC = refl

-- | Inversion of `inferType ≡ inj₂ ty`: either the bidirectional
-- elaborator inferred it, or the oracle proposed it and the verified
-- `checkElab` validated it (D072).
data InferTypeInv (nctx : NamedCtx) (body : RawExpr) (ty : Type) : Set where
  via-elab : ∀ {Ψ eE d f}
    → inferElab nctx body ≡ success ty Ψ eE d f
    → InferTypeInv nctx body ty
  via-oracle : ∀ {err Ψ eE d f}
    → inferElab nctx body ≡ failure err
    → Principal.principalGround nctx body ≡ just ty
    → checkElab nctx body ty ≡ success Ψ eE d f
    → InferTypeInv nctx body ty

inferType-inv : ∀ (ctx : C.FunCtx) (polys : PolyCtx) (body : RawExpr) (ty : Type)
  → C.inferType ctx polys body ≡ inj₂ ty
  → InferTypeInv (ctxWithImportsAndPolys ctx polys) body ty
inferType-inv ctx polys body ty eq =
  go (inferElab (ctxWithImportsAndPolys ctx polys) body) refl
  where
  nctx = ctxWithImportsAndPolys ctx polys
  go : (r : InferElabResult (NamedCtx.debruijn nctx))
     → inferElab nctx body ≡ r
     → InferTypeInv nctx body ty
  go (success A Ψ eE d f) eqI = goS (inj₂-inj re)
    where
    re : _≡_ {A = String ⊎ Type} (inj₂ A) (inj₂ ty)
    re = trans (sym (cong (result-extract nctx body) eqI))
           (trans (sym (inferType≡extract ctx polys body)) eq)
    goS : A ≡ ty → InferTypeInv nctx body ty
    goS refl = via-elab eqI
  go (failure err) eqI =
    go2 (itv-inv nctx body _ (Principal.principalGround nctx body) ty
          (trans (sym (cong (result-extract nctx body) eqI))
            (trans (sym (inferType≡extract ctx polys body)) eq)))
    where
    go2 : Principal.principalGround nctx body ≡ just ty ×
          (∃[ Ψ ] ∃[ eE ] ∃[ d ] ∃[ f ]
            checkElab nctx body ty ≡ success Ψ eE d f)
        → InferTypeInv nctx body ty
    go2 (mEq , Ψ , eE , d , f , eqC) = via-oracle eqI mEq eqC

-- `inferElab` success at the canonExpr'd body + canonPolys'd ctx ⇒ `inferType ≡ inj₂ ty`.
inferElab→inferType : ∀ (ctx : C.FunCtx) (polys : PolyCtx) (body : _) (ty : Type) {Ψ eE d f}
  → inferElab (ctxWithImportsAndPolys ctx polys) body ≡ success ty Ψ eE d f
  → C.inferType ctx polys body ≡ inj₂ ty
inferElab→inferType ctx polys body ty eqs =
  trans (inferType≡extract ctx polys body)
    (cong (result-extract (ctxWithImportsAndPolys ctx polys) body) eqs)

-- D072 oracle-branch transport helpers (shared by both primitivity
-- cases of `inferType-transport`; hoisted because a `where` cannot span
-- with-branches).
module _ (ctx : C.FunCtx) (polysU : List PolyFunInfo) (b : List String)
         (pib : PInB (C.buildPolyCtx polysU) b) (fi : FunInfo) (ty : Type) where

  private
    polysB = C.buildPolyCtx polysU
    polysC = canonPolysCtx b polysB
    nctxS = ctxWithImportsAndPolys ctx polysB
    nctxC = ctxWithImportsAndPolys ctx polysC
    wf = <-wellFounded (length polysB)

    clash : ∀ {A Ψ₁ eE₁ d₁ f₁ err} {Z : Set}
      → inferElab nctxS (funBody fi) ≡ success A Ψ₁ eE₁ d₁ f₁
      → inferElab nctxS (funBody fi) ≡ failure err → Z
    clash eqS eqF with trans (sym eqS) eqF
    ... | ()

  oracle-transport-prim : ∀ {err Ψ eE d f}
    → inferElab nctxS (funBody fi) ≡ failure err
    → Principal.principalGround nctxS (funBody fi) ≡ just ty
    → checkElab nctxS (funBody fi) ty ≡ success Ψ eE d f
    → C.inferType ctx polysC (funBody fi) ≡ inj₂ ty
  oracle-transport-prim eqF eqO eqC with inferElab nctxC (funBody fi) in eqI'
  ... | success A Ψ' eE' d' f' =
        clash (let _ , _ , _ , eqR = infer-complete
                     (polys-reflect-ᵢ b polysB pib wf
                       (infer-sound _ (funBody fi) eqI'))
               in eqR) eqF
  ... | failure err' =
        trans
          (cong (C.inferType-validate nctxC (funBody fi)
                  ("Cannot infer type: " ++ renderError err'))
            (trans (principalGround-polys ctx polysB b (funBody fi)) eqO))
          (itv-intro nctxC (funBody fi) _ ty
            (let _ , _ , _ , eqC' = check-complete
                   (polys-transport-ᶜ b polysB pib wf
                     (check-sound nctxS (funBody fi) ty eqC))
             in eqC'))

  oracle-transport-user : ∀ {err Ψ eE d f}
    → inferElab nctxS (funBody fi) ≡ failure err
    → Principal.principalGround nctxS (funBody fi) ≡ just ty
    → checkElab nctxS (funBody fi) ty ≡ success Ψ eE d f
    → C.inferType ctx polysC (canonExpr b [] [] (funBody fi)) ≡ inj₂ ty
  oracle-transport-user eqF eqO eqC
    with inferElab nctxC (canonExpr b [] [] (funBody fi)) in eqI'
  ... | success A Ψ' eE' d' f' =
        clash (let _ , _ , _ , eqR = infer-complete
                     (canon-reflects-ᵢ b (funBody fi) (⊆ᵇ-nil {b})
                       (polys-reflect-ᵢ b polysB pib wf
                         (infer-sound _ (canonExpr b [] [] (funBody fi)) eqI')))
               in eqR) eqF
  ... | failure err' =
        trans
          (cong (C.inferType-validate nctxC (canonExpr b [] [] (funBody fi))
                  ("Cannot infer type: " ++ renderError err'))
            (trans (principalGround-canon ctx polysB b (funBody fi)) eqO))
          (itv-intro nctxC (canonExpr b [] [] (funBody fi)) _ ty
            (let _ , _ , _ , eqC' = check-complete
                   (polys-transport-ᶜ b polysB pib wf
                     (canon-pres-ᶜ {ctx = nctxS} b (⊆ᵇ-nil {b}) (mkPIB pib)
                       (check-sound nctxS (funBody fi) ty eqC)))
             in eqC'))

inferType-transport :
  ∀ (ctx : C.FunCtx) (polysU : List PolyFunInfo) (b : List String)
    (pib : PInB (C.buildPolyCtx polysU) b) (fi : FunInfo) (ty : Type)
  → C.inferType ctx (C.buildPolyCtx polysU) (funBody fi) ≡ inj₂ ty
  → C.inferType ctx (C.buildPolyCtx (canonPolys b polysU)) (funBody (canonFI b fi)) ≡ inj₂ ty
inferType-transport ctx polysU b pib fi ty eq
  rewrite buildPolyCtx-canon b polysU
  with funIsPrimitive fi
     | inferType-inv ctx (C.buildPolyCtx polysU) (funBody fi) ty eq
-- Elaborator branch, PRIMITIVE body unchanged: only the poly context
-- canonicalizes.
... | true  | via-elab eqU =
      inferElab→inferType ctx (canonPolysCtx b (C.buildPolyCtx polysU)) (funBody fi) ty
        (let _ , _ , _ , eqR = infer-complete
               (polys-transport-ᵢ b (C.buildPolyCtx polysU) pib
                 (<-wellFounded (length (C.buildPolyCtx polysU))) (infer-sound _ (funBody fi) eqU))
         in eqR)
-- Elaborator branch, USER body: canonExpr on the body, then the poly
-- context canonicalizes.
... | false | via-elab eqU =
      inferElab→inferType ctx (canonPolysCtx b (C.buildPolyCtx polysU)) (canonExpr b [] [] (funBody fi)) ty
        (let _ , _ , _ , eqR = infer-complete
               (polys-transport-ᵢ b (C.buildPolyCtx polysU) pib
                 (<-wellFounded (length (C.buildPolyCtx polysU)))
                 (canon-pres-ᵢ b (⊆ᵇ-nil {b}) (mkPIB pib)
                   (infer-sound _ (funBody fi) eqU)))
         in eqR)
-- D072 oracle branch: the source inferElab failed, so the canon-side
-- one must fail too (a canon success would REFLECT to a source
-- success); then the oracle answer carries over by CanonPrincipal and
-- the validating checkElab transports through the ⊢ᶜ bridges.
... | true  | via-oracle eqF eqO eqC =
      oracle-transport-prim ctx polysU b pib fi ty eqF eqO eqC
... | false | via-oracle eqF eqO eqC =
      oracle-transport-user ctx polysU b pib fi ty eqF eqO eqC

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
... | true  = polys-transport-ᶜ b (C.buildPolyCtx polysU) pib
                (<-wellFounded (length (C.buildPolyCtx polysU))) jud
... | false = polys-transport-ᶜ b (C.buildPolyCtx polysU) pib
                (<-wellFounded (length (C.buildPolyCtx polysU)))
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
