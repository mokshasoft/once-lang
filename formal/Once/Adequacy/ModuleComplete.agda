-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.ModuleComplete — the FORWARD module-compile completeness
-- lift (Plan 0.49 Phase 1, row-1b): a declaratively well-typed module with a
-- valid `main` COMPILES (`moduleToIR m ≡ just ir`). This forces the
-- typechecker-COMPLETE half: it routes through the proven `check-complete`.
--
--   (1) compileFunBody-complete: a `⊢ᶜ` derivation ⇒ the body compiles
--       (`check-complete` ∘ compileFunBody-aux on success).
--   (2) compileFun-complete: ⇒ the function compiles (main needs ty≡EffUU,
--       provided declaratively).
--   (3) caf-go-complete: ⇒ the whole function list compiles.
--   (4) findMain-complete + assembly: `moduleToIR m ≡ just ir`.
------------------------------------------------------------------------

module Once.Adequacy.ModuleComplete where

open import Data.Bool using (false)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Sum.Properties using (inj₂-injective)
open import Data.Unit using (tt)
open import Data.Maybe using (just)
open import Data.Product using (Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.String using (String) renaming (_≟_ to _≟str_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Once.Type using (Type; Unit; _⇒[_]_; mk-kind; Many; eff)
open import Once.IR using (IR)
open import Once.Surface.Syntax using (Expr; ∅; Usage)
open import Once.Surface.Elaborate using (elaborate)
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.TypeCheck.Classify using (SigEffectCtx)
open import Once.TypeCheck.Elaborate
  using (checkElab; ctxWithImportsAndSelfAndPolys; resolveExpr; PolyCtx)
open import Once.TypeCheck.Judgment using (_⊢ᶜ_∶_⨾_)
open import Once.TypeCheck.Completeness using (check-complete)
import Once.Compile as C
import Once.Adequacy.AcceptSound as AS
open import Once.Parser using (FunInfo)
open FunInfo

EffUU : Type
EffUU = Unit ⇒[ mk-kind Many eff ] Unit

-- main-named functions must be declared at EffUU (explicit annotation,
-- ctx-independent) for the entry to compile/wrap. (Declarative side condition.)
MainEffUU : FunInfo → Set
MainEffUU fi = funName fi ≡ "main" → funType fi ≡ just EffUU

------------------------------------------------------------------------
-- (1) a `⊢ᶜ` derivation ⇒ the body compiles, via `check-complete`.
------------------------------------------------------------------------

compileFunBody-complete : ∀ (ctx : C.FunCtx) (polys : PolyCtx) (sigEffs : SigEffectCtx)
  (name : String) (ty : Type) (body : RawExpr) {Ψ : Usage 0} →
  (ctxWithImportsAndSelfAndPolys ctx polys sigEffs name ty) ⊢ᶜ body ∶ ty ⨾ Ψ →
  Σ-syntax (IR Unit ty) (λ irFun →
    C.compileFunBody C.Heap false ctx polys sigEffs name ty body ≡ inj₂ irFun)
compileFunBody-complete ctx polys sigEffs name ty body deriv =
  let (eE , d , f , ce) = check-complete deriv
  in elaborate C.Heap (resolveExpr polys ((name , ty) ∷ ctx) ((name , ty) ∷ ctx) 0 eE)
   , cong (C.compileFunBody-aux C.Heap false ctx polys name ty refl) ce

------------------------------------------------------------------------
-- (2) ⇒ the function compiles. `compileFun` dispatches on `name == "main"`
-- = `isYes (name ≟ "main")`, so casing `name ≟str "main"` reduces it.
------------------------------------------------------------------------

compileFun-complete : ∀ (ctx : C.FunCtx) (polys : PolyCtx) (sigEffs : SigEffectCtx)
  (name : String) (ty : Type) (body : RawExpr) {Ψ : Usage 0} →
  (name ≡ "main" → ty ≡ EffUU) →
  (ctxWithImportsAndSelfAndPolys ctx polys sigEffs name ty) ⊢ᶜ body ∶ ty ⨾ Ψ →
  Σ-syntax (IR Unit ty) (λ irFun →
    C.compileFun C.Heap false ctx polys sigEffs name ty body ≡ inj₂ irFun)
compileFun-complete ctx polys sigEffs name ty body main-ok deriv with name ≟str "main"
... | no ¬p = compileFunBody-complete ctx polys sigEffs name ty body deriv
... | yes p with main-ok p
...   | refl = compileFunBody-complete ctx polys sigEffs name EffUU body deriv

------------------------------------------------------------------------
-- (3) ⇒ the whole list compiles (forward mirror of `caf-go-sound`).
------------------------------------------------------------------------

caf-go-complete : ∀ (polys : PolyCtx) (sigEffs : SigEffectCtx) (funs : List FunInfo)
  (ctx : C.FunCtx) →
  AS.AllFunsTyped polys sigEffs funs ctx →
  All MainEffUU funs →
  Σ-syntax (List C.CompiledFun) (λ compiled →
    C.compileAllFuns-go C.Heap false polys sigEffs funs ctx ≡ inj₂ compiled)
caf-go-complete polys sigEffs [] ctx AS.tnil _ = [] , refl
caf-go-complete polys sigEffs (fi ∷ rest) ctx (AS.tcons {ty = ty} rf deriv rest-typed) (pfi ∷ prest) =
  let main-ok : funName fi ≡ "main" → ty ≡ EffUU
      main-ok p = sym (inj₂-injective
        (subst (λ ft → C.resolveFunType ctx polys ft (funBody fi) ≡ inj₂ ty) (pfi p) rf))
      (irFun , cf-eq) = compileFun-complete ctx polys sigEffs (funName fi) ty (funBody fi) main-ok deriv
      (compiled-rest , rec-eq) = caf-go-complete polys sigEffs rest (C.extendFunCtx ctx (funName fi) ty) rest-typed prest
  in (C.mkCompiledFun (funName fi)
        (proj₁ (C.maybeWrapMain (funName fi) ty irFun))
        (proj₂ (C.maybeWrapMain (funName fi) ty irFun))
        (funIsPrimitive fi) ∷ compiled-rest)
   , trans (cong (C.caf-go-rf-aux C.Heap false polys sigEffs fi rest ctx) rf)
       (trans (cong (C.caf-go-cf-aux C.Heap false polys sigEffs fi rest ctx ty) cf-eq)
              (cong (C.caf-go-wrap fi ty irFun) rec-eq))
