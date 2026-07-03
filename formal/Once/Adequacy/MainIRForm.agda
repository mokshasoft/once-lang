-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.MainIRForm — discharge of `main-ir-form` (Plan 0.49 Phase 1).
--
-- `moduleToIR m ≡ just ir → ir ≡ wrapMainAsEntry (elaborate Heap seR)`: the
-- compiled `main` IR is the entry-wrap of the elaborated resolved surface term.
-- Built bottom-up:
--   (1) validateMain inversion: a successfully-compiled `main` has type EffUU.
--   (2) compileFunBody form: its IR is `elaborate Heap (resolveExpr se)`.
--   (3) compileAllFuns-go value-tracking induction: the main entry's `cfIR`.
--   (4) moduleToIR / findMain inversion: assemble.
------------------------------------------------------------------------

module Once.Adequacy.MainIRForm where

open import Data.Bool using (Bool; false; true)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Sum.Properties using (inj₂-injective)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.List using (List; []; _∷_)
open import Data.String using (String) renaming (_≟_ to _≟str_)
open import Once.CanonicalName using (CanonicalName; bare) renaming (_≟ᶜ_ to _≟cn_)
open import Relation.Nullary using (yes; no; ¬_; Dec)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Once.Adequacy.SourceTrace
  using (findMain; findMain-here; isUnit?; moduleToIR; moduleToIR-aux)

open import Once.Type
  using (Type; Unit; Void; Int; Float; Str; Buffer; _*_; _+_; _⇒[_]_;
         μ-type; ν-type; mk-kind; Quantity; Zero; One; Many; Purity; pure; eff)
open import Once.IR using (IR)
open import Once.Surface.Syntax using (Expr; ∅; Usage)
open import Once.Surface.Elaborate using (elaborate)
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.TypeCheck.Classify using (SigEffectCtx; NamedCtx; Imports)
open import Once.TypeCheck.Elaborate
  using (checkElab; ctxWithImportsAndSelfAndPolys; resolveExpr; PolyCtx;
         CheckElabResult; success)
import Once.Compile as C
import Once.Adequacy.AcceptSound as AS
open import Once.Parser using (FunInfo)
open FunInfo

EffUU : Type
EffUU = Unit ⇒[ mk-kind Many eff ] Unit

------------------------------------------------------------------------
-- Plan 0.55: the strengthened extraction payload. Besides the resolved
-- surface term `seR` (whose elaboration is `main`'s IR), carry the `checkElab`
-- witness `ce` and the resolver arguments, so `MainRealizeAgrees.main-extract`
-- can (i) identify `seR` with `resolveExpr … se` and (ii) recover the typing
-- derivation via `check-sound ce`. All of these are already computed inside
-- `compileFunBody-form`; the payload just stops discarding them.
------------------------------------------------------------------------

-- The main function's checkElab context is `ctxWithImportsAndSelfAndPolys ctx
-- polys sigEffs "main" EffUU`, which has `size 0` / `debruijn ∅` — so `se : Expr
-- ∅ Ψ EffUU` (`Ψ : Usage 0`) and the syntactic `seR ≡ resolveExpr … se` both
-- typecheck. We bind the components (`ctx polys sigEffs`) rather than an abstract
-- `cctx`, so those size/debruijn reductions are available.
Payload : (Ψ : Usage 0) → Expr ∅ Ψ EffUU → Set
Payload Ψ seR =
  Σ-syntax C.FunCtx (λ ctx → Σ-syntax PolyCtx (λ polys → Σ-syntax SigEffectCtx (λ sigEffs →
  Σ-syntax RawExpr (λ body →
  Σ-syntax (Expr ∅ Ψ EffUU) (λ se →
  Σ-syntax ℕ (λ d → Σ-syntax ℕ (λ f →
  Σ-syntax (checkElab (ctxWithImportsAndSelfAndPolys ctx polys sigEffs "main" EffUU) body EffUU
             ≡ success Ψ se d f) (λ ce →
    seR ≡ resolveExpr polys (("main" , EffUU) ∷ ctx) (("main" , EffUU) ∷ ctx) 0 se))))))))

-- Body-level form (before entry-wrap): `irFun ≡ elaborate Heap seR` + payload.
BodyForm : IR Unit EffUU → Set
BodyForm irFun =
  Σ-syntax (Usage 0) (λ Ψ → Σ-syntax (Expr ∅ Ψ EffUU) (λ seR →
    (irFun ≡ elaborate C.Heap seR) × Payload Ψ seR))

------------------------------------------------------------------------
-- (1) validateMain inversion: `validateMain ty ≡ inj₂ tt → ty ≡ EffUU`.
-- Every non-EffUU `ty` has a concrete mismatching component, so
-- `validateMain ty` reduces to `inj₁ …` and the equation is absurd.
------------------------------------------------------------------------

validateMain-EffUU : ∀ (ty : Type) → C.validateMain ty ≡ inj₂ tt → ty ≡ EffUU
validateMain-EffUU (Unit ⇒[ mk-kind Many eff ] Unit) eq = refl
-- non-arrow heads
validateMain-EffUU Unit       ()
validateMain-EffUU Void       ()
validateMain-EffUU Int        ()
validateMain-EffUU Float      ()
validateMain-EffUU Str        ()
validateMain-EffUU Buffer     ()
validateMain-EffUU (_ * _)    ()
validateMain-EffUU (_ + _)    ()
validateMain-EffUU (μ-type _) ()
validateMain-EffUU (ν-type _) ()
-- arrow with domain Unit, kind (Many,eff), but codomain ≠ Unit
validateMain-EffUU (Unit ⇒[ mk-kind Many eff ] Void)         ()
validateMain-EffUU (Unit ⇒[ mk-kind Many eff ] Int)          ()
validateMain-EffUU (Unit ⇒[ mk-kind Many eff ] Float)        ()
validateMain-EffUU (Unit ⇒[ mk-kind Many eff ] Str)          ()
validateMain-EffUU (Unit ⇒[ mk-kind Many eff ] Buffer)       ()
validateMain-EffUU (Unit ⇒[ mk-kind Many eff ] (_ * _))      ()
validateMain-EffUU (Unit ⇒[ mk-kind Many eff ] (_ + _))      ()
validateMain-EffUU (Unit ⇒[ mk-kind Many eff ] (_ ⇒[ _ ] _)) ()
validateMain-EffUU (Unit ⇒[ mk-kind Many eff ] (μ-type _))   ()
validateMain-EffUU (Unit ⇒[ mk-kind Many eff ] (ν-type _))   ()
-- arrow with domain Unit but kind ≠ (Many,eff)
validateMain-EffUU (Unit ⇒[ mk-kind Many pure ] B) ()
validateMain-EffUU (Unit ⇒[ mk-kind One π ] B)     ()
validateMain-EffUU (Unit ⇒[ mk-kind Zero π ] B)    ()
-- arrow with domain ≠ Unit
validateMain-EffUU (Void ⇒[ k ] B)         ()
validateMain-EffUU (Int ⇒[ k ] B)          ()
validateMain-EffUU (Float ⇒[ k ] B)        ()
validateMain-EffUU (Str ⇒[ k ] B)          ()
validateMain-EffUU (Buffer ⇒[ k ] B)       ()
validateMain-EffUU ((_ * _) ⇒[ k ] B)      ()
validateMain-EffUU ((_ + _) ⇒[ k ] B)      ()
validateMain-EffUU ((_ ⇒[ _ ] _) ⇒[ k ] B) ()
validateMain-EffUU ((μ-type _) ⇒[ k ] B)   ()
validateMain-EffUU ((ν-type _) ⇒[ k ] B)   ()

------------------------------------------------------------------------
-- (2) compileFunBody form: a successfully-compiled body (at EffUU, doOpt=false,
-- Heap) is `elaborate Heap (resolveExpr … se)` for the checkElab term `se`.
-- Reuses `AcceptSound.compileFunBody-aux-success` (inverts compileFunBody-aux).
------------------------------------------------------------------------

compileFunBody-form : ∀ (ctx : C.FunCtx) (polys : PolyCtx) (sigEffs : SigEffectCtx)
  (body : RawExpr) (irFun : IR Unit EffUU) →
  C.compileFunBody C.Heap false ctx polys sigEffs "main" EffUU body ≡ inj₂ irFun →
  BodyForm irFun
compileFunBody-form ctx polys sigEffs body irFun eq =
  let cr = checkElab (ctxWithImportsAndSelfAndPolys ctx polys sigEffs "main" EffUU) body EffUU
      (Ψ , se , d , f , ce) =
        AS.compileFunBody-aux-success false ctx polys "main" EffUU refl cr eq
      eq2 : C.compileFunBody-aux C.Heap false ctx polys "main" EffUU refl (success Ψ se d f)
            ≡ inj₂ irFun
      eq2 = subst (λ c → C.compileFunBody-aux C.Heap false ctx polys "main" EffUU refl c ≡ inj₂ irFun)
                  ce eq
  in Ψ , resolveExpr polys (("main" , EffUU) ∷ ctx) (("main" , EffUU) ∷ ctx) 0 se
       , sym (inj₂-injective eq2)
       , ctx , polys , sigEffs , body , se , d , f , ce , refl

------------------------------------------------------------------------
-- (3a) compileFun at "main": reduce through `validateMain`, and extract the
-- body form. Linchpin: `"main" == "main"` reduces to `true`.
------------------------------------------------------------------------

-- `compileFun "main" …` reduces to `compileFun-main-aux … (validateMain ty)`.
compileFun-main-reduces : ∀ (ctx : C.FunCtx) (polys : PolyCtx) (sigEffs : SigEffectCtx)
  (ty : Type) (body : RawExpr) →
  C.compileFun C.Heap false ctx polys sigEffs "main" ty body
  ≡ C.compileFun-main-aux C.Heap false ctx polys sigEffs "main" ty body (C.validateMain ty)
compileFun-main-reduces ctx polys sigEffs ty body = refl

-- A successfully-compiled "main" has type EffUU.
compileFun-main-EffUU : ∀ (ctx : C.FunCtx) (polys : PolyCtx) (sigEffs : SigEffectCtx)
  (ty : Type) (body : RawExpr) (irFun : IR Unit ty) →
  C.compileFun C.Heap false ctx polys sigEffs "main" ty body ≡ inj₂ irFun →
  ty ≡ EffUU
compileFun-main-EffUU ctx polys sigEffs ty body irFun eq with C.validateMain ty in veq
... | inj₂ tt  = validateMain-EffUU ty veq
... | inj₁ err = case eq of λ ()

-- At EffUU, `compileFun "main"` IS `compileFunBody` (validateMain EffUU ≡ inj₂ tt).
compileFun-main-formEffUU : ∀ (ctx : C.FunCtx) (polys : PolyCtx) (sigEffs : SigEffectCtx)
  (body : RawExpr) (irFun : IR Unit EffUU) →
  C.compileFun C.Heap false ctx polys sigEffs "main" EffUU body ≡ inj₂ irFun →
  BodyForm irFun
compileFun-main-formEffUU ctx polys sigEffs body irFun eq =
  compileFunBody-form ctx polys sigEffs body irFun eq

-- compileFun "main": success ⇒ ty≡EffUU AND the (coerced) IR is elaborate-of-resolved.
compileFun-main-form : ∀ (ctx : C.FunCtx) (polys : PolyCtx) (sigEffs : SigEffectCtx)
  (ty : Type) (body : RawExpr) (irFun : IR Unit ty) →
  C.compileFun C.Heap false ctx polys sigEffs "main" ty body ≡ inj₂ irFun →
  Σ-syntax (ty ≡ EffUU) (λ uty → BodyForm (subst (IR Unit) uty irFun))
compileFun-main-form ctx polys sigEffs ty body irFun eq
  with compileFun-main-EffUU ctx polys sigEffs ty body irFun eq
... | refl = refl , compileFun-main-formEffUU ctx polys sigEffs body irFun eq

------------------------------------------------------------------------
-- (3b) findMain dispatch helper: a head whose name ≠ "main" is skipped.
------------------------------------------------------------------------

findMain-here-no : ∀ (cf : C.CompiledFun) (b : Data.Bool.Bool)
  (mu : Maybe (C.CompiledFun.cfType cf ≡ Unit)) (cont : Maybe (IR Unit Unit))
  (¬p : ¬ (C.CompiledFun.cfName cf ≡ bare "main")) →
  findMain-here cf b (no ¬p) mu cont ≡ cont
findMain-here-no cf false mu cont ¬p = refl
findMain-here-no cf true  mu cont ¬p = refl

------------------------------------------------------------------------
-- (3c) The value-tracking induction over `compileAllFuns-go`: the `findMain`
-- result is the entry-wrap of the elaborated resolved main term.
------------------------------------------------------------------------

open C.CompiledFun using (cfType; cfName; cfIsPrimitive)

-- `bare` is injective (single-component CanonicalName), so a String name ≠
-- "main" lifts to its CanonicalName ≠ `bare "main"`.
bare-injective : ∀ {s t} → bare s ≡ bare t → s ≡ t
bare-injective refl = refl

-- A head whose name ≠ "main" is skipped by findMain. (Proven in its OWN goal,
-- where the `with`-abstraction of the stuck String-decidable applies — unlike a
-- freshly-built `subst` type, where it would not reduce.)
findMain-skip : ∀ (cf : C.CompiledFun) (rest : List C.CompiledFun) →
  ¬ (cfName cf ≡ bare "main") → findMain (cf ∷ rest) ≡ findMain rest
findMain-skip cf rest ¬p with cfName cf ≟cn bare "main"
... | yes p  = ⊥-elim (¬p p)
... | no ¬q  = findMain-here-no cf (cfIsPrimitive cf) (isUnit? (cfType cf)) (findMain rest) ¬q

-- A primitive head is skipped by findMain (regardless of name/type).
findMain-skip-prim : ∀ (cf : C.CompiledFun) (rest : List C.CompiledFun) →
  cfIsPrimitive cf ≡ true → findMain (cf ∷ rest) ≡ findMain rest
findMain-skip-prim cf rest pp rewrite pp = refl

Form : IR Unit Unit → Set
Form ir = Σ-syntax (Usage 0) (λ Ψ → Σ-syntax (Expr ∅ Ψ EffUU) (λ seR →
            (ir ≡ C.wrapMainAsEntry (elaborate C.Heap seR)) × Payload Ψ seR))

-- Plan 0.55: `caf-go-find-form` rewritten from nested `with … in` blocks into
-- top-level, explicit-scrutinee helpers (each takes the compile sub-result + its
-- `≡` equation as arguments). This makes it EXTERNALLY REDUCIBLE — so the
-- alignment lemma (`Once.Adequacy.MainAlign`) can drive it in lockstep with a
-- structural walk over `AllFunsTyped`. Behaviour-preserving vs the old version.
caf-go-find-form : ∀ (polys : PolyCtx) (sigEffs : SigEffectCtx) (funs : List FunInfo)
  (ctx : C.FunCtx) (compiled : List C.CompiledFun) (ir : IR Unit Unit) →
  C.compileAllFuns-go C.Heap false polys sigEffs funs ctx ≡ inj₂ compiled →
  findMain compiled ≡ just ir → Form ir

-- dispatch on the resolveFunType result
cff-rf : ∀ (polys : PolyCtx) (sigEffs : SigEffectCtx) (fi : FunInfo) (rest : List FunInfo)
  (ctx : C.FunCtx) (compiled : List C.CompiledFun) (ir : IR Unit Unit) (rfv : String ⊎ Type) →
  C.caf-go-rf-aux C.Heap false polys sigEffs fi rest ctx rfv ≡ inj₂ compiled →
  findMain compiled ≡ just ir → Form ir

-- dispatch on the compileFun result (keep `cf-conn` for the STOP extraction)
cff-cf : ∀ (polys : PolyCtx) (sigEffs : SigEffectCtx) (fi : FunInfo) (rest : List FunInfo)
  (ctx : C.FunCtx) (ty : Type) (compiled : List C.CompiledFun) (ir : IR Unit Unit)
  (cfv : String ⊎ IR Unit ty) →
  C.compileFun C.Heap false ctx polys sigEffs (funName fi) ty (funBody fi) ≡ cfv →
  C.caf-go-cf-aux C.Heap false polys sigEffs fi rest ctx ty cfv ≡ inj₂ compiled →
  findMain compiled ≡ just ir → Form ir

-- dispatch on the recursion result (keep `cf-conn`/`rec-conn`)
cff-rec : ∀ (polys : PolyCtx) (sigEffs : SigEffectCtx) (fi : FunInfo) (rest : List FunInfo)
  (ctx : C.FunCtx) (ty : Type) (irFun : IR Unit ty) (compiled : List C.CompiledFun) (ir : IR Unit Unit)
  (cf-conn : C.compileFun C.Heap false ctx polys sigEffs (funName fi) ty (funBody fi) ≡ inj₂ irFun)
  (recv : String ⊎ List C.CompiledFun) →
  C.compileAllFuns-go C.Heap false polys sigEffs rest (C.extendFunCtx ctx (funName fi) ty) ≡ recv →
  C.caf-go-wrap fi ty irFun recv ≡ inj₂ compiled →
  findMain compiled ≡ just ir → Form ir

-- dispatch on `name ≟ "main"` and the primitive flag. `nm`/`bdy`/`pb` are the
-- head's fields generalised to VARIABLES, so `yes refl` can refine `nm := "main"`.
cff-dispatch : ∀ (polys : PolyCtx) (sigEffs : SigEffectCtx) (nm : String) (bdy : RawExpr)
  (rest : List FunInfo) (ctx : C.FunCtx) (ty : Type) (irFun : IR Unit ty)
  (compiled-rest : List C.CompiledFun) (ir : IR Unit Unit) (pb : Bool)
  (cf-conn : C.compileFun C.Heap false ctx polys sigEffs nm ty bdy ≡ inj₂ irFun)
  (rec-conn : C.compileAllFuns-go C.Heap false polys sigEffs rest (C.extendFunCtx ctx nm ty) ≡ inj₂ compiled-rest)
  (fm : findMain (C.mkCompiledFun (bare nm) (proj₁ (C.maybeWrapMain nm ty irFun))
                    (proj₂ (C.maybeWrapMain nm ty irFun)) pb ∷ compiled-rest) ≡ just ir)
  (nd : Dec (nm ≡ "main")) → Form ir

-- STOP: `nm ≡ "main"`, non-primitive. `bf` is `compileFun-main-form`'s result.
cff-stop : ∀ (ctx : C.FunCtx) (polys : PolyCtx) (sigEffs : SigEffectCtx) (ty : Type) (bdy : RawExpr)
  (irFun : IR Unit ty) (compiled-rest : List C.CompiledFun) (ir : IR Unit Unit)
  (bf : Σ-syntax (ty ≡ EffUU) (λ uty → BodyForm (subst (IR Unit) uty irFun)))
  (fm : findMain (C.mkCompiledFun (bare "main") (proj₁ (C.maybeWrapMain "main" ty irFun))
                    (proj₂ (C.maybeWrapMain "main" ty irFun)) false ∷ compiled-rest) ≡ just ir)
  → Form ir

caf-go-find-form polys sigEffs [] ctx compiled ir caf-eq fm-eq =
  case subst (λ c → findMain c ≡ just ir) (sym (inj₂-injective caf-eq)) fm-eq of λ ()
caf-go-find-form polys sigEffs (fi ∷ rest) ctx compiled ir caf-eq fm-eq =
  cff-rf polys sigEffs fi rest ctx compiled ir
    (C.resolveFunType ctx polys (funType fi) (funBody fi)) caf-eq fm-eq

cff-rf polys sigEffs fi rest ctx compiled ir (inj₁ err) () fm-eq
cff-rf polys sigEffs fi rest ctx compiled ir (inj₂ ty) caf-eq fm-eq =
  cff-cf polys sigEffs fi rest ctx ty compiled ir
    (C.compileFun C.Heap false ctx polys sigEffs (funName fi) ty (funBody fi)) refl caf-eq fm-eq

cff-cf polys sigEffs fi rest ctx ty compiled ir (inj₁ err) cf-conn () fm-eq
cff-cf polys sigEffs fi rest ctx ty compiled ir (inj₂ irFun) cf-conn caf-eq fm-eq =
  cff-rec polys sigEffs fi rest ctx ty irFun compiled ir cf-conn
    (C.compileAllFuns-go C.Heap false polys sigEffs rest (C.extendFunCtx ctx (funName fi) ty)) refl
    caf-eq fm-eq

cff-rec polys sigEffs fi rest ctx ty irFun compiled ir cf-conn (inj₁ err) rec-conn () fm-eq
cff-rec polys sigEffs fi rest ctx ty irFun compiled ir cf-conn (inj₂ compiled-rest) rec-conn caf-eq fm-eq =
  cff-dispatch polys sigEffs (funName fi) (funBody fi) rest ctx ty irFun compiled-rest ir (funIsPrimitive fi)
    cf-conn rec-conn
    (subst (λ c → findMain c ≡ just ir) (sym (inj₂-injective caf-eq)) fm-eq)
    (funName fi ≟str "main")

cff-dispatch polys sigEffs nm bdy rest ctx ty irFun compiled-rest ir pb cf-conn rec-conn fm (no ¬p) =
  caf-go-find-form polys sigEffs rest (C.extendFunCtx ctx nm ty) compiled-rest ir rec-conn
    (trans (sym (findMain-skip
                   (C.mkCompiledFun (bare nm) (proj₁ (C.maybeWrapMain nm ty irFun))
                      (proj₂ (C.maybeWrapMain nm ty irFun)) pb) compiled-rest
                   (λ e → ¬p (bare-injective e))))
           fm)
cff-dispatch polys sigEffs nm bdy rest ctx ty irFun compiled-rest ir true cf-conn rec-conn fm (yes refl) =
  caf-go-find-form polys sigEffs rest (C.extendFunCtx ctx "main" ty) compiled-rest ir rec-conn
    (trans (sym (findMain-skip-prim
                   (C.mkCompiledFun (bare "main") (proj₁ (C.maybeWrapMain "main" ty irFun))
                      (proj₂ (C.maybeWrapMain "main" ty irFun)) true) compiled-rest refl))
           fm)
cff-dispatch polys sigEffs nm bdy rest ctx ty irFun compiled-rest ir false cf-conn rec-conn fm (yes refl) =
  cff-stop ctx polys sigEffs ty bdy irFun compiled-rest ir
    (compileFun-main-form ctx polys sigEffs ty bdy irFun cf-conn) fm

cff-stop ctx polys sigEffs ty bdy irFun compiled-rest ir (refl , Ψ , seR , irEq , payload) fm =
  Ψ , seR , trans (sym (just-injective fm)) (cong C.wrapMainAsEntry irEq) , payload

------------------------------------------------------------------------
-- (4) Assemble: unfold `moduleToIR` to `compileAllFuns-go`, apply the induction.
------------------------------------------------------------------------

-- Plan 0.55: `main-ir-form` unfolds `moduleToIR` via explicit-scrutinee helpers
-- (dispatch on `extractFunctions` then `compileAllFuns-go`), so it is EXTERNALLY
-- REDUCIBLE: a caller that `with`-abstracts the same scrutinees drives it in
-- lockstep. `mif-ef`/`mif-caf` bottom out in the (now reducible) `caf-go-find-form`.
main-ir-form : ∀ (m : C.Module) (ir : IR Unit Unit) →
  moduleToIR m ≡ just ir → Form ir

mif-caf : ∀ (m : C.Module) (ir : IR Unit Unit) (funs : List FunInfo) (polys : List C.PolyFunInfo)
  (cv : String ⊎ List C.CompiledFun) →
  C.compileAllFuns-go C.Heap false (C.buildPolyCtx polys) (C.collectSigEffects (C.Module.decls m)) funs C.emptyFunCtx ≡ cv →
  moduleToIR-aux cv ≡ just ir → Form ir
mif-caf m ir funs polys (inj₁ err) caf-eq mi = case mi of λ ()
mif-caf m ir funs polys (inj₂ compiled) caf-eq mi =
  caf-go-find-form (C.buildPolyCtx polys) (C.collectSigEffects (C.Module.decls m))
    funs C.emptyFunCtx compiled ir caf-eq mi

mif-ef : ∀ (m : C.Module) (ir : IR Unit Unit)
  (efv : String ⊎ (List FunInfo × List C.PolyFunInfo)) →
  moduleToIR-aux (C.compileResolvedModule-aux C.Heap false m efv) ≡ just ir → Form ir
mif-ef m ir (inj₁ err) mi = case mi of λ ()
mif-ef m ir (inj₂ (funs , polys)) mi =
  mif-caf m ir funs polys
    (C.compileAllFuns-go C.Heap false (C.buildPolyCtx polys) (C.collectSigEffects (C.Module.decls m)) funs C.emptyFunCtx)
    refl mi

main-ir-form m ir mi = mif-ef m ir (C.extractFunctions (C.extractAliases m) m) mi
