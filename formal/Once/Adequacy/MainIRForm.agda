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

open import Data.Bool using (false; true)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Sum.Properties using (inj₂-injective)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.List using (List; []; _∷_)
open import Data.String using (String) renaming (_≟_ to _≟str_)
open import Once.CanonicalName using (CanonicalName; bare) renaming (_≟ᶜ_ to _≟cn_)
open import Relation.Nullary using (yes; no; ¬_)
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
open import Once.TypeCheck.Classify using (SigEffectCtx)
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
  (name : String) (body : RawExpr) (irFun : IR Unit EffUU) →
  C.compileFunBody C.Heap false ctx polys sigEffs name EffUU body ≡ inj₂ irFun →
  Σ-syntax (Usage 0) (λ Ψ → Σ-syntax (Expr ∅ Ψ EffUU) (λ seR → irFun ≡ elaborate C.Heap seR))
compileFunBody-form ctx polys sigEffs name body irFun eq =
  let cr = checkElab (ctxWithImportsAndSelfAndPolys ctx polys sigEffs name EffUU) body EffUU
      (Ψ , se , d , f , ce) =
        AS.compileFunBody-aux-success false ctx polys name EffUU refl cr eq
      eq2 : C.compileFunBody-aux C.Heap false ctx polys name EffUU refl (success Ψ se d f)
            ≡ inj₂ irFun
      eq2 = subst (λ c → C.compileFunBody-aux C.Heap false ctx polys name EffUU refl c ≡ inj₂ irFun)
                  ce eq
  in Ψ , resolveExpr polys ((name , EffUU) ∷ ctx) ((name , EffUU) ∷ ctx) 0 se
       , sym (inj₂-injective eq2)

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
  Σ-syntax (Usage 0) (λ Ψ → Σ-syntax (Expr ∅ Ψ EffUU) (λ seR → irFun ≡ elaborate C.Heap seR))
compileFun-main-formEffUU ctx polys sigEffs body irFun eq =
  compileFunBody-form ctx polys sigEffs "main" body irFun eq

-- compileFun "main": success ⇒ ty≡EffUU AND the (coerced) IR is elaborate-of-resolved.
compileFun-main-form : ∀ (ctx : C.FunCtx) (polys : PolyCtx) (sigEffs : SigEffectCtx)
  (ty : Type) (body : RawExpr) (irFun : IR Unit ty) →
  C.compileFun C.Heap false ctx polys sigEffs "main" ty body ≡ inj₂ irFun →
  Σ-syntax (ty ≡ EffUU) (λ uty → Σ-syntax (Usage 0) (λ Ψ → Σ-syntax (Expr ∅ Ψ EffUU) (λ seR →
    subst (IR Unit) uty irFun ≡ elaborate C.Heap seR)))
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

Form : IR Unit Unit → Set
Form ir = Σ-syntax (Usage 0) (λ Ψ → Σ-syntax (Expr ∅ Ψ EffUU) (λ seR →
            ir ≡ C.wrapMainAsEntry (elaborate C.Heap seR)))

caf-go-find-form : ∀ (polys : PolyCtx) (sigEffs : SigEffectCtx) (funs : List FunInfo)
  (ctx : C.FunCtx) (compiled : List C.CompiledFun) (ir : IR Unit Unit) →
  C.compileAllFuns-go C.Heap false polys sigEffs funs ctx ≡ inj₂ compiled →
  findMain compiled ≡ just ir → Form ir
caf-go-find-form polys sigEffs [] ctx compiled ir caf-eq fm-eq =
  case subst (λ c → findMain c ≡ just ir) (sym (inj₂-injective caf-eq)) fm-eq of λ ()
caf-go-find-form polys sigEffs (fi ∷ rest) ctx compiled ir caf-eq fm-eq
  with C.resolveFunType ctx polys (funType fi) (funBody fi) in rf-eq
... | inj₁ err = case caf-eq of λ ()
... | inj₂ ty
    with C.compileFun C.Heap false ctx polys sigEffs (funName fi) ty (funBody fi) in cf-eq
...   | inj₁ err = case caf-eq of λ ()
...   | inj₂ irFun
      with C.compileAllFuns-go C.Heap false polys sigEffs rest (C.extendFunCtx ctx (funName fi) ty) in rec-eq
...     | inj₁ err = case caf-eq of λ ()
...     | inj₂ compiled-rest
        with funName fi ≟str "main"
...       | no ¬p =
            caf-go-find-form polys sigEffs rest (C.extendFunCtx ctx (funName fi) ty) compiled-rest ir rec-eq
              (trans (sym (findMain-skip
                             (C.mkCompiledFun (bare (funName fi))
                               (proj₁ (C.maybeWrapMain (funName fi) ty irFun))
                               (proj₂ (C.maybeWrapMain (funName fi) ty irFun))
                               (funIsPrimitive fi)) compiled-rest (λ e → ¬p (bare-injective e))))
                     (subst (λ c → findMain c ≡ just ir) (sym (inj₂-injective caf-eq)) fm-eq))
...       | yes refl
          with funIsPrimitive fi
...         | true =
              caf-go-find-form polys sigEffs rest (C.extendFunCtx ctx "main" ty) compiled-rest ir rec-eq
                (subst (λ c → findMain c ≡ just ir) (sym (inj₂-injective caf-eq)) fm-eq)
...         | false
            with compileFun-main-form ctx polys sigEffs ty (funBody fi) irFun cf-eq
...           | (refl , Ψ , seR , irEq) =
                Ψ , seR ,
                trans (sym (just-injective
                              (subst (λ c → findMain c ≡ just ir) (sym (inj₂-injective caf-eq)) fm-eq)))
                      (cong C.wrapMainAsEntry irEq)

------------------------------------------------------------------------
-- (4) Assemble: unfold `moduleToIR` to `compileAllFuns-go`, apply the induction.
------------------------------------------------------------------------

main-ir-form : ∀ (m : C.Module) (ir : IR Unit Unit) →
  moduleToIR m ≡ just ir → Form ir
main-ir-form m ir mi
  with C.extractFunctions (C.extractAliases m) m in ef-eq
... | inj₁ err = case mi of λ ()
... | inj₂ (funs , polys) -- compileResolvedModule reduces to compileAllFuns-go
    with C.compileAllFuns-go C.Heap false (C.buildPolyCtx polys)
           (C.collectSigEffects (C.Module.decls m)) funs C.emptyFunCtx in caf-eq
...   | inj₁ err = case mi of λ ()
...   | inj₂ compiled =
        caf-go-find-form (C.buildPolyCtx polys) (C.collectSigEffects (C.Module.decls m))
          funs C.emptyFunCtx compiled ir caf-eq mi
