-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.ModuleComplete — the FORWARD module-compile completeness
-- lift (Plan 0.49 Phase 1, row-1b): a declaratively well-typed module with a
-- valid `main` COMPILES (`moduleToIR m ≡ just ir`). This forces the
-- typechecker-COMPLETE half: it routes through the proven `check-complete`.
--
-- The "valid main" side conditions are phrased over the TYPING DERIVATION
-- (`AllFunsTyped`'s resolved `ty`), NOT the surface `funType`, so they work
-- for inferred AND explicit main types — and, crucially, so they REVERSE-LIFT
-- (compile-success ⇒ the conditions), which `funType`-based ones do not.
------------------------------------------------------------------------

module Once.Adequacy.ModuleComplete where

open import Data.Bool using (Bool; false; true)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Sum.Properties using (inj₂-injective)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (just)
open import Data.Product using (Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.String using (String) renaming (_≟_ to _≟str_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Once.Adequacy.SourceTrace using (findMain; moduleToIR; moduleToIR-aux)
open import Once.Adequacy.MainIRForm using (findMain-skip)

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
-- Derivation-indexed "valid main" predicates (over `AllFunsTyped`'s `ty`).
------------------------------------------------------------------------

-- Every main-named function (in the derivation) resolved to EffUU.
AllMainEffUU : ∀ {polys sigEffs funs ctx} → AS.AllFunsTyped polys sigEffs funs ctx → Set
AllMainEffUU AS.tnil = ⊤
AllMainEffUU (AS.tcons {fi = fi} {ty = ty} _ _ rest) =
  (funName fi ≡ "main" → ty ≡ EffUU) × AllMainEffUU rest

-- A non-primitive main-named function (resolved to EffUU) exists.
MainExists : ∀ {polys sigEffs funs ctx} → AS.AllFunsTyped polys sigEffs funs ctx → Set
MainExists AS.tnil = ⊥
MainExists (AS.tcons {fi = fi} {ty = ty} _ _ rest) =
  ((funName fi ≡ "main") × (funIsPrimitive fi ≡ false) × (ty ≡ EffUU)) ⊎ MainExists rest

------------------------------------------------------------------------
-- (3) ⇒ the whole list compiles (forward mirror of `caf-go-sound`).
------------------------------------------------------------------------

caf-go-complete : ∀ (polys : PolyCtx) (sigEffs : SigEffectCtx) {funs : List FunInfo}
  (ctx : C.FunCtx) (aft : AS.AllFunsTyped polys sigEffs funs ctx) →
  AllMainEffUU aft →
  Σ-syntax (List C.CompiledFun) (λ compiled →
    C.compileAllFuns-go C.Heap false polys sigEffs funs ctx ≡ inj₂ compiled)
caf-go-complete polys sigEffs ctx AS.tnil _ = [] , refl
caf-go-complete polys sigEffs ctx (AS.tcons {fi = fi} {rest = rest} {ty = ty} rf deriv rest-typed) (main-ok , prest) =
  let (irFun , cf-eq) = compileFun-complete ctx polys sigEffs (funName fi) ty (funBody fi) main-ok deriv
      (compiled-rest , rec-eq) = caf-go-complete polys sigEffs (C.extendFunCtx ctx (funName fi) ty) rest-typed prest
  in (C.mkCompiledFun (funName fi)
        (proj₁ (C.maybeWrapMain (funName fi) ty irFun))
        (proj₂ (C.maybeWrapMain (funName fi) ty irFun))
        (funIsPrimitive fi) ∷ compiled-rest)
   , trans (cong (C.caf-go-rf-aux C.Heap false polys sigEffs fi rest ctx) rf)
       (trans (cong (C.caf-go-cf-aux C.Heap false polys sigEffs fi rest ctx ty) cf-eq)
              (cong (C.caf-go-wrap fi ty irFun) rec-eq))

------------------------------------------------------------------------
-- (4) findMain finds the entry, and assembly to `moduleToIR ≡ just`.
------------------------------------------------------------------------

-- A wrapped "main" entry: non-primitive ⇒ found; primitive ⇒ skipped to the
-- tail. Cases the primitive flag as an ARGUMENT, so `fi` is never split.
findMain-main-or-skip : ∀ (irFun : IR Unit EffUU) (b : Bool) (rest : List C.CompiledFun)
  (ir-rest : IR Unit Unit) → findMain rest ≡ just ir-rest →
  Σ-syntax (IR Unit Unit) (λ ir →
    findMain (C.mkCompiledFun "main" Unit (C.wrapMainAsEntry irFun) b ∷ rest) ≡ just ir)
findMain-main-or-skip irFun false rest ir-rest fm = C.wrapMainAsEntry irFun , refl
findMain-main-or-skip irFun true  rest ir-rest fm = ir-rest , fm

FindResult : ∀ (polys : PolyCtx) (sigEffs : SigEffectCtx) (funs : List FunInfo) (ctx : C.FunCtx) → Set
FindResult polys sigEffs funs ctx =
  Σ-syntax (List C.CompiledFun) (λ compiled → Σ-syntax (IR Unit Unit) (λ ir →
    (C.compileAllFuns-go C.Heap false polys sigEffs funs ctx ≡ inj₂ compiled)
    × (findMain compiled ≡ just ir)))

caf-go-find-complete : ∀ (polys : PolyCtx) (sigEffs : SigEffectCtx) {funs : List FunInfo}
  (ctx : C.FunCtx) (aft : AS.AllFunsTyped polys sigEffs funs ctx) →
  AllMainEffUU aft → MainExists aft → FindResult polys sigEffs funs ctx
-- here: fi is the non-prim EffUU main.
caf-go-find-complete polys sigEffs ctx (AS.tcons {fi = fi} {rest = rest} {ty = ty} rf deriv rest-typed) (main-ok , prest) (inj₁ (refl , refl , refl))
  with compileFun-complete ctx polys sigEffs "main" EffUU (funBody fi) (λ _ → refl) deriv
... | (irFun , cf-eq)
  with caf-go-complete polys sigEffs (C.extendFunCtx ctx "main" EffUU) rest-typed prest
...   | (compiled-rest , rec-eq) =
        C.mkCompiledFun "main" Unit (C.wrapMainAsEntry irFun) false ∷ compiled-rest
        , C.wrapMainAsEntry irFun
        , trans (cong (C.caf-go-rf-aux C.Heap false polys sigEffs fi rest ctx) rf)
            (trans (cong (C.caf-go-cf-aux C.Heap false polys sigEffs fi rest ctx EffUU) cf-eq)
                   (cong (C.caf-go-wrap fi EffUU irFun) rec-eq))
        , findMain-main-here irFun compiled-rest
  where
    findMain-main-here : ∀ (g : IR Unit EffUU) (r : List C.CompiledFun) →
      findMain (C.mkCompiledFun "main" Unit (C.wrapMainAsEntry g) false ∷ r) ≡ just (C.wrapMainAsEntry g)
    findMain-main-here g r = refl
-- there: the main is in `rest`; compile `fi`, recurse, then dispatch `fi`.
caf-go-find-complete polys sigEffs ctx (AS.tcons {fi = fi} {rest = rest} {ty = ty} rf deriv rest-typed) (main-ok , prest) (inj₂ me-rest)
  with compileFun-complete ctx polys sigEffs (funName fi) ty (funBody fi) main-ok deriv
     | caf-go-find-complete polys sigEffs (C.extendFunCtx ctx (funName fi) ty) rest-typed prest me-rest
... | (irFun , cf-eq) | (compiled-rest , ir , rec-eq , fm-rest) = result
  where
    cf0 : C.CompiledFun
    cf0 = C.mkCompiledFun (funName fi) (proj₁ (C.maybeWrapMain (funName fi) ty irFun))
            (proj₂ (C.maybeWrapMain (funName fi) ty irFun)) (funIsPrimitive fi)
    ca-eq : C.compileAllFuns-go C.Heap false polys sigEffs (fi ∷ rest) ctx ≡ inj₂ (cf0 ∷ compiled-rest)
    ca-eq = trans (cong (C.caf-go-rf-aux C.Heap false polys sigEffs fi rest ctx) rf)
              (trans (cong (C.caf-go-cf-aux C.Heap false polys sigEffs fi rest ctx ty) cf-eq)
                     (cong (C.caf-go-wrap fi ty irFun) rec-eq))
    result : FindResult polys sigEffs (fi ∷ rest) ctx
    result with funName fi ≟str "main"
    ... | no ¬p =
          cf0 ∷ compiled-rest , ir , ca-eq , trans (findMain-skip cf0 compiled-rest ¬p) fm-rest
    ... | yes refl with main-ok refl
    ...   | refl =
            C.mkCompiledFun "main" Unit (C.wrapMainAsEntry irFun) (funIsPrimitive fi) ∷ compiled-rest
            , proj₁ (findMain-main-or-skip irFun (funIsPrimitive fi) compiled-rest ir fm-rest)
            , trans (cong (C.caf-go-rf-aux C.Heap false polys sigEffs fi rest ctx) rf)
                (trans (cong (C.caf-go-cf-aux C.Heap false polys sigEffs fi rest ctx EffUU) cf-eq)
                       (cong (C.caf-go-wrap fi EffUU irFun) rec-eq))
            , proj₂ (findMain-main-or-skip irFun (funIsPrimitive fi) compiled-rest ir fm-rest)

------------------------------------------------------------------------
-- ModuleTyped-level predicates + the assembly to `moduleToIR ≡ just`.
------------------------------------------------------------------------

ModuleMainEffUU-ef : ∀ (m : C.Module) (ef : String ⊎ (List FunInfo × List C.PolyFunInfo))
  → AS.ModuleTyped-ef m ef → Set
ModuleMainEffUU-ef m (inj₂ _) mt = AllMainEffUU mt

ModuleMainExists-ef : ∀ (m : C.Module) (ef : String ⊎ (List FunInfo × List C.PolyFunInfo))
  → AS.ModuleTyped-ef m ef → Set
ModuleMainExists-ef m (inj₂ _) mt = MainExists mt

HasValidMain-decl : ∀ (m : C.Module) → AS.ModuleTyped m → Set
HasValidMain-decl m mt =
  ModuleMainEffUU-ef m (C.extractFunctions (C.extractAliases m) m) mt
  × ModuleMainExists-ef m (C.extractFunctions (C.extractAliases m) m) mt

moduleToIR-complete : ∀ (m : C.Module) (mt : AS.ModuleTyped m) →
  HasValidMain-decl m mt →
  Σ-syntax (IR Unit Unit) (λ ir → moduleToIR m ≡ just ir)
moduleToIR-complete m mt (amu , me) with C.extractFunctions (C.extractAliases m) m
... | inj₂ (funs , polys)
    with caf-go-find-complete (C.buildPolyCtx polys) (C.collectSigEffects (C.Module.decls m))
           C.emptyFunCtx mt amu me
...   | (compiled , ir , ca-eq , fm-eq) =
        ir , trans (cong moduleToIR-aux ca-eq) fm-eq
