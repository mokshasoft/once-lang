-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.String using (String) renaming (_≟_ to _≟str_)
open import Once.CanonicalName using (bare)
open import Relation.Nullary using (yes; no; Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Function using (case_of_)
open import Once.Adequacy.SourceTrace using (findMain; moduleToIR; moduleToIR-aux)
open import Once.Adequacy.MainIRForm using (findMain-skip; compileFun-main-EffUU; bare-injective)

open import Once.Type using (Type; Unit; _⇒[_]_; mk-kind; Many; eff)
open import Once.IR using (IR)
open import Once.IRTy using (⌊_⌋)
open import Once.Surface.Syntax using (Expr; ∅; Usage)
open import Once.Surface.Elaborate using (elaborate)
-- Plan 0.49 / D063 C4: the elaborator-free reference elaboration. Importing it
-- here (proof layer) is fine — `realize` itself does NOT import `checkElab`.
open import Once.Denotation.Realize using (realize)
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.TypeCheck.Classify using (SigEffectCtx)
open import Once.TypeCheck.Elaborate
  using (checkElab; ctxWithImportsAndSelfAndPolys; PolyCtx; _≟T_)
open import Once.TypeCheck.ElaborateProofs using (resolveExpr)
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
  Σ-syntax (IR ⌊ Unit ⌋ ⌊ ty ⌋) (λ irFun →
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
  Σ-syntax (IR ⌊ Unit ⌋ ⌊ ty ⌋) (λ irFun →
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
  in (C.mkCompiledFun (bare (funName fi))
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
findMain-main-or-skip : ∀ (irFun : IR ⌊ Unit ⌋ ⌊ EffUU ⌋) (b : Bool) (rest : List C.CompiledFun)
  (ir-rest : IR ⌊ Unit ⌋ ⌊ Unit ⌋) → findMain rest ≡ just ir-rest →
  Σ-syntax (IR ⌊ Unit ⌋ ⌊ Unit ⌋) (λ ir →
    findMain (C.mkCompiledFun (bare "main") Unit (C.wrapMainAsEntry irFun) b ∷ rest) ≡ just ir)
findMain-main-or-skip irFun false rest ir-rest fm = C.wrapMainAsEntry irFun , refl
findMain-main-or-skip irFun true  rest ir-rest fm = ir-rest , fm

FindResult : ∀ (polys : PolyCtx) (sigEffs : SigEffectCtx) (funs : List FunInfo) (ctx : C.FunCtx) → Set
FindResult polys sigEffs funs ctx =
  Σ-syntax (List C.CompiledFun) (λ compiled → Σ-syntax (IR ⌊ Unit ⌋ ⌊ Unit ⌋) (λ ir →
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
        C.mkCompiledFun (bare "main") Unit (C.wrapMainAsEntry irFun) false ∷ compiled-rest
        , C.wrapMainAsEntry irFun
        , trans (cong (C.caf-go-rf-aux C.Heap false polys sigEffs fi rest ctx) rf)
            (trans (cong (C.caf-go-cf-aux C.Heap false polys sigEffs fi rest ctx EffUU) cf-eq)
                   (cong (C.caf-go-wrap fi EffUU irFun) rec-eq))
        , findMain-main-here irFun compiled-rest
  where
    findMain-main-here : ∀ (g : IR ⌊ Unit ⌋ ⌊ EffUU ⌋) (r : List C.CompiledFun) →
      findMain (C.mkCompiledFun (bare "main") Unit (C.wrapMainAsEntry g) false ∷ r) ≡ just (C.wrapMainAsEntry g)
    findMain-main-here g r = refl
-- there: the main is in `rest`; compile `fi`, recurse, then dispatch `fi`.
caf-go-find-complete polys sigEffs ctx (AS.tcons {fi = fi} {rest = rest} {ty = ty} rf deriv rest-typed) (main-ok , prest) (inj₂ me-rest)
  with compileFun-complete ctx polys sigEffs (funName fi) ty (funBody fi) main-ok deriv
     | caf-go-find-complete polys sigEffs (C.extendFunCtx ctx (funName fi) ty) rest-typed prest me-rest
... | (irFun , cf-eq) | (compiled-rest , ir , rec-eq , fm-rest) = result
  where
    cf0 : C.CompiledFun
    cf0 = C.mkCompiledFun (bare (funName fi)) (proj₁ (C.maybeWrapMain (funName fi) ty irFun))
            (proj₂ (C.maybeWrapMain (funName fi) ty irFun)) (funIsPrimitive fi)
    ca-eq : C.compileAllFuns-go C.Heap false polys sigEffs (fi ∷ rest) ctx ≡ inj₂ (cf0 ∷ compiled-rest)
    ca-eq = trans (cong (C.caf-go-rf-aux C.Heap false polys sigEffs fi rest ctx) rf)
              (trans (cong (C.caf-go-cf-aux C.Heap false polys sigEffs fi rest ctx ty) cf-eq)
                     (cong (C.caf-go-wrap fi ty irFun) rec-eq))
    result : FindResult polys sigEffs (fi ∷ rest) ctx
    result with funName fi ≟str "main"
    ... | no ¬p =
          cf0 ∷ compiled-rest , ir , ca-eq , trans (findMain-skip cf0 compiled-rest (λ e → ¬p (bare-injective e))) fm-rest
    ... | yes refl with main-ok refl
    ...   | refl =
            C.mkCompiledFun (bare "main") Unit (C.wrapMainAsEntry irFun) (funIsPrimitive fi) ∷ compiled-rest
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
  Σ-syntax (IR ⌊ Unit ⌋ ⌊ Unit ⌋) (λ ir → moduleToIR m ≡ just ir)
moduleToIR-complete m mt (amu , me) with C.extractFunctions (C.extractAliases m) m
... | inj₂ (funs , polys)
    with caf-go-find-complete (C.buildPolyCtx polys) (C.collectSigEffects (C.Module.decls m))
           C.emptyFunCtx mt amu me
...   | (compiled , ir , ca-eq , fm-eq) =
        ir , trans (cong moduleToIR-aux ca-eq) fm-eq

------------------------------------------------------------------------
-- Plan 0.49 / D063 C4: the main's CANONICAL realize-term.
--
-- `mainRealized` reads `main`'s `⊢ᶜ` derivation off `ModuleTyped` and applies
-- the elaborator-free `realize` — giving the surface term INDEPENDENTLY of
-- `checkElab` (the row-3 forcing). `main`'s body context is
-- `ctxWithImportsAndSelfAndPolys …` whose `debruijn` is `∅`, so the term lands
-- at `Expr ∅ Ψ EffUU` (what `runMainˢ` needs). The `MainExists` `refl` fixes
-- `ty ≡ EffUU`. The meaning `⟦tp⟧ˢ` = `runMainˢ` of this.
------------------------------------------------------------------------
-- Plan 0.55 (approach A): DETERMINISTIC selector. Walk to the FIRST source-level
-- `main` (`funName ≡ "main" ∧ ¬funIsPrimitive ∧ ty ≡ EffUU`), dispatching on those
-- decisions — NOT on `me`'s inj₁/inj₂ choice (which could point past the first
-- main). `me` is used ONLY to supply the tail witness in the skip branches (so the
-- recursion is non-empty). This makes the selection agree BY CONSTRUCTION with
-- `findMain` (which also picks the first `main`), enabling the `main-extract`
-- alignment without a fragile position-uniqueness argument.
-- Explicit-scrutinee dispatch helper (mutual with `mainRealized-go`), so that the
-- selection is EXTERNALLY REDUCIBLE in proofs: once the three decisions are literal
-- constructors, `mrg-dispatch` reduces (no `with`-block opacity). Return the head IFF
-- it is the (source-level) `main` (name `"main"`, `ty ≡ EffUU`, non-primitive); else
-- recurse into the tail witness `w`.
mainRealized-go : ∀ {polys sigEffs funs ctx}
                  (aft : AS.AllFunsTyped polys sigEffs funs ctx)
                → MainExists aft → Σ-syntax (Usage 0) (λ Ψ → Expr ∅ Ψ EffUU)
mrg-dispatch : ∀ {polys sigEffs nm bdy rest ctx ty Ψ}
  (deriv : (ctxWithImportsAndSelfAndPolys ctx polys sigEffs nm ty) ⊢ᶜ bdy ∶ ty ⨾ Ψ)
  (rest-typed : AS.AllFunsTyped polys sigEffs rest (C.extendFunCtx ctx nm ty))
  (w : MainExists rest-typed)
  → Dec (nm ≡ "main") → Dec (ty ≡ EffUU) → Bool
  → Σ-syntax (Usage 0) (λ Ψ' → Expr ∅ Ψ' EffUU)

-- `inj₁` witnesses the head IS `main` (position 0, hence the first) — return it.
mainRealized-go (AS.tcons {Ψ = Ψ} rf deriv rest) (inj₁ (_ , _ , refl)) = Ψ , realize deriv
-- `inj₂` says a main exists in the tail; but to stay FIRST we still check the head.
mainRealized-go (AS.tcons {fi = fi} {ty = ty} rf deriv rt) (inj₂ w) =
  mrg-dispatch deriv rt w (funName fi ≟str "main") (ty ≟T EffUU) (funIsPrimitive fi)

mrg-dispatch {Ψ = Ψ} deriv rest-typed w (yes _) (yes refl) false = Ψ , realize deriv
mrg-dispatch deriv rest-typed w (no _)  _          _     = mainRealized-go rest-typed w
mrg-dispatch deriv rest-typed w (yes _) (no _)     _     = mainRealized-go rest-typed w
mrg-dispatch deriv rest-typed w (yes _) (yes _)    true  = mainRealized-go rest-typed w

-- Externally-reducible aux (Plan 0.55): takes the `extractFunctions` result as an
-- EXPLICIT argument, so a caller that `with`-abstracts the same scrutinee drives it
-- in lockstep (mirrors `MainIRForm.mif-ef`). Behaviour identical to the old
-- `mainRealized` (which is now defined via it).
mainRealized-ef : ∀ (m : C.Module) (ef : String ⊎ (List FunInfo × List C.PolyFunInfo))
  (mt : AS.ModuleTyped-ef m ef)
  → ModuleMainEffUU-ef m ef mt → ModuleMainExists-ef m ef mt
  → Σ-syntax (Usage 0) (λ Ψ → Expr ∅ Ψ EffUU)
mainRealized-ef m (inj₂ (funs , polys)) mt amu me = mainRealized-go mt me

mainRealized : ∀ (m : C.Module) (mt : AS.ModuleTyped m) → HasValidMain-decl m mt
             → Σ-syntax (Usage 0) (λ Ψ → Expr ∅ Ψ EffUU)
mainRealized m mt (amu , me) =
  mainRealized-ef m (C.extractFunctions (C.extractAliases m) m) mt amu me

------------------------------------------------------------------------
-- REVERSE lift (for soundness): compile-success ⇒ the declarative conditions.
------------------------------------------------------------------------

-- Every main-named function compiled ⇒ its resolved ty is EffUU
-- (validateMain succeeded). Forces nothing new; reuses compileFun-main-EffUU.
caf-go-mains : ∀ (polys : PolyCtx) (sigEffs : SigEffectCtx) {funs : List FunInfo}
  (ctx : C.FunCtx) (aft : AS.AllFunsTyped polys sigEffs funs ctx) {compiled : List C.CompiledFun} →
  C.compileAllFuns-go C.Heap false polys sigEffs funs ctx ≡ inj₂ compiled →
  AllMainEffUU aft
caf-go-mains polys sigEffs ctx AS.tnil _ = tt
caf-go-mains polys sigEffs ctx (AS.tcons {fi = fi} {rest = rest} {ty = ty} rf deriv rest-typed) {compiled} caf-eq =
  go (subst (λ r → C.caf-go-rf-aux C.Heap false polys sigEffs fi rest ctx r ≡ inj₂ compiled) rf caf-eq)
  where
    go : C.caf-go-cf-aux C.Heap false polys sigEffs fi rest ctx ty
           (C.compileFun C.Heap false ctx polys sigEffs (funName fi) ty (funBody fi)) ≡ inj₂ compiled →
         (funName fi ≡ "main" → ty ≡ EffUU) × AllMainEffUU rest-typed
    go eq2 with C.compileFun C.Heap false ctx polys sigEffs (funName fi) ty (funBody fi) in cf-eq
    ... | inj₁ err = case eq2 of λ ()
    ... | inj₂ irFun
        with C.compileAllFuns-go C.Heap false polys sigEffs rest (C.extendFunCtx ctx (funName fi) ty) in rec-eq
    ...   | inj₁ err = case eq2 of λ ()
    ...   | inj₂ compiled-rest =
            (λ p → compileFun-main-EffUU ctx polys sigEffs ty (funBody fi) irFun
                     (subst (λ nm → C.compileFun C.Heap false ctx polys sigEffs nm ty (funBody fi) ≡ inj₂ irFun)
                            p cf-eq))
            , caf-go-mains polys sigEffs (C.extendFunCtx ctx (funName fi) ty) rest-typed rec-eq

-- A primitive head is skipped by findMain (regardless of name/type).
open C.CompiledFun using (cfIsPrimitive)
findMain-skip-prim : ∀ (cf : C.CompiledFun) (rest : List C.CompiledFun) →
  cfIsPrimitive cf ≡ true → findMain (cf ∷ rest) ≡ findMain rest
findMain-skip-prim cf rest pp rewrite pp = refl

-- findMain found an entry ⇒ some main-named non-primitive EffUU function exists.
caf-go-mainexists : ∀ (polys : PolyCtx) (sigEffs : SigEffectCtx) {funs : List FunInfo}
  (ctx : C.FunCtx) (aft : AS.AllFunsTyped polys sigEffs funs ctx)
  {compiled : List C.CompiledFun} {ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋} →
  C.compileAllFuns-go C.Heap false polys sigEffs funs ctx ≡ inj₂ compiled →
  findMain compiled ≡ just ir → MainExists aft
caf-go-mainexists polys sigEffs ctx AS.tnil caf-eq fm =
  case subst (λ c → findMain c ≡ just _) (sym (inj₂-injective caf-eq)) fm of λ ()
caf-go-mainexists polys sigEffs ctx (AS.tcons {fi = fi} {rest = rest} {ty = ty} rf deriv rest-typed) {compiled} {ir} caf-eq fm =
  go (subst (λ r → C.caf-go-rf-aux C.Heap false polys sigEffs fi rest ctx r ≡ inj₂ compiled) rf caf-eq)
  where
    go : C.caf-go-cf-aux C.Heap false polys sigEffs fi rest ctx ty
           (C.compileFun C.Heap false ctx polys sigEffs (funName fi) ty (funBody fi)) ≡ inj₂ compiled →
         MainExists (AS.tcons {fi = fi} {rest = rest} {ty = ty} rf deriv rest-typed)
    go eq2 with C.compileFun C.Heap false ctx polys sigEffs (funName fi) ty (funBody fi) in cf-eq
    ... | inj₁ err = case eq2 of λ ()
    ... | inj₂ irFun
        with C.compileAllFuns-go C.Heap false polys sigEffs rest (C.extendFunCtx ctx (funName fi) ty) in rec-eq
    ...   | inj₁ err = case eq2 of λ ()
    ...   | inj₂ compiled-rest = dispatch
      where
        cf0 : C.CompiledFun
        cf0 = C.mkCompiledFun (bare (funName fi)) (proj₁ (C.maybeWrapMain (funName fi) ty irFun))
                (proj₂ (C.maybeWrapMain (funName fi) ty irFun)) (funIsPrimitive fi)
        fm0 : findMain (cf0 ∷ compiled-rest) ≡ just ir
        fm0 = subst (λ c → findMain c ≡ just ir) (sym (inj₂-injective eq2)) fm
        dispatch : MainExists (AS.tcons {fi = fi} {rest = rest} {ty = ty} rf deriv rest-typed)
        dispatch with funName fi ≟str "main"
        ... | no ¬p =
              inj₂ (caf-go-mainexists polys sigEffs (C.extendFunCtx ctx (funName fi) ty) rest-typed
                      rec-eq (trans (sym (findMain-skip cf0 compiled-rest (λ e → ¬p (bare-injective e)))) fm0))
        ... | yes refl = mx (funIsPrimitive fi) refl
                            (compileFun-main-EffUU ctx polys sigEffs ty (funBody fi) irFun cf-eq)
          where
            mx : (b : Bool) → funIsPrimitive fi ≡ b → ty ≡ EffUU →
                 ((funName fi ≡ "main") × (funIsPrimitive fi ≡ false) × (ty ≡ EffUU)) ⊎ MainExists rest-typed
            mx false fp ty-eff = inj₁ (refl , fp , ty-eff)
            mx true  fp ty-eff =
              inj₂ (caf-go-mainexists polys sigEffs (C.extendFunCtx ctx "main" ty) rest-typed
                      rec-eq (trans (sym (findMain-skip-prim cf0 compiled-rest fp)) fm0))

------------------------------------------------------------------------
-- The reverse lift, assembled: compile-success (via moduleToIR≡just) ⇒
-- HasValidMain-decl. This is what `correctR-sound` uses to build `tp`.
------------------------------------------------------------------------

moduleToIR-sound : ∀ (m : C.Module) (mt : AS.ModuleTyped m) {ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋} →
  moduleToIR m ≡ just ir → HasValidMain-decl m mt
moduleToIR-sound m mt mi with C.extractFunctions (C.extractAliases m) m
... | inj₂ (funs , polys)
    with C.compileAllFuns-go C.Heap false (C.buildPolyCtx polys)
           (C.collectSigEffects (C.Module.decls m)) funs C.emptyFunCtx in ca-eq
...   | inj₂ compiled =
        caf-go-mains (C.buildPolyCtx polys) (C.collectSigEffects (C.Module.decls m)) C.emptyFunCtx mt ca-eq
        , caf-go-mainexists (C.buildPolyCtx polys) (C.collectSigEffects (C.Module.decls m)) C.emptyFunCtx mt ca-eq mi
