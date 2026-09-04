-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.FunBundle — Plan 0.55: the per-function bundled
-- compiled+typed selector that discharges `main-extract`'s selector alignment.
--
-- ONE inductive `FunBundle` carries, per function, the compile witnesses
-- (`rf`/`ce`/`cf`+`irFun`) as BOUND fields, so neither `resolveFunType` nor
-- `compileFun` is ever recomputed over an abstract `fi` (the old neutral). Both
-- the `findMain`-style selector (`bundle-find`) and the `mainRealized-go`-style
-- selector (`bundle-realize`) read from it, so their agreement is definitional.
--
-- Promoted from the validated `BundlePOC.agda` blueprint. The two plumbing
-- lemmas are PROVEN here:
--   * `compileFun-ce`          — ce-returning refinement of `compileFun-sound`.
--   * `bundle→compiled≡compiled` — `caf-go-bundle` ↔ `compileAllFuns-go`.
------------------------------------------------------------------------

module Once.Adequacy.FunBundle where


open import Once.Spec.Module using (AllFunsTyped; MainExists; tcons; tnil)
open import Data.Bool using (Bool; false; true)
open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Sum.Properties using (inj₂-injective)
open import Data.Product using (_×_; Σ-syntax; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String; _==_) renaming (_≟_ to _≟str_)
open import Once.CanonicalName using (bare) renaming (_≟ᶜ_ to _≟cn_)
open import Relation.Nullary using (yes; no; Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Function using (case_of_)

open import Once.IR using (IR)
open import Once.IRTy using (⌊_⌋)
open import Once.Type using (Unit; Type; _⇒[_]_; mk-kind; Many; eff)
import Once.Compile as C
open import Once.Surface.Syntax using (Expr; ∅; Usage)
open import Once.Surface.Elaborate using (elaborate; elaborateFull)
open import Once.Denotation.Realize using (realize)
open import Once.TypeCheck.Elaborate as TE
  using (CheckElabResult; checkElab; ctxWithImportsAndSelfAndPolys; PolyCtx; _≟T_)
open import Once.TypeCheck.ElaborateProofs using (resolveExpr)
open import Once.TypeCheck.Classify using (NamedCtx; SigEffectCtx)
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.TypeCheck.Judgment using (_⊢ᶜ_∶_⨾_)
open import Once.TypeCheck.Soundness using (check-sound)
open import Once.Parser using (FunInfo)
open FunInfo
import Once.Adequacy.AcceptSound as AS
open import Once.Adequacy.SourceTrace using (findMain; findMain-here; isUnit?)
open import Once.Adequacy.MainIRForm using (findMain-skip; bare-injective; compileFun-main-EffUU)
import Once.Adequacy.ModuleComplete as MC

EffUU : Type
EffUU = Unit ⇒[ mk-kind Many eff ] Unit

------------------------------------------------------------------------
-- (1) The bundled structure.
------------------------------------------------------------------------

data FunBundle (polys : PolyCtx) (sigEffs : SigEffectCtx)
     : List FunInfo → C.FunCtx → Set where
  bnil : ∀ {ctx} → FunBundle polys sigEffs [] ctx
  bcons : ∀ {fi rest ctx ty}
    {Ψ  : Usage (NamedCtx.size (ctxWithImportsAndSelfAndPolys ctx polys sigEffs (funName fi) ty))}
    {se : Expr (NamedCtx.debruijn (ctxWithImportsAndSelfAndPolys ctx polys sigEffs (funName fi) ty)) Ψ ty}
    {d f : ℕ}
    {irFun : IR ⌊ Unit ⌋ ⌊ ty ⌋} →
    (rf : C.resolveFunType ctx polys (funType fi) (funBody fi) ≡ inj₂ ty) →
    (ce : checkElab (ctxWithImportsAndSelfAndPolys ctx polys sigEffs (funName fi) ty)
            (funBody fi) ty ≡ TE.success Ψ se d f) →
    (cf : C.compileFun C.Heap false ctx polys sigEffs (funName fi) ty (funBody fi) ≡ inj₂ irFun) →
    FunBundle polys sigEffs rest (C.extendFunCtx ctx (funName fi) ty) →
    FunBundle polys sigEffs (fi ∷ rest) ctx

------------------------------------------------------------------------
-- (1b) PROVEN plumbing: `compileFun-ce` — ce-returning refinement of
-- `AcceptSound.compileFun-sound` (same inversion, returns the `checkElab`
-- witness instead of `check-sound` of it).
------------------------------------------------------------------------

compileFunBody-ce : ∀ (doOpt : Bool) (ctx : C.FunCtx) (polys : PolyCtx)
  (sigEffs : SigEffectCtx) (name : String) (ty : Type) (expr : RawExpr) {ir : IR ⌊ Unit ⌋ ⌊ ty ⌋} →
  C.compileFunBody C.Heap doOpt ctx polys sigEffs name ty expr ≡ inj₂ ir →
  Σ-syntax (Usage (NamedCtx.size (ctxWithImportsAndSelfAndPolys ctx polys sigEffs name ty))) (λ Ψ →
  Σ-syntax (Expr (NamedCtx.debruijn (ctxWithImportsAndSelfAndPolys ctx polys sigEffs name ty)) Ψ ty) (λ se →
  Σ-syntax ℕ (λ d → Σ-syntax ℕ (λ f →
    checkElab (ctxWithImportsAndSelfAndPolys ctx polys sigEffs name ty) expr ty ≡ TE.success Ψ se d f))))
compileFunBody-ce doOpt ctx polys sigEffs name ty expr eq =
  AS.compileFunBody-aux-success doOpt ctx polys name ty refl
    (checkElab (ctxWithImportsAndSelfAndPolys ctx polys sigEffs name ty) expr ty) eq

compileFun-main-aux-ce : ∀ (doOpt : Bool) (ctx : C.FunCtx) (polys : PolyCtx)
  (sigEffs : SigEffectCtx) (name : String) (ty : Type) (expr : RawExpr) (vm : String ⊎ ⊤) {ir : IR ⌊ Unit ⌋ ⌊ ty ⌋} →
  C.compileFun-main-aux C.Heap doOpt ctx polys sigEffs name ty expr vm ≡ inj₂ ir →
  Σ-syntax (Usage (NamedCtx.size (ctxWithImportsAndSelfAndPolys ctx polys sigEffs name ty))) (λ Ψ →
  Σ-syntax (Expr (NamedCtx.debruijn (ctxWithImportsAndSelfAndPolys ctx polys sigEffs name ty)) Ψ ty) (λ se →
  Σ-syntax ℕ (λ d → Σ-syntax ℕ (λ f →
    checkElab (ctxWithImportsAndSelfAndPolys ctx polys sigEffs name ty) expr ty ≡ TE.success Ψ se d f))))
compileFun-main-aux-ce doOpt ctx polys sigEffs name ty expr (inj₁ err) ()
compileFun-main-aux-ce doOpt ctx polys sigEffs name ty expr (inj₂ _) eq =
  compileFunBody-ce doOpt ctx polys sigEffs name ty expr eq

compileFun-aux-ce : ∀ (doOpt : Bool) (ctx : C.FunCtx) (polys : PolyCtx)
  (sigEffs : SigEffectCtx) (name : String) (ty : Type) (expr : RawExpr) (b : Bool) {ir : IR ⌊ Unit ⌋ ⌊ ty ⌋} →
  C.compileFun-aux C.Heap doOpt ctx polys sigEffs name ty expr b ≡ inj₂ ir →
  Σ-syntax (Usage (NamedCtx.size (ctxWithImportsAndSelfAndPolys ctx polys sigEffs name ty))) (λ Ψ →
  Σ-syntax (Expr (NamedCtx.debruijn (ctxWithImportsAndSelfAndPolys ctx polys sigEffs name ty)) Ψ ty) (λ se →
  Σ-syntax ℕ (λ d → Σ-syntax ℕ (λ f →
    checkElab (ctxWithImportsAndSelfAndPolys ctx polys sigEffs name ty) expr ty ≡ TE.success Ψ se d f))))
compileFun-aux-ce doOpt ctx polys sigEffs name ty expr true eq =
  compileFun-main-aux-ce doOpt ctx polys sigEffs name ty expr (C.validateMain ty) eq
compileFun-aux-ce doOpt ctx polys sigEffs name ty expr false eq =
  compileFunBody-ce doOpt ctx polys sigEffs name ty expr eq

compileFun-ce : ∀ (polys : PolyCtx) (sigEffs : SigEffectCtx)
  (ctx : C.FunCtx) (ty : Type) (fi : FunInfo) (irFun : IR ⌊ Unit ⌋ ⌊ ty ⌋) →
  C.compileFun C.Heap false ctx polys sigEffs (funName fi) ty (funBody fi) ≡ inj₂ irFun →
  Σ-syntax (Usage (NamedCtx.size (ctxWithImportsAndSelfAndPolys ctx polys sigEffs (funName fi) ty))) (λ Ψ →
  Σ-syntax (Expr (NamedCtx.debruijn (ctxWithImportsAndSelfAndPolys ctx polys sigEffs (funName fi) ty)) Ψ ty) (λ se →
  Σ-syntax ℕ (λ d → Σ-syntax ℕ (λ f →
    checkElab (ctxWithImportsAndSelfAndPolys ctx polys sigEffs (funName fi) ty) (funBody fi) ty
      ≡ TE.success Ψ se d f))))
compileFun-ce polys sigEffs ctx ty fi irFun eq =
  compileFun-aux-ce false ctx polys sigEffs (funName fi) ty (funBody fi) (funName fi == "main") eq

------------------------------------------------------------------------
-- (2) Typing view + compiled view.
------------------------------------------------------------------------

bundle→typed : ∀ {polys sigEffs funs ctx} →
  FunBundle polys sigEffs funs ctx → AllFunsTyped polys sigEffs funs ctx
bundle→typed bnil = tnil
bundle→typed (bcons {fi = fi} {ty = ty} rf ce cf rest) =
  tcons rf (check-sound (ctxWithImportsAndSelfAndPolys _ _ _ (funName fi) ty) (funBody fi) ty ce)
              (bundle→typed rest)

bundle→compiled : ∀ {polys sigEffs funs ctx} →
  FunBundle polys sigEffs funs ctx → List C.CompiledFun
bundle→compiled bnil = []
bundle→compiled (bcons {fi = fi} {ty = ty} {irFun = irFun} rf ce cf rest) =
  C.mkCompiledFun (bare (funName fi)) (proj₁ (C.maybeWrapMain (funName fi) ty irFun))
    (proj₂ (C.maybeWrapMain (funName fi) ty irFun)) (funIsPrimitive fi)
  ∷ bundle→compiled rest

------------------------------------------------------------------------
-- (2b) The builder — reuses the `caf-go-sound` lockstep, additionally
-- threading `ce`/`cf`. Returns the `bundle→compiled ≡ compiled` proof PAIRED,
-- so `bundle→compiled≡compiled` is proven by the SAME recursion (no separate
-- opaque `with`-induction). Explicit-scrutinee helpers (no `with`).
------------------------------------------------------------------------

CGB : (polys : PolyCtx) (sigEffs : SigEffectCtx) (funs : List FunInfo) (ctx : C.FunCtx)
      (compiled : List C.CompiledFun) → Set
CGB polys sigEffs funs ctx compiled =
  Σ-syntax (FunBundle polys sigEffs funs ctx) (λ b → bundle→compiled b ≡ compiled)

caf-go-bundleP : ∀ (polys : PolyCtx) (sigEffs : SigEffectCtx) (funs : List FunInfo) (ctx : C.FunCtx)
  (compiled : List C.CompiledFun) →
  C.compileAllFuns-go C.Heap false polys sigEffs funs ctx ≡ inj₂ compiled → CGB polys sigEffs funs ctx compiled

cgb-rf : ∀ (polys : PolyCtx) (sigEffs : SigEffectCtx) (fi : FunInfo) (rest : List FunInfo)
  (ctx : C.FunCtx) (compiled : List C.CompiledFun) (rfv : String ⊎ Type) →
  C.resolveFunType ctx polys (funType fi) (funBody fi) ≡ rfv →
  C.caf-go-rf-aux C.Heap false polys sigEffs fi rest ctx rfv ≡ inj₂ compiled →
  CGB polys sigEffs (fi ∷ rest) ctx compiled
cgb-cf : ∀ (polys : PolyCtx) (sigEffs : SigEffectCtx) (fi : FunInfo) (rest : List FunInfo)
  (ctx : C.FunCtx) (ty : Type) (compiled : List C.CompiledFun) (cfv : String ⊎ IR ⌊ Unit ⌋ ⌊ ty ⌋) →
  C.resolveFunType ctx polys (funType fi) (funBody fi) ≡ inj₂ ty →
  C.compileFun C.Heap false ctx polys sigEffs (funName fi) ty (funBody fi) ≡ cfv →
  C.caf-go-cf-aux C.Heap false polys sigEffs fi rest ctx ty cfv ≡ inj₂ compiled →
  CGB polys sigEffs (fi ∷ rest) ctx compiled
cgb-rec : ∀ (polys : PolyCtx) (sigEffs : SigEffectCtx) (fi : FunInfo) (rest : List FunInfo)
  (ctx : C.FunCtx) (ty : Type) (irFun : IR ⌊ Unit ⌋ ⌊ ty ⌋) (compiled : List C.CompiledFun)
  (recv : String ⊎ List C.CompiledFun) →
  C.resolveFunType ctx polys (funType fi) (funBody fi) ≡ inj₂ ty →
  C.compileFun C.Heap false ctx polys sigEffs (funName fi) ty (funBody fi) ≡ inj₂ irFun →
  C.compileAllFuns-go C.Heap false polys sigEffs rest (C.extendFunCtx ctx (funName fi) ty) ≡ recv →
  C.caf-go-wrap fi ty irFun recv ≡ inj₂ compiled →
  CGB polys sigEffs (fi ∷ rest) ctx compiled

caf-go-bundleP polys sigEffs [] ctx compiled eq = bnil , inj₂-injective eq
caf-go-bundleP polys sigEffs (fi ∷ rest) ctx compiled eq =
  cgb-rf polys sigEffs fi rest ctx compiled
    (C.resolveFunType ctx polys (funType fi) (funBody fi)) refl eq

cgb-rf polys sigEffs fi rest ctx compiled (inj₁ err) rf-conn ()
cgb-rf polys sigEffs fi rest ctx compiled (inj₂ ty) rf-conn eq =
  cgb-cf polys sigEffs fi rest ctx ty compiled
    (C.compileFun C.Heap false ctx polys sigEffs (funName fi) ty (funBody fi)) rf-conn refl eq

cgb-cf polys sigEffs fi rest ctx ty compiled (inj₁ err) rf-conn cf-conn ()
cgb-cf polys sigEffs fi rest ctx ty compiled (inj₂ irFun) rf-conn cf-conn eq =
  cgb-rec polys sigEffs fi rest ctx ty irFun compiled
    (C.compileAllFuns-go C.Heap false polys sigEffs rest (C.extendFunCtx ctx (funName fi) ty))
    rf-conn cf-conn refl eq

cgb-rec polys sigEffs fi rest ctx ty irFun compiled (inj₁ err) rf-conn cf-conn rec-conn ()
cgb-rec polys sigEffs fi rest ctx ty irFun compiled (inj₂ compiled-rest) rf-conn cf-conn rec-conn eq =
  let (Ψ , se , d , f , ce) = compileFun-ce polys sigEffs ctx ty fi irFun cf-conn
      (b-rest , eq-rest) = caf-go-bundleP polys sigEffs rest (C.extendFunCtx ctx (funName fi) ty) compiled-rest rec-conn
  in bcons {Ψ = Ψ} {se = se} {d = d} {f = f} {irFun = irFun} rf-conn ce cf-conn b-rest
   , trans (cong (C.mkCompiledFun (bare (funName fi)) (proj₁ (C.maybeWrapMain (funName fi) ty irFun))
                    (proj₂ (C.maybeWrapMain (funName fi) ty irFun)) (funIsPrimitive fi) ∷_) eq-rest)
           (inj₂-injective eq)

-- The bundle builder + its compiled-list-correspondence, as named exports.
caf-go-bundle : ∀ (polys : PolyCtx) (sigEffs : SigEffectCtx) (funs : List FunInfo) (ctx : C.FunCtx)
  {compiled : List C.CompiledFun} →
  C.compileAllFuns-go C.Heap false polys sigEffs funs ctx ≡ inj₂ compiled →
  FunBundle polys sigEffs funs ctx
caf-go-bundle polys sigEffs funs ctx {compiled} eq = proj₁ (caf-go-bundleP polys sigEffs funs ctx compiled eq)

bundle→compiled≡compiled : ∀ (polys : PolyCtx) (sigEffs : SigEffectCtx) (funs : List FunInfo) (ctx : C.FunCtx)
  (compiled : List C.CompiledFun) (eq : C.compileAllFuns-go C.Heap false polys sigEffs funs ctx ≡ inj₂ compiled) →
  bundle→compiled (caf-go-bundle polys sigEffs funs ctx eq) ≡ compiled
bundle→compiled≡compiled polys sigEffs funs ctx compiled eq = proj₂ (caf-go-bundleP polys sigEffs funs ctx compiled eq)

------------------------------------------------------------------------
-- (3) The main selector + extraction (bundle-internal alignment).
------------------------------------------------------------------------

BMainExists : ∀ {polys sigEffs funs ctx} → FunBundle polys sigEffs funs ctx → Set
BMainExists bnil = ⊥
BMainExists (bcons {fi = fi} {ty = ty} _ _ _ rest) =
  ((funName fi ≡ "main") × (funIsPrimitive fi ≡ false) × (ty ≡ EffUU)) ⊎ BMainExists rest

------------------------------------------------------------------------
-- (3a) Compile-side selector `bundle-find` + agreement with `findMain`.
------------------------------------------------------------------------

bf-dispatch : ∀ {P : Set} {ty} → IR ⌊ Unit ⌋ ⌊ ty ⌋ →
  Dec P → Dec (ty ≡ EffUU) → Bool → Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋) → Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋)
bf-dispatch irFun np tq true  cont = cont
bf-dispatch irFun (yes _) (yes refl) false cont = just (C.wrapMainAsEntry irFun)
bf-dispatch irFun (no _)  _          false cont = cont
bf-dispatch irFun (yes _) (no _)     false cont = cont

bundle-find : ∀ {polys sigEffs funs ctx} → FunBundle polys sigEffs funs ctx → Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋)
bundle-find bnil = nothing
bundle-find (bcons {fi = fi} {ty = ty} {irFun = irFun} rf ce cf rest) =
  bf-dispatch irFun (funName fi ≟str "main") (ty ≟T EffUU) (funIsPrimitive fi) (bundle-find rest)

fa-head : ∀ {polys sigEffs} (fi : FunInfo) (ctx : C.FunCtx) (ty : Type) (irFun : IR ⌊ Unit ⌋ ⌊ ty ⌋)
  {Ψ : Usage (NamedCtx.size (ctxWithImportsAndSelfAndPolys ctx polys sigEffs (funName fi) ty))}
  {se : Expr (NamedCtx.debruijn (ctxWithImportsAndSelfAndPolys ctx polys sigEffs (funName fi) ty)) Ψ ty}
  {d f : ℕ}
  (ce : checkElab (ctxWithImportsAndSelfAndPolys ctx polys sigEffs (funName fi) ty) (funBody fi) ty
          ≡ TE.success Ψ se d f)
  (cf : C.compileFun C.Heap false ctx polys sigEffs (funName fi) ty (funBody fi) ≡ inj₂ irFun)
  (rest-c : List C.CompiledFun) (rest-f : Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋)) →
  findMain rest-c ≡ rest-f →
  findMain (C.mkCompiledFun (bare (funName fi)) (proj₁ (C.maybeWrapMain (funName fi) ty irFun))
             (proj₂ (C.maybeWrapMain (funName fi) ty irFun)) (funIsPrimitive fi) ∷ rest-c)
    ≡ bf-dispatch irFun (funName fi ≟str "main") (ty ≟T EffUU) (funIsPrimitive fi) rest-f
fa-head {polys = polys} {sigEffs = sigEffs} fi ctx ty irFun ce cf rest-c rest-f ih
  with funIsPrimitive fi
... | true = ih
... | false with funName fi ≟str "main"
...   | no ¬p = ih
...   | yes p with ty ≟T EffUU
...     | yes refl rewrite p = refl
...     | no ¬q rewrite p =
          ⊥-elim (¬q (compileFun-main-EffUU ctx polys sigEffs ty (funBody fi) irFun cf))

find-agree : ∀ {polys sigEffs funs ctx} (b : FunBundle polys sigEffs funs ctx) →
  findMain (bundle→compiled b) ≡ bundle-find b
find-agree bnil = refl
find-agree (bcons {fi = fi} {ctx = ctx} {ty = ty} {irFun = irFun} rf ce cf rest) =
  fa-head fi ctx ty irFun ce cf (bundle→compiled rest) (bundle-find rest) (find-agree rest)

------------------------------------------------------------------------
-- (3b) Typing-side selector `bundle-realize` + agreement with `mainRealized-go`.
------------------------------------------------------------------------

bme→me : ∀ {polys sigEffs funs ctx} (b : FunBundle polys sigEffs funs ctx) →
  BMainExists b → MainExists (bundle→typed b)
bme→me (bcons _ _ _ rest) (inj₁ x) = inj₁ x
bme→me (bcons _ _ _ rest) (inj₂ w) = inj₂ (bme→me rest w)

br-dispatch : ∀ {polys sigEffs rest ctx ty} (fi : FunInfo)
  {Ψ : Usage (NamedCtx.size (ctxWithImportsAndSelfAndPolys ctx polys sigEffs (funName fi) ty))}
  {se : Expr (NamedCtx.debruijn (ctxWithImportsAndSelfAndPolys ctx polys sigEffs (funName fi) ty)) Ψ ty}
  {d f : ℕ}
  (ce : checkElab (ctxWithImportsAndSelfAndPolys ctx polys sigEffs (funName fi) ty) (funBody fi) ty
          ≡ TE.success Ψ se d f)
  (rt : FunBundle polys sigEffs rest (C.extendFunCtx ctx (funName fi) ty)) (w : BMainExists rt)
  → Dec (funName fi ≡ "main") → Dec (ty ≡ EffUU) → Bool
  → Σ-syntax (Usage 0) (λ Ψ' → Expr ∅ Ψ' EffUU)

bundle-realize : ∀ {polys sigEffs funs ctx} (b : FunBundle polys sigEffs funs ctx) →
  BMainExists b → Σ-syntax (Usage 0) (λ Ψ → Expr ∅ Ψ EffUU)
bundle-realize {polys = polys} {sigEffs = sigEffs}
               (bcons {fi = fi} {ctx = ctx} {Ψ = Ψ} rf ce cf rest) (inj₁ (_ , _ , refl)) =
  Ψ , realize (check-sound (ctxWithImportsAndSelfAndPolys ctx polys sigEffs (funName fi) EffUU) (funBody fi) EffUU ce)
bundle-realize (bcons {fi = fi} {ty = ty} rf ce cf rest) (inj₂ w) =
  br-dispatch fi ce rest w (funName fi ≟str "main") (ty ≟T EffUU) (funIsPrimitive fi)

-- PRIM-FIRST clause order, matching `bf-dispatch` (so `bundle-find` and
-- `bundle-realize` dispatch identically ⇒ their node-coherence is definitional).
br-dispatch fi ce rt w _        _          true  = bundle-realize rt w
br-dispatch {polys = polys} {sigEffs = sigEffs} {ctx = ctx} fi {Ψ = Ψ} ce rt w (yes _) (yes refl) false =
  Ψ , realize (check-sound (ctxWithImportsAndSelfAndPolys ctx polys sigEffs (funName fi) EffUU) (funBody fi) EffUU ce)
br-dispatch fi ce rt w (no _)  _          false = bundle-realize rt w
br-dispatch fi ce rt w (yes _) (no _)     false = bundle-realize rt w

realize-agree : ∀ {polys sigEffs funs ctx} (b : FunBundle polys sigEffs funs ctx) (bme : BMainExists b) →
  MC.mainRealized-go (bundle→typed b) (bme→me b bme) ≡ bundle-realize b bme

ra-head : ∀ {polys sigEffs rest ctx ty} (fi : FunInfo)
  {Ψ : Usage (NamedCtx.size (ctxWithImportsAndSelfAndPolys ctx polys sigEffs (funName fi) ty))}
  {se : Expr (NamedCtx.debruijn (ctxWithImportsAndSelfAndPolys ctx polys sigEffs (funName fi) ty)) Ψ ty}
  {d f : ℕ}
  (ce : checkElab (ctxWithImportsAndSelfAndPolys ctx polys sigEffs (funName fi) ty) (funBody fi) ty
          ≡ TE.success Ψ se d f)
  (rt : FunBundle polys sigEffs rest (C.extendFunCtx ctx (funName fi) ty)) (w : BMainExists rt) →
  MC.mrg-dispatch (check-sound (ctxWithImportsAndSelfAndPolys ctx polys sigEffs (funName fi) ty) (funBody fi) ty ce)
      (bundle→typed rt) (bme→me rt w) (funName fi ≟str "main") (ty ≟T EffUU) (funIsPrimitive fi)
  ≡ br-dispatch fi ce rt w (funName fi ≟str "main") (ty ≟T EffUU) (funIsPrimitive fi)
-- `mrg-dispatch` is name-first, `br-dispatch` (now) prim-first ⇒ case all three
-- concretely (prim always; type when name=yes) so BOTH sides reduce per branch.
ra-head {ty = ty} fi ce rt w
  with funName fi ≟str "main" | ty ≟T EffUU | funIsPrimitive fi
... | no _  | _        | false = realize-agree rt w
... | no _  | _        | true  = realize-agree rt w
... | yes _ | yes refl | false = refl
... | yes _ | yes refl | true  = realize-agree rt w
... | yes _ | no _     | false = realize-agree rt w
... | yes _ | no _     | true  = realize-agree rt w

realize-agree (bcons rf ce cf rest) (inj₁ (_ , _ , refl)) = refl
realize-agree (bcons {fi = fi} rf ce cf rest) (inj₂ w) = ra-head fi ce rest w

------------------------------------------------------------------------
-- (3c) `bundle-realize-node`: extract the selected main node's data
-- (`mctx`/`mbody`/`mΨ`/`mse`/`mce`) with a proof that `bundle-realize` returns
-- exactly `realize (check-sound … mce)` at that node. Feeds eq2 of `main-extract`.
-- Prim-first dispatch (mirrors `br-dispatch`) ⇒ same node as `bundle-find`.
------------------------------------------------------------------------

RNode : ∀ (polys : PolyCtx) (sigEffs : SigEffectCtx)
  → Σ-syntax (Usage 0) (λ Ψ' → Expr ∅ Ψ' EffUU) → Set
RNode polys sigEffs r =
  Σ-syntax C.FunCtx (λ mctx → Σ-syntax RawExpr (λ mbody →
  Σ-syntax (Usage 0) (λ mΨ → Σ-syntax (Expr ∅ mΨ EffUU) (λ mse → Σ-syntax ℕ (λ md → Σ-syntax ℕ (λ mf →
  Σ-syntax (checkElab (ctxWithImportsAndSelfAndPolys mctx polys sigEffs "main" EffUU) mbody EffUU
             ≡ TE.success mΨ mse md mf) (λ mce →
    r ≡ (mΨ , realize (check-sound (ctxWithImportsAndSelfAndPolys mctx polys sigEffs "main" EffUU) mbody EffUU mce)))))))))

bundle-realize-node : ∀ {polys sigEffs funs ctx} (b : FunBundle polys sigEffs funs ctx)
  (bme : BMainExists b) → RNode polys sigEffs (bundle-realize b bme)

brn-dispatch : ∀ {polys sigEffs rest ctx ty} (fi : FunInfo)
  {Ψ : Usage (NamedCtx.size (ctxWithImportsAndSelfAndPolys ctx polys sigEffs (funName fi) ty))}
  {se : Expr (NamedCtx.debruijn (ctxWithImportsAndSelfAndPolys ctx polys sigEffs (funName fi) ty)) Ψ ty}
  {d f : ℕ}
  (ce : checkElab (ctxWithImportsAndSelfAndPolys ctx polys sigEffs (funName fi) ty) (funBody fi) ty
          ≡ TE.success Ψ se d f)
  (rt : FunBundle polys sigEffs rest (C.extendFunCtx ctx (funName fi) ty)) (w : BMainExists rt)
  (nd : Dec (funName fi ≡ "main")) (td : Dec (ty ≡ EffUU)) (pb : Bool)
  → RNode polys sigEffs (br-dispatch fi ce rt w nd td pb)
brn-dispatch fi ce rt w _        _          true  = bundle-realize-node rt w
brn-dispatch {polys = polys} {sigEffs = sigEffs} {ctx = ctx} fi {Ψ = Ψ} {se = se} {d = d} {f = f} ce rt w (yes p) (yes refl) false rewrite p =
  ctx , funBody fi , Ψ , se , d , f , ce , refl
brn-dispatch fi ce rt w (no _)  _          false = bundle-realize-node rt w
brn-dispatch fi ce rt w (yes _) (no _)     false = bundle-realize-node rt w

bundle-realize-node {polys = polys} {sigEffs = sigEffs}
  (bcons {fi = fi} {ctx = ctx} {Ψ = Ψ} {se = se} {d = d} {f = f} rf ce cf rest) (inj₁ (p , _ , refl)) rewrite p =
  ctx , funBody fi , Ψ , se , d , f , ce , refl
bundle-realize-node (bcons {fi = fi} {ty = ty} rf ce cf rest) (inj₂ w) =
  brn-dispatch fi ce rest w (funName fi ≟str "main") (ty ≟T EffUU) (funIsPrimitive fi)

------------------------------------------------------------------------
-- (3d) `bundle-find-exists`: a `just` find result witnesses `BMainExists`.
------------------------------------------------------------------------

bundle-find-exists : ∀ {polys sigEffs funs ctx} (b : FunBundle polys sigEffs funs ctx)
  {ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋} → bundle-find b ≡ just ir → BMainExists b
bundle-find-exists bnil ()
bundle-find-exists (bcons {fi = fi} {ty = ty} {irFun = irFun} rf ce cf rest) eq
  with funName fi ≟str "main" | ty ≟T EffUU | funIsPrimitive fi
... | yes p | yes refl | false = inj₁ (p , refl , refl)
... | yes _ | yes refl | true  = inj₂ (bundle-find-exists rest eq)
... | yes _ | no _     | false = inj₂ (bundle-find-exists rest eq)
... | yes _ | no _     | true  = inj₂ (bundle-find-exists rest eq)
... | no _  | _        | false = inj₂ (bundle-find-exists rest eq)
... | no _  | _        | true  = inj₂ (bundle-find-exists rest eq)

------------------------------------------------------------------------
-- (3e) `bundle-main-node`: the COMBINED find+realize node extractor. Returns
-- the selected main node's data with BOTH (i) the find-side IR form
-- (`bundle-find b ≡ just (wrapMainAsEntry (elaborate … seR))`) and (ii) the
-- realize-side (`bundle-realize b bme ≡ (Ψ , realize (check-sound … ce))`),
-- over the SAME node. Feeds the bundle-rebased `main-ir-form` (Plan 0.55).
------------------------------------------------------------------------

-- IR-form lemma: from the bound `ce`/`cf` at a "main" node, the compiled IR is
-- the elaboration of the resolved checkElab term (uses the bound `se`/`ce`).
irFun-main-form : ∀ (ctx : C.FunCtx) (polys : PolyCtx) (sigEffs : SigEffectCtx)
  (body : RawExpr) (irFun : IR ⌊ Unit ⌋ ⌊ EffUU ⌋)
  {Ψ : Usage 0} {se : Expr ∅ Ψ EffUU} {d f : ℕ}
  (ce : checkElab (ctxWithImportsAndSelfAndPolys ctx polys sigEffs "main" EffUU) body EffUU
          ≡ TE.success Ψ se d f)
  (cf : C.compileFun C.Heap false ctx polys sigEffs "main" EffUU body ≡ inj₂ irFun) →
  irFun ≡ elaborateFull C.Heap (resolveExpr polys (("main" , EffUU) ∷ ctx) (("main" , EffUU) ∷ ctx) 0 se)
irFun-main-form ctx polys sigEffs body irFun ce cf =
  inj₂-injective (trans (sym cf) (cong (C.compileFunBody-aux C.Heap false ctx polys "main" EffUU refl) ce))

MNodeAt : ∀ (polys : PolyCtx) (sigEffs : SigEffectCtx)
  → Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋) → Σ-syntax (Usage 0) (λ Ψ' → Expr ∅ Ψ' EffUU) → Set
MNodeAt polys sigEffs fr rr =
  Σ-syntax C.FunCtx (λ mctx → Σ-syntax RawExpr (λ mbody →
  Σ-syntax (Usage 0) (λ mΨ → Σ-syntax (Expr ∅ mΨ EffUU) (λ mse → Σ-syntax ℕ (λ md → Σ-syntax ℕ (λ mf →
  Σ-syntax (checkElab (ctxWithImportsAndSelfAndPolys mctx polys sigEffs "main" EffUU) mbody EffUU
             ≡ TE.success mΨ mse md mf) (λ mce →
    (fr ≡ just (C.wrapMainAsEntry (elaborateFull C.Heap
            (resolveExpr polys (("main" , EffUU) ∷ mctx) (("main" , EffUU) ∷ mctx) 0 mse))))
  × (rr ≡ (mΨ , realize (check-sound (ctxWithImportsAndSelfAndPolys mctx polys sigEffs "main" EffUU)
                           mbody EffUU mce))))))))))

bundle-main-node : ∀ {polys sigEffs funs ctx} (b : FunBundle polys sigEffs funs ctx)
  (bme : BMainExists b) → MNodeAt polys sigEffs (bundle-find b) (bundle-realize b bme)

bmn-dispatch : ∀ {polys sigEffs rest ctx ty} (fi : FunInfo)
  {Ψ : Usage (NamedCtx.size (ctxWithImportsAndSelfAndPolys ctx polys sigEffs (funName fi) ty))}
  {se : Expr (NamedCtx.debruijn (ctxWithImportsAndSelfAndPolys ctx polys sigEffs (funName fi) ty)) Ψ ty}
  {d f : ℕ} {irFun : IR ⌊ Unit ⌋ ⌊ ty ⌋}
  (ce : checkElab (ctxWithImportsAndSelfAndPolys ctx polys sigEffs (funName fi) ty) (funBody fi) ty
          ≡ TE.success Ψ se d f)
  (cf : C.compileFun C.Heap false ctx polys sigEffs (funName fi) ty (funBody fi) ≡ inj₂ irFun)
  (rt : FunBundle polys sigEffs rest (C.extendFunCtx ctx (funName fi) ty)) (w : BMainExists rt)
  (nd : Dec (funName fi ≡ "main")) (td : Dec (ty ≡ EffUU)) (pb : Bool)
  → MNodeAt polys sigEffs (bf-dispatch irFun nd td pb (bundle-find rt))
                          (br-dispatch fi ce rt w nd td pb)
bmn-dispatch fi ce cf rt w _        _          true  = bundle-main-node rt w
bmn-dispatch {polys = polys} {sigEffs = sigEffs} {ctx = ctx} fi {Ψ = Ψ} {se = se} {d = d} {f = f} {irFun = irFun}
             ce cf rt w (yes p) (yes refl) false rewrite p =
  ctx , funBody fi , Ψ , se , d , f , ce ,
    cong (λ x → just (C.wrapMainAsEntry x)) (irFun-main-form ctx polys sigEffs (funBody fi) irFun ce cf) , refl
bmn-dispatch fi ce cf rt w (no _)  _          false = bundle-main-node rt w
bmn-dispatch fi ce cf rt w (yes _) (no _)     false = bundle-main-node rt w

bundle-main-node {polys = polys} {sigEffs = sigEffs}
  (bcons {fi = fi} {ctx = ctx} {Ψ = Ψ} {se = se} {d = d} {f = f} {irFun = irFun} rf ce cf rest) (inj₁ (p , pr , refl))
  rewrite p | pr with "main" ≟str "main" | EffUU ≟T EffUU
... | yes refl | yes refl =
      ctx , funBody fi , Ψ , se , d , f , ce ,
        cong (λ x → just (C.wrapMainAsEntry x)) (irFun-main-form ctx polys sigEffs (funBody fi) irFun ce cf) , refl
... | yes _    | no ¬q = ⊥-elim (¬q refl)
... | no ¬r    | _     = ⊥-elim (¬r refl)
bundle-main-node (bcons {fi = fi} {ty = ty} rf ce cf rest) (inj₂ w) =
  bmn-dispatch fi ce cf rest w (funName fi ≟str "main") (ty ≟T EffUU) (funIsPrimitive fi)
