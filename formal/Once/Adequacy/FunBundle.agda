-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.FunBundle — Plan 0.55: the per-function bundled
-- compiled+typed selector that discharges `main-extract`'s selector alignment.
--
-- D241 (plan 0.103 6c′): indexed by the module TELESCOPE walk.
--
-- ONE inductive `FunBundle` carries, per entry, the compile witnesses
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


open import Once.Spec.Module using (ModTele; []; ffi; mono; poly; MainIn; ctxOf; addImp)
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
open import Once.Type.Rigid using (rigidOf; RigidFree; rigidFree?)
open import Once.Functor.Translate using (IsConcrete)
open import Once.Functor.Decide using (isConcrete?)
open import Once.Type.Honest using (HonestFFI; honest?)
import Once.Surface.Syntax as Srf
open import Once.Surface.Syntax using (Expr; ∅; Usage)
open import Once.Surface.Elaborate using (elaborate; elaborateFull)
open import Once.Denotation.Realize using (realize)
open import Once.TypeCheck.Elaborate as TE
  using (CheckElabResult; checkElab; ctxWithImportsAndPolys; PolyCtx)
open import Once.Type.DecEq using (_≟T_)
open import Once.TypeCheck.ElaborateProofs using (resolveExpr)
open import Once.TypeCheck.Classify using (NamedCtx)
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

ctxC : C.CScope → NamedCtx
ctxC sc = ctxWithImportsAndPolys (C.CScope.cimps sc) (C.cpolys sc)

data FunBundle : C.CScope → List C.Entry → Set where
  bnil  : ∀ {sc} → FunBundle sc []
  bffi  : ∀ {sc fi ty es} {c : IsConcrete ty} {h : HonestFFI ty} {g : RigidFree ty}
        → funIsPrimitive fi ≡ true → funType fi ≡ just ty
        → isConcrete? ty ≡ just c → honest? ty ≡ just h → rigidFree? ty ≡ just g
        → FunBundle (C.extendScope sc (funName fi) ty) es
        → FunBundle sc (C.e-fun fi ∷ es)
  bcons : ∀ {sc fi es ty}
    {Ψ  : Usage (NamedCtx.size (ctxC sc))}
    {se : Expr (NamedCtx.debruijn (ctxC sc)) Ψ ty}
    {d f : ℕ}
    {irFun : IR ⌊ Unit ⌋ ⌊ ty ⌋} →
    (ep : funIsPrimitive fi ≡ false) →
    (rf : C.resolveFunType (C.CScope.cimps sc) (C.cpolys sc) (funType fi) (funBody fi) ≡ inj₂ ty) →
    {g : RigidFree ty} → (eg : rigidFree? ty ≡ just g) →
    (ce : checkElab (ctxC sc) (funBody fi) ty ≡ TE.success Ψ se d f) →
    (cf : C.compileFun C.Heap false (C.CScope.cimps sc) (C.cpolys sc) (C.declImps (C.CScope.ctele sc))
            (funName fi) ty (funBody fi) ≡ inj₂ irFun) →
    FunBundle (C.extendScope sc (funName fi) ty) es →
    FunBundle sc (C.e-fun fi ∷ es)
  bpoly : ∀ {sc pfi es}
    {Ψ  : Usage (NamedCtx.size (ctxC sc))}
    {se : Expr (NamedCtx.debruijn (ctxC sc)) Ψ (rigidOf (C.PolyFunInfo.pfunType pfi))}
    {d f : ℕ} →
    (ce : checkElab (ctxC sc) (C.PolyFunInfo.pfunBody pfi) (rigidOf (C.PolyFunInfo.pfunType pfi)) ≡ TE.success Ψ se d f) →
    FunBundle (C.addEntry sc pfi) es →
    FunBundle sc (C.e-poly pfi ∷ es)

compileFunBody-ce : ∀ (doOpt : Bool) (ctx : C.FunCtx) (polys : PolyCtx) (impsOf : C.String → C.FunCtx)
  (name : String) (ty : Type) (expr : RawExpr) {ir : IR ⌊ Unit ⌋ ⌊ ty ⌋} →
  C.compileFunBody C.Heap doOpt ctx polys impsOf name ty expr ≡ inj₂ ir →
  Σ-syntax (Usage (NamedCtx.size (ctxWithImportsAndPolys ctx polys))) (λ Ψ →
  Σ-syntax (Expr (NamedCtx.debruijn (ctxWithImportsAndPolys ctx polys)) Ψ ty) (λ se →
  Σ-syntax ℕ (λ d → Σ-syntax ℕ (λ f →
    checkElab (ctxWithImportsAndPolys ctx polys) expr ty ≡ TE.success Ψ se d f))))
compileFunBody-ce doOpt ctx polys impsOf name ty expr eq =
  AS.compileFunBody-aux-success doOpt ctx polys impsOf name ty refl
    (checkElab (ctxWithImportsAndPolys ctx polys) expr ty) eq

compileFun-main-aux-ce : ∀ (doOpt : Bool) (ctx : C.FunCtx) (polys : PolyCtx) (impsOf : C.String → C.FunCtx)
  (name : String) (ty : Type) (expr : RawExpr) (vm : String ⊎ ⊤) {ir : IR ⌊ Unit ⌋ ⌊ ty ⌋} →
  C.compileFun-main-aux C.Heap doOpt ctx polys impsOf name ty expr vm ≡ inj₂ ir →
  Σ-syntax (Usage (NamedCtx.size (ctxWithImportsAndPolys ctx polys))) (λ Ψ →
  Σ-syntax (Expr (NamedCtx.debruijn (ctxWithImportsAndPolys ctx polys)) Ψ ty) (λ se →
  Σ-syntax ℕ (λ d → Σ-syntax ℕ (λ f →
    checkElab (ctxWithImportsAndPolys ctx polys) expr ty ≡ TE.success Ψ se d f))))
compileFun-main-aux-ce doOpt ctx polys impsOf name ty expr (inj₁ err) ()
compileFun-main-aux-ce doOpt ctx polys impsOf name ty expr (inj₂ _) eq =
  compileFunBody-ce doOpt ctx polys impsOf name ty expr eq

compileFun-aux-ce : ∀ (doOpt : Bool) (ctx : C.FunCtx) (polys : PolyCtx) (impsOf : C.String → C.FunCtx)
  (name : String) (ty : Type) (expr : RawExpr) (b : Bool) {ir : IR ⌊ Unit ⌋ ⌊ ty ⌋} →
  C.compileFun-aux C.Heap doOpt ctx polys impsOf name ty expr b ≡ inj₂ ir →
  Σ-syntax (Usage (NamedCtx.size (ctxWithImportsAndPolys ctx polys))) (λ Ψ →
  Σ-syntax (Expr (NamedCtx.debruijn (ctxWithImportsAndPolys ctx polys)) Ψ ty) (λ se →
  Σ-syntax ℕ (λ d → Σ-syntax ℕ (λ f →
    checkElab (ctxWithImportsAndPolys ctx polys) expr ty ≡ TE.success Ψ se d f))))
compileFun-aux-ce doOpt ctx polys impsOf name ty expr true eq =
  compileFun-main-aux-ce doOpt ctx polys impsOf name ty expr (C.validateMain ty) eq
compileFun-aux-ce doOpt ctx polys impsOf name ty expr false eq =
  compileFunBody-ce doOpt ctx polys impsOf name ty expr eq

compileFun-ce : ∀ (polys : PolyCtx) (impsOf : C.String → C.FunCtx)
  (ctx : C.FunCtx) (ty : Type) (fi : FunInfo) (irFun : IR ⌊ Unit ⌋ ⌊ ty ⌋) →
  C.compileFun C.Heap false ctx polys impsOf (funName fi) ty (funBody fi) ≡ inj₂ irFun →
  Σ-syntax (Usage (NamedCtx.size (ctxWithImportsAndPolys ctx polys))) (λ Ψ →
  Σ-syntax (Expr (NamedCtx.debruijn (ctxWithImportsAndPolys ctx polys)) Ψ ty) (λ se →
  Σ-syntax ℕ (λ d → Σ-syntax ℕ (λ f →
    checkElab (ctxWithImportsAndPolys ctx polys) (funBody fi) ty
      ≡ TE.success Ψ se d f))))
compileFun-ce polys impsOf ctx ty fi irFun eq =
  compileFun-aux-ce false ctx polys impsOf (funName fi) ty (funBody fi) (funName fi == "main") eq

------------------------------------------------------------------------
-- (2) Typing view + compiled view.
------------------------------------------------------------------------


bundle→typed : ∀ {sc es} → FunBundle sc es → ModTele (AS.scopeOf sc) es
bundle→typed bnil = []
bundle→typed (bffi {c = c} {h = h} {g = g} ep et _ _ _ rest) = ffi ep et c h g (bundle→typed rest)
bundle→typed {sc} (bcons {fi = fi} {ty = ty} ep rf {g} eg ce cf rest) =
  mono ep rf g (check-sound (ctxC sc) (funBody fi) ty ce) (bundle→typed rest)
bundle→typed {sc} (bpoly {pfi = pfi} ce rest) =
  poly (check-sound (ctxC sc) (C.PolyFunInfo.pfunBody pfi) (rigidOf (C.PolyFunInfo.pfunType pfi)) ce) (bundle→typed rest)

primCF : ∀ (fi : FunInfo) (ty : Type) → IsConcrete ty → C.CompiledFun
primCF fi ty c = C.mkCompiledFun (bare (funName fi)) ty (elaborateFull C.Heap (Srf.sigOp {Γ = Srf.∅} (bare (funName fi)) c)) true

bundle→compiled : ∀ {sc es} → FunBundle sc es → List C.CompiledFun
bundle→compiled bnil = []
bundle→compiled (bffi {fi = fi} {ty = ty} {c = c} _ _ _ _ _ rest) = primCF fi ty c ∷ bundle→compiled rest
bundle→compiled (bcons {fi = fi} {ty = ty} {irFun = irFun} ep rf eg ce cf rest) =
  C.mkCompiledFun (bare (funName fi)) (proj₁ (C.maybeWrapMain (funName fi) ty irFun))
    (proj₂ (C.maybeWrapMain (funName fi) ty irFun)) (funIsPrimitive fi)
  ∷ bundle→compiled rest
bundle→compiled (bpoly ce rest) = bundle→compiled rest

-- A bundle for every accepted telescope, whose compiled list IS the compiler's.
CGB : C.CScope → List C.Entry → List C.CompiledFun → Set
CGB sc es compiled = Σ-syntax (FunBundle sc es) (λ b → bundle→compiled b ≡ compiled)

ce-bundleP : ∀ (sc : C.CScope) (es : List C.Entry) (compiled : List C.CompiledFun)
  → C.compileEntries C.Heap false sc es ≡ inj₂ compiled → CGB sc es compiled
cgb-fun : ∀ (sc : C.CScope) (fi : FunInfo) (es : List C.Entry) (compiled : List C.CompiledFun) (b : Bool)
  → funIsPrimitive fi ≡ b → C.ce-fun C.Heap false sc fi es b ≡ inj₂ compiled → CGB sc (C.e-fun fi ∷ es) compiled
cgb-prim : ∀ (sc : C.CScope) (fi : FunInfo) (es : List C.Entry) (compiled : List C.CompiledFun)
  → funIsPrimitive fi ≡ true → (mt : Maybe Type) → funType fi ≡ mt
  → C.ce-prim C.Heap false sc fi es mt ≡ inj₂ compiled → CGB sc (C.e-fun fi ∷ es) compiled
cgb-mono : ∀ (sc : C.CScope) (fi : FunInfo) (es : List C.Entry) (compiled : List C.CompiledFun)
  → funIsPrimitive fi ≡ false → (rt : String ⊎ Type)
  → C.resolveFunType (C.CScope.cimps sc) (C.cpolys sc) (funType fi) (funBody fi) ≡ rt
  → C.ce-mono C.Heap false sc fi es rt ≡ inj₂ compiled → CGB sc (C.e-fun fi ∷ es) compiled
cgb-poly : ∀ (sc : C.CScope) (pfi : C.PolyFunInfo) (es : List C.Entry) (compiled : List C.CompiledFun)
  → (r : TE.VerifiedCheckResult (ctxC sc) (C.PolyFunInfo.pfunBody pfi) (rigidOf (C.PolyFunInfo.pfunType pfi)))
  → TE.checkElabV (ctxC sc) (C.PolyFunInfo.pfunBody pfi) (rigidOf (C.PolyFunInfo.pfunType pfi)) ≡ r
  → C.ce-poly C.Heap false sc pfi es (C.checkOK r) ≡ inj₂ compiled → CGB sc (C.e-poly pfi ∷ es) compiled

ce-bundleP sc [] compiled eq = bnil , inj₂-injective eq
ce-bundleP sc (C.e-fun fi ∷ es) compiled eq = cgb-fun sc fi es compiled (funIsPrimitive fi) refl eq
ce-bundleP sc (C.e-poly pfi ∷ es) compiled eq = cgb-poly sc pfi es compiled _ refl eq

cgb-fun sc fi es compiled true  ep eq = cgb-prim sc fi es compiled ep (funType fi) refl eq
cgb-fun sc fi es compiled false ep eq =
  cgb-mono sc fi es compiled ep (C.resolveFunType (C.CScope.cimps sc) (C.cpolys sc) (funType fi) (funBody fi)) refl eq

cgb-prim sc fi es compiled ep nothing et ()
cgb-prim sc fi es compiled ep (just ty) et eq = conc (isConcrete? ty) refl (honest? ty) refl (rigidFree? ty) refl eq
  where
    conc : (mc : Maybe (IsConcrete ty)) → isConcrete? ty ≡ mc → (mh : Maybe (HonestFFI ty)) → honest? ty ≡ mh
         → (mg : Maybe (RigidFree ty)) → rigidFree? ty ≡ mg
         → C.ce-prim-conc C.Heap false sc fi es ty mc mh mg ≡ inj₂ compiled → CGB sc (C.e-fun fi ∷ es) compiled
    conc nothing _ _ _ _ _ ()
    conc (just _) _ nothing _ _ _ ()
    conc (just _) _ (just _) _ nothing _ ()
    conc (just c) ec (just h) eh (just g) eg eq′ with C.compileEntries C.Heap false (C.extendScope sc (funName fi) ty) es in rec
    ... | inj₁ _ = case eq′ of λ ()
    ... | inj₂ rest =
          let (b , beq) = ce-bundleP (C.extendScope sc (funName fi) ty) es rest rec
          in bffi {c = c} {h = h} {g = g} ep et ec eh eg b , trans (cong (primCF fi ty c ∷_) beq) (inj₂-injective eq′)

cgb-mono sc fi es compiled ep (inj₁ _) er ()
cgb-mono sc fi es compiled ep (inj₂ ty) er eq with rigidFree? ty in eg
... | nothing = case eq of λ ()
... | just g
  with C.compileFun C.Heap false (C.CScope.cimps sc) (C.cpolys sc) (C.declImps (C.CScope.ctele sc)) (funName fi) ty (funBody fi) in cf
... | inj₁ _ = case eq of λ ()
... | inj₂ irFun
      with C.compileEntries C.Heap false (C.extendScope sc (funName fi) ty) es in rec
...   | inj₁ _ = case eq of λ ()
...   | inj₂ rest =
        let (Ψ , se , d , f , ce) = compileFun-ce (C.cpolys sc) (C.declImps (C.CScope.ctele sc)) (C.CScope.cimps sc) ty fi irFun cf
            (b , beq) = ce-bundleP (C.extendScope sc (funName fi) ty) es rest rec
        in bcons {Ψ = Ψ} {se = se} {d = d} {f = f} {irFun = irFun} ep er eg ce cf b
         , trans (cong (C.mkCompiledFun (bare (funName fi)) (proj₁ (C.maybeWrapMain (funName fi) ty irFun))
                          (proj₂ (C.maybeWrapMain (funName fi) ty irFun)) (funIsPrimitive fi) ∷_) beq)
                 (inj₂-injective eq)

cgb-poly sc pfi es compiled (TE.failure _ , _) _ ()
cgb-poly sc pfi es compiled (TE.success Ψ se d f , w) cv eq =
  let (b , beq) = ce-bundleP (C.addEntry sc pfi) es compiled eq
  in bpoly {Ψ = Ψ} {se = se} {d = d} {f = f} (cong proj₁ cv) b , beq

ce-bundle : ∀ (sc : C.CScope) (es : List C.Entry) {compiled : List C.CompiledFun}
  → C.compileEntries C.Heap false sc es ≡ inj₂ compiled → FunBundle sc es
ce-bundle sc es {compiled} eq = proj₁ (ce-bundleP sc es compiled eq)

bundle→compiled≡compiled : ∀ (sc : C.CScope) (es : List C.Entry) (compiled : List C.CompiledFun)
  (eq : C.compileEntries C.Heap false sc es ≡ inj₂ compiled) → bundle→compiled (ce-bundle sc es eq) ≡ compiled
bundle→compiled≡compiled sc es compiled eq = proj₂ (ce-bundleP sc es compiled eq)

BMainExists : ∀ {sc es} → FunBundle sc es → Set
BMainExists bnil = ⊥
BMainExists (bffi _ _ _ _ _ rest) = BMainExists rest
BMainExists (bcons {fi = fi} {ty = ty} _ _ _ _ _ rest) =
  ((funName fi ≡ "main") × (funIsPrimitive fi ≡ false) × (ty ≡ EffUU)) ⊎ BMainExists rest
BMainExists (bpoly _ rest) = BMainExists rest

bf-dispatch : ∀ {P : Set} {ty} → IR ⌊ Unit ⌋ ⌊ ty ⌋ →
  Dec P → Dec (ty ≡ EffUU) → Bool → Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋) → Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋)
bf-dispatch irFun np tq true  cont = cont
bf-dispatch irFun (yes _) (yes refl) false cont = just (C.wrapMainAsEntry irFun)
bf-dispatch irFun (no _)  _          false cont = cont
bf-dispatch irFun (yes _) (no _)     false cont = cont

bundle-find : ∀ {sc es} → FunBundle sc es → Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋)
bundle-find bnil = nothing
bundle-find (bffi _ _ _ _ _ rest) = bundle-find rest
bundle-find (bcons {fi = fi} {ty = ty} {irFun = irFun} ep rf eg ce cf rest) =
  bf-dispatch irFun (funName fi ≟str "main") (ty ≟T EffUU) (funIsPrimitive fi) (bundle-find rest)
bundle-find (bpoly _ rest) = bundle-find rest

fa-head : ∀ {sc} (fi : FunInfo) (ty : Type) (irFun : IR ⌊ Unit ⌋ ⌊ ty ⌋)
  (cf : C.compileFun C.Heap false (C.CScope.cimps sc) (C.cpolys sc) (C.declImps (C.CScope.ctele sc))
          (funName fi) ty (funBody fi) ≡ inj₂ irFun)
  (rest-c : List C.CompiledFun) (rest-f : Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋)) →
  findMain rest-c ≡ rest-f →
  findMain (C.mkCompiledFun (bare (funName fi)) (proj₁ (C.maybeWrapMain (funName fi) ty irFun))
             (proj₂ (C.maybeWrapMain (funName fi) ty irFun)) (funIsPrimitive fi) ∷ rest-c)
    ≡ bf-dispatch irFun (funName fi ≟str "main") (ty ≟T EffUU) (funIsPrimitive fi) rest-f
fa-head {sc} fi ty irFun cf rest-c rest-f ih
  with funIsPrimitive fi
... | true = ih
... | false with funName fi ≟str "main"
...   | no ¬p = ih
...   | yes p with ty ≟T EffUU
...     | yes refl rewrite p = refl
...     | no ¬q rewrite p =
          ⊥-elim (¬q (compileFun-main-EffUU (C.CScope.cimps sc) (C.cpolys sc) (C.declImps (C.CScope.ctele sc)) ty (funBody fi) irFun cf))

find-agree : ∀ {sc es} (b : FunBundle sc es) → findMain (bundle→compiled b) ≡ bundle-find b
find-agree bnil = refl
find-agree (bffi _ _ _ _ _ rest) = find-agree rest
find-agree {sc} (bcons {fi = fi} {ty = ty} {irFun = irFun} ep rf eg ce cf rest) =
  fa-head {sc} fi ty irFun cf (bundle→compiled rest) (bundle-find rest) (find-agree rest)
find-agree (bpoly _ rest) = find-agree rest

bme→me : ∀ {sc es} (b : FunBundle sc es) → BMainExists b → MainIn (bundle→typed b)
bme→me (bffi _ _ _ _ _ rest) w = bme→me rest w
bme→me (bcons _ _ _ _ _ rest) (inj₁ (p , _ , e)) = inj₁ (p , e)
bme→me (bcons _ _ _ _ _ rest) (inj₂ w) = inj₂ (bme→me rest w)
bme→me (bpoly _ rest) w = bme→me rest w

bundle-realize : ∀ {sc es} (b : FunBundle sc es) → BMainExists b → Σ-syntax (Usage 0) (λ Ψ → Expr ∅ Ψ EffUU)
br-dispatch : ∀ {sc es ty} (fi : FunInfo)
  {Ψ : Usage (NamedCtx.size (ctxC sc))} {se : Expr (NamedCtx.debruijn (ctxC sc)) Ψ ty} {d f : ℕ}
  (ce : checkElab (ctxC sc) (funBody fi) ty ≡ TE.success Ψ se d f)
  (rt : FunBundle (C.extendScope sc (funName fi) ty) es) (w : BMainExists rt)
  → Dec (funName fi ≡ "main") → Dec (ty ≡ EffUU) → Σ-syntax (Usage 0) (λ Ψ' → Expr ∅ Ψ' EffUU)
bundle-realize (bffi _ _ _ _ _ rest) w = bundle-realize rest w
bundle-realize {sc} (bcons {fi = fi} {Ψ = Ψ} ep rf eg ce cf rest) (inj₁ (_ , _ , refl)) =
  Ψ , realize (check-sound (ctxC sc) (funBody fi) EffUU ce)
bundle-realize {sc} (bcons {fi = fi} {ty = ty} ep rf eg ce cf rest) (inj₂ w) =
  br-dispatch {sc} fi ce rest w (funName fi ≟str "main") (ty ≟T EffUU)
bundle-realize (bpoly _ rest) w = bundle-realize rest w
br-dispatch {sc} fi {Ψ = Ψ} ce rt w (yes _) (yes refl) = Ψ , realize (check-sound (ctxC sc) (funBody fi) EffUU ce)
br-dispatch fi ce rt w (no _)  _      = bundle-realize rt w
br-dispatch fi ce rt w (yes _) (no _) = bundle-realize rt w

realize-agree : ∀ {sc es} (b : FunBundle sc es) (bme : BMainExists b) →
  MC.mainRealized-go (bundle→typed b) (bme→me b bme) ≡ bundle-realize b bme
ra-head : ∀ {sc es ty} (fi : FunInfo)
  {Ψ : Usage (NamedCtx.size (ctxC sc))} {se : Expr (NamedCtx.debruijn (ctxC sc)) Ψ ty} {d f : ℕ}
  (ce : checkElab (ctxC sc) (funBody fi) ty ≡ TE.success Ψ se d f)
  (rt : FunBundle (C.extendScope sc (funName fi) ty) es) (w : BMainExists rt)
  (nd : Dec (funName fi ≡ "main")) (td : Dec (ty ≡ EffUU)) →
  MC.mrg-dispatch {sc = AS.scopeOf sc} {fi = fi} {es = es} (check-sound (ctxC sc) (funBody fi) ty ce)
      {bundle→typed rt} (bme→me rt w) nd td
  ≡ br-dispatch {sc} fi ce rt w nd td
ra-head fi ce rt w (yes _) (yes refl) = refl
ra-head fi ce rt w (no _)  _          = realize-agree rt w
ra-head fi ce rt w (yes _) (no _)     = realize-agree rt w
realize-agree (bffi _ _ _ _ _ rest) w = realize-agree rest w
realize-agree (bcons ep rf eg ce cf rest) (inj₁ (_ , _ , refl)) = refl
realize-agree {sc} (bcons {fi = fi} {ty = ty} ep rf eg ce cf rest) (inj₂ w) =
  ra-head {sc} fi ce rest w (funName fi ≟str "main") (ty ≟T EffUU)
realize-agree (bpoly _ rest) w = realize-agree rest w

bundle-find-exists : ∀ {sc es} (b : FunBundle sc es) {ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋}
  → bundle-find b ≡ just ir → BMainExists b
bundle-find-exists bnil ()
bundle-find-exists (bffi _ _ _ _ _ rest) eq = bundle-find-exists rest eq
bundle-find-exists (bpoly _ rest) eq = bundle-find-exists rest eq
bundle-find-exists (bcons {fi = fi} {ty = ty} {irFun = irFun} ep rf eg ce cf rest) eq
  with funName fi ≟str "main" | ty ≟T EffUU | funIsPrimitive fi
... | yes p | yes refl | false = inj₁ (p , refl , refl)
... | yes _ | yes refl | true  = inj₂ (bundle-find-exists rest eq)
... | yes _ | no _     | false = inj₂ (bundle-find-exists rest eq)
... | yes _ | no _     | true  = inj₂ (bundle-find-exists rest eq)
... | no _  | _        | false = inj₂ (bundle-find-exists rest eq)
... | no _  | _        | true  = inj₂ (bundle-find-exists rest eq)

irFun-main-form : ∀ (ctx : C.FunCtx) (polys : PolyCtx) (impsOf : C.String → C.FunCtx)
  (body : RawExpr) (irFun : IR ⌊ Unit ⌋ ⌊ EffUU ⌋)
  {Ψ : Usage 0} {se : Expr ∅ Ψ EffUU} {d f : ℕ}
  (ce : checkElab (ctxWithImportsAndPolys ctx polys) body EffUU
          ≡ TE.success Ψ se d f)
  (cf : C.compileFun C.Heap false ctx polys impsOf "main" EffUU body ≡ inj₂ irFun) →
  irFun ≡ elaborateFull C.Heap (resolveExpr polys impsOf (("main" , EffUU) ∷ ctx) 0 se)
irFun-main-form ctx polys impsOf body irFun ce cf =
  inj₂-injective (trans (sym cf) (cong (C.compileFunBody-aux C.Heap false ctx polys impsOf "main" EffUU refl) ce))

MNodeAt : Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋) → Σ-syntax (Usage 0) (λ Ψ' → Expr ∅ Ψ' EffUU) → Set
MNodeAt fr rr =
  Σ-syntax C.CScope (λ msc → Σ-syntax RawExpr (λ mbody →
  Σ-syntax (Usage 0) (λ mΨ → Σ-syntax (Expr ∅ mΨ EffUU) (λ mse → Σ-syntax ℕ (λ md → Σ-syntax ℕ (λ mf →
  Σ-syntax (checkElab (ctxC msc) mbody EffUU ≡ TE.success mΨ mse md mf) (λ mce →
    (fr ≡ just (C.wrapMainAsEntry (elaborateFull C.Heap
            (resolveExpr (C.cpolys msc) (C.declImps (C.CScope.ctele msc)) (("main" , EffUU) ∷ C.CScope.cimps msc) 0 mse))))
  × (rr ≡ (mΨ , realize (check-sound (ctxC msc) mbody EffUU mce))))))))))

bundle-main-node : ∀ {sc es} (b : FunBundle sc es)
  (bme : BMainExists b) → MNodeAt (bundle-find b) (bundle-realize b bme)
bmn-dispatch : ∀ {sc es ty} (fi : FunInfo)
  {Ψ : Usage (NamedCtx.size (ctxC sc))} {se : Expr (NamedCtx.debruijn (ctxC sc)) Ψ ty}
  {d f : ℕ} {irFun : IR ⌊ Unit ⌋ ⌊ ty ⌋}
  (ce : checkElab (ctxC sc) (funBody fi) ty ≡ TE.success Ψ se d f)
  (cf : C.compileFun C.Heap false (C.CScope.cimps sc) (C.cpolys sc) (C.declImps (C.CScope.ctele sc))
          (funName fi) ty (funBody fi) ≡ inj₂ irFun)
  (ep : funIsPrimitive fi ≡ false)
  (rt : FunBundle (C.extendScope sc (funName fi) ty) es) (w : BMainExists rt)
  (nd : Dec (funName fi ≡ "main")) (td : Dec (ty ≡ EffUU))
  → MNodeAt (bf-dispatch irFun nd td (funIsPrimitive fi) (bundle-find rt)) (br-dispatch {sc} fi ce rt w nd td)
bundle-main-node (bffi _ _ _ _ _ rest) w = bundle-main-node rest w
bundle-main-node (bpoly _ rest) w = bundle-main-node rest w
bundle-main-node {sc} (bcons {fi = fi} {Ψ = Ψ} {se = se} {d = d} {f = f} {irFun = irFun} ep rf eg ce cf rest) (inj₁ (p , pr , refl))
  rewrite p | pr with "main" ≟str "main" | EffUU ≟T EffUU
... | yes refl | yes refl =
      sc , funBody fi , Ψ , se , d , f , ce ,
        cong (λ x → just (C.wrapMainAsEntry x))
          (irFun-main-form (C.CScope.cimps sc) (C.cpolys sc) (C.declImps (C.CScope.ctele sc)) (funBody fi) irFun ce cf) , refl
... | yes _    | no ¬q = ⊥-elim (¬q refl)
... | no ¬r    | _     = ⊥-elim (¬r refl)
bundle-main-node {sc} (bcons {fi = fi} {ty = ty} ep rf eg ce cf rest) (inj₂ w) =
  bmn-dispatch {sc} fi ce cf ep rest w (funName fi ≟str "main") (ty ≟T EffUU)
bmn-dispatch {sc} fi {Ψ = Ψ} {se = se} {d = d} {f = f} {irFun = irFun} ce cf ep rt w (yes p) (yes refl)
  rewrite ep | p =
  sc , funBody fi , Ψ , se , d , f , ce ,
    cong (λ x → just (C.wrapMainAsEntry x))
      (irFun-main-form (C.CScope.cimps sc) (C.cpolys sc) (C.declImps (C.CScope.ctele sc)) (funBody fi) irFun ce cf) , refl
bmn-dispatch fi ce cf ep rt w (no _)  td rewrite ep = bundle-main-node rt w
bmn-dispatch fi ce cf ep rt w (yes _) (no _) rewrite ep = bundle-main-node rt w
