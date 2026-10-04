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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Function using (case_of_)
open import Once.Compile using (findMain; moduleToIR; moduleToIR-aux; mainCall)
open import Once.Adequacy.MainIRForm using (findMain-skip; compileFun-main-EffUU; bare-injective)

open import Once.Type using (Type; Unit; _⇒[_]_; mk-kind; Many; eff)
open import Once.IR using (IR)
open import Once.IRTy using (⌊_⌋)
open import Once.Surface.Syntax using (Expr; ∅; Usage; [])
open import Once.Surface.Elaborate using (elaborate; elaborateFull)
-- Plan 0.49 / D063 C4: the elaborator-free reference elaboration. Importing it
-- here (proof layer) is fine — `realize` itself does NOT import `checkElab`.
open import Once.Denotation.Realize using (realize)
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.Spec.Module
  using (EffUU; ModTele; []; ffi; mono; poly; ModuleTyped-ef; ModuleTyped;
         MainsEffUU; MainIn; HasValidMain-ef; HasValidMain; ctxOf; addImp)
import Once.TypeCheck.Elaborate as TE
open import Once.Functor.Decide using (isConcrete?-complete)
open import Once.Type.Honest using (honest?-complete)
open import Once.Type.Rigid using (rigidFree?-complete)

cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {a a′ b b′ c c′} → a ≡ a′ → b ≡ b′ → c ≡ c′ → f a b c ≡ f a′ b′ c′
cong₃ f refl refl refl = refl
open import Once.Surface.Context using (zeroUsage)
import Once.Surface.Syntax as Srf
open import Once.TypeCheck.Elaborate
  using (checkElab; ctxWithImportsAndPolys; PolyCtx)
open import Once.Type.DecEq using (_≟T_)
open import Once.TypeCheck.ElaborateProofs using (resolveExpr)
open import Once.TypeCheck.Judgment using (_⊢ᶜ_∶_⨾_)
open import Once.TypeCheck.Completeness using (check-complete)
import Once.Compile as C
import Once.Adequacy.AcceptSound as AS
open import Once.Parser using (FunInfo)
open FunInfo

-- `EffUU` is in `Once.Spec.Module` (plan 0.84).

------------------------------------------------------------------------
-- (1) a `⊢ᶜ` derivation ⇒ the body compiles, via `check-complete`.
------------------------------------------------------------------------

compileFunBody-complete : ∀ (ctx : C.FunCtx) (polys : PolyCtx) (impsOf : C.String → C.FunCtx)
  (name : String) (ty : Type) (body : RawExpr) {Ψ : Usage 0} →
  (ctxWithImportsAndPolys ctx polys) ⊢ᶜ body ∶ ty ⨾ Ψ →
  Σ-syntax (IR ⌊ Unit ⌋ ⌊ ty ⌋) (λ irFun →
    C.compileFunBody C.Heap false ctx polys impsOf name ty body ≡ inj₂ irFun)
-- D143: `Ψ : Usage 0` must be MATCHED, not just quantified: `Usage` is a
-- `data` (no eta), so `∅ ↾ Ψ` is stuck until `Ψ` is `[]`, and the
-- elaborated IR's domain `⌊ ⟦ ∅ ↾ Ψ ⟧ᶜ ⌋` will not reduce to `Unit`.
compileFunBody-complete ctx polys impsOf name ty body {[]} deriv =
  succ (TE.checkElabV (ctxWithImportsAndPolys ctx polys) body ty) (proj₂ (proj₂ (proj₂ (check-complete deriv))))
  where
    succ : ∀ (cr : TE.VerifiedCheckResult (ctxWithImportsAndPolys ctx polys) body ty) {eE d f}
         → proj₁ cr ≡ TE.success [] eE d f
         → Σ-syntax (IR ⌊ Unit ⌋ ⌊ ty ⌋) (λ irFun → C.compileFunBody-aux C.Heap false ctx polys impsOf name ty refl cr ≡ inj₂ irFun)
    succ (TE.success _ _ _ _ , _) refl = _ , refl

------------------------------------------------------------------------
-- (2) ⇒ the function compiles. `compileFun` dispatches on `name == "main"`
-- = `isYes (name ≟ "main")`, so casing `name ≟str "main"` reduces it.
------------------------------------------------------------------------

compileFun-complete : ∀ (ctx : C.FunCtx) (polys : PolyCtx) (impsOf : C.String → C.FunCtx)
  (name : String) (ty : Type) (body : RawExpr) {Ψ : Usage 0} →
  (name ≡ "main" → ty ≡ EffUU) →
  (ctxWithImportsAndPolys ctx polys) ⊢ᶜ body ∶ ty ⨾ Ψ →
  Σ-syntax (IR ⌊ Unit ⌋ ⌊ ty ⌋) (λ irFun →
    C.compileFun C.Heap false ctx polys impsOf name ty body ≡ inj₂ irFun)
compileFun-complete ctx polys impsOf name ty body main-ok deriv with name ≟str "main"
... | no ¬p = compileFunBody-complete ctx polys impsOf name ty body deriv
... | yes p with main-ok p
...   | refl = compileFunBody-complete ctx polys impsOf name EffUU body deriv

------------------------------------------------------------------------
-- Derivation-indexed "valid main" predicates (over `AllFunsTyped`'s `ty`).
------------------------------------------------------------------------

-- `AllMainEffUU`/`MainExists` are in `Once.Spec.Module` (plan 0.84).

------------------------------------------------------------------------
-- (3) ⇒ the whole list compiles (forward mirror of `caf-go-sound`).
------------------------------------------------------------------------

------------------------------------------------------------------------
-- D241 (plan 0.103 6c′): the compiler ACCEPTS every well-typed telescope.
------------------------------------------------------------------------

scopeOf = AS.scopeOf

checkOK-complete : ∀ {ctx e T} (r : TE.VerifiedCheckResult ctx e T) {Ψ eE d f}
  → proj₁ r ≡ TE.success Ψ eE d f → C.checkOK r ≡ inj₂ tt
checkOK-complete (TE.failure _ , _) ()
checkOK-complete (TE.success _ _ _ _ , _) _ = refl

-- The telescope walk, one entry at a time: each step is a chain of
-- `cong`s through the explicit-aux stages.
ce-complete : ∀ (sc : C.CScope) {es : List C.Entry} (mt : ModTele (scopeOf sc) es) → MainsEffUU mt →
  Σ-syntax (List C.CompiledFun) (λ cfs → C.compileEntries C.Heap false sc es ≡ inj₂ cfs)
ce-complete sc [] _ = [] , refl
ce-complete sc (ffi {fi = fi} {ty = ty} {es = es} ep et c h g rest) mrest =
  let (cfs , rec) = ce-complete (C.extendScope sc (funName fi) ty) rest mrest
      (c′ , ec) = isConcrete?-complete c
      (h′ , eh) = honest?-complete {ty} h
  in _ , trans (cong (C.ce-fun C.Heap false sc fi es) ep)
           (trans (cong (C.ce-prim C.Heap false sc fi es) et)
             (trans (cong₃ (C.ce-prim-conc C.Heap false sc fi es ty) ec eh (rigidFree?-complete g))
                    (cong (C.consCF _) rec)))
ce-complete sc (mono {fi = fi} {ty = ty} {es = es} ep er g deriv rest) (main-ok , mrest) =
  let (irFun , cf-eq) = compileFun-complete (C.CScope.cimps sc) (C.cpolys sc) (C.declImps (C.CScope.ctele sc))
                          (funName fi) ty (funBody fi) main-ok deriv
      (cfs , rec) = ce-complete (C.extendScope sc (funName fi) ty) rest mrest
  in _ , trans (cong (C.ce-fun C.Heap false sc fi es) ep)
           (trans (cong (C.ce-mono C.Heap false sc fi es) er)
             (trans (cong (C.ce-mono-g C.Heap false sc fi es ty) (rigidFree?-complete g))
             (trans (cong (C.ce-mono-ir C.Heap false sc fi es ty) cf-eq)
                    (cong (C.consCF (C.mkCompiledFun (bare (funName fi)) ty irFun (funIsPrimitive fi))) rec))))
ce-complete sc (poly {pfi = pfi} {es = es} deriv rest) mrest =
  let (_ , _ , _ , ce) = check-complete deriv
      (cfs , rec) = ce-complete (C.addEntry sc pfi) rest mrest
  in cfs , trans (cong (C.ce-poly C.Heap false sc pfi es) (checkOK-complete _ ce)) rec

open C.CompiledFun using (cfIsPrimitive)

findMain-skip-prim : ∀ (cf : C.CompiledFun) (rest : List C.CompiledFun) →
  cfIsPrimitive cf ≡ true → findMain (cf ∷ rest) ≡ findMain rest
findMain-skip-prim cf rest pp rewrite pp = refl

FindResult : C.CScope → List C.Entry → Set
FindResult sc es =
  Σ-syntax (List C.CompiledFun) (λ compiled → Σ-syntax (IR ⌊ Unit ⌋ ⌊ Unit ⌋) (λ ir →
    (C.compileEntries C.Heap false sc es ≡ inj₂ compiled) × (findMain compiled ≡ just ir)))

-- The compiled telescope contains `main`, and `findMain` finds it.
ce-find-complete : ∀ (sc : C.CScope) {es : List C.Entry} (mt : ModTele (scopeOf sc) es) →
  MainsEffUU mt → MainIn mt → FindResult sc es
ce-find-complete sc [] _ ()
ce-find-complete sc (ffi {fi = fi} {ty = ty} {es = es} ep et c h g rest) mrest mi =
  let (cfs , ir , rec , fm) = ce-find-complete (C.extendScope sc (funName fi) ty) rest mrest mi
      (c′ , ec) = isConcrete?-complete c
      (h′ , eh) = honest?-complete {ty} h
  in _ , ir
     , trans (cong (C.ce-fun C.Heap false sc fi es) ep)
         (trans (cong (C.ce-prim C.Heap false sc fi es) et)
           (trans (cong₃ (C.ce-prim-conc C.Heap false sc fi es ty) ec eh (rigidFree?-complete g))
                  (cong (C.consCF _) rec)))
     , fm
ce-find-complete sc (poly {pfi = pfi} {es = es} deriv rest) mrest mi =
  let (_ , _ , _ , ce) = check-complete deriv
      (cfs , ir , rec , fm) = ce-find-complete (C.addEntry sc pfi) rest mrest mi
  in cfs , ir , trans (cong (C.ce-poly C.Heap false sc pfi es) (checkOK-complete _ ce)) rec , fm
ce-find-complete sc (mono {fi = fi} {ty = ty} {es = es} ep er g deriv rest) (main-ok , mrest) mi =
  step mi (funName fi ≟str "main")
  where
    cfc = compileFun-complete (C.CScope.cimps sc) (C.cpolys sc) (C.declImps (C.CScope.ctele sc))
            (funName fi) ty (funBody fi) main-ok deriv
    irFun = proj₁ cfc
    chain : ∀ {r} → C.compileEntries C.Heap false (C.extendScope sc (funName fi) ty) es ≡ r
          → C.compileEntries C.Heap false sc (C.e-fun fi ∷ es) ≡ C.consCF (C.mkCompiledFun (bare (funName fi)) ty irFun (funIsPrimitive fi)) r
    chain rec = trans (cong (C.ce-fun C.Heap false sc fi es) ep)
                  (trans (cong (C.ce-mono C.Heap false sc fi es) er)
                    (trans (cong (C.ce-mono-g C.Heap false sc fi es ty) (rigidFree?-complete g))
                    (trans (cong (C.ce-mono-ir C.Heap false sc fi es ty) (proj₂ cfc))
                           (cong (C.consCF (C.mkCompiledFun (bare (funName fi)) ty irFun (funIsPrimitive fi))) rec))))
    cf0 : C.CompiledFun
    cf0 = C.mkCompiledFun (bare (funName fi)) ty irFun (funIsPrimitive fi)
    -- A `main : IO Unit` definition is found where it stands.
    here : funName fi ≡ "main" → ty ≡ EffUU → ∀ cfs
         → Σ-syntax (IR ⌊ Unit ⌋ ⌊ Unit ⌋) (λ ir → findMain (cf0 ∷ cfs) ≡ just ir)
    here nm te cfs = found (funName fi) ty irFun (funIsPrimitive fi) nm te ep
      where
        found : ∀ (n : String) (t : Type) (g : IR ⌊ Unit ⌋ ⌊ t ⌋) (b : Bool) → n ≡ "main" → t ≡ EffUU → b ≡ false
          → Σ-syntax (IR ⌊ Unit ⌋ ⌊ Unit ⌋) (λ ir →
              findMain (C.mkCompiledFun (bare n) t g b ∷ cfs) ≡ just ir)
        found .("main") .EffUU g .false refl refl refl = mainCall , refl
    step : ((funName fi ≡ "main") × (ty ≡ EffUU)) ⊎ MainIn rest → Dec (funName fi ≡ "main") → FindResult sc (C.e-fun fi ∷ es)
    step (inj₁ (nm , te)) _ =
      let (cfs , rec) = ce-complete (C.extendScope sc (funName fi) ty) rest mrest
          (ir , fm) = here nm te cfs
      in cf0 ∷ cfs , ir , chain rec , fm
    step (inj₂ mi′) (yes nm) =
      let (cfs , rec) = ce-complete (C.extendScope sc (funName fi) ty) rest mrest
          (ir , fm) = here nm (main-ok nm) cfs
      in cf0 ∷ cfs , ir , chain rec , fm
    step (inj₂ mi′) (no ¬nm) =
      let (cfs , ir , rec , fm) = ce-find-complete (C.extendScope sc (funName fi) ty) rest mrest mi′
      in cf0 ∷ cfs , ir , chain rec , trans (findMain-skip cf0 cfs (λ e → ¬nm (bare-injective e))) fm

moduleToIR-complete : ∀ (m : C.Module) (mt : ModuleTyped m) → HasValidMain m mt →
  Σ-syntax (IR ⌊ Unit ⌋ ⌊ Unit ⌋) (λ ir → moduleToIR m ≡ just ir)
moduleToIR-complete m mt hvm with C.extractFunctions (C.extractAliases m) m
... | inj₂ es with ce-find-complete C.emptyCScope mt (proj₁ hvm) (proj₂ hvm)
...   | (compiled , ir , ce-eq , fm-eq) = ir , trans (cong moduleToIR-aux ce-eq) fm-eq

------------------------------------------------------------------------
-- The realized `main`: the surface expression of its derivation.
------------------------------------------------------------------------

ce-mains : ∀ (sc : C.CScope) {es} (mt : ModTele (scopeOf sc) es) {cfs}
  → C.compileEntries C.Heap false sc es ≡ inj₂ cfs → MainsEffUU mt
ce-mains sc [] _ = tt
ce-mains sc (ffi {fi = fi} {ty = ty} {es = es} ep et c h g rest) eq =
  ce-mains (C.extendScope sc (funName fi) ty) rest
    (proj₂ (AS.consCF-inj _ (subst (λ r → r ≡ inj₂ _)
      (trans (cong (C.ce-fun C.Heap false sc fi es) ep)
        (trans (cong (C.ce-prim C.Heap false sc fi es) et)
               (cong₃ (C.ce-prim-conc C.Heap false sc fi es ty) (proj₂ (isConcrete?-complete c)) (proj₂ (honest?-complete {ty} h)) (rigidFree?-complete g))))
      eq)))
ce-mains sc (poly {pfi = pfi} {es = es} deriv rest) eq =
  let (_ , _ , _ , ce) = check-complete deriv
  in ce-mains (C.addEntry sc pfi) rest
       (subst (λ r → r ≡ inj₂ _) (cong (C.ce-poly C.Heap false sc pfi es) (checkOK-complete _ ce)) eq)
ce-mains sc (mono {fi = fi} {ty = ty} {es = es} ep er g deriv rest) {cfs} eq = go _ refl
  where
    eq′ = subst (λ r → r ≡ inj₂ cfs)
            (trans (cong (C.ce-fun C.Heap false sc fi es) ep)
              (trans (cong (C.ce-mono C.Heap false sc fi es) er) (cong (C.ce-mono-g C.Heap false sc fi es ty) (rigidFree?-complete g)))) eq
    go : ∀ ri → C.compileFun C.Heap false (C.CScope.cimps sc) (C.cpolys sc) (C.declImps (C.CScope.ctele sc))
                  (funName fi) ty (funBody fi) ≡ ri
       → (funName fi ≡ "main" → ty ≡ EffUU) × MainsEffUU rest
    go (inj₁ _) cf = case subst (λ r → C.ce-mono-ir C.Heap false sc fi es ty r ≡ inj₂ cfs) cf eq′ of λ ()
    go (inj₂ irFun) cf =
      (λ p → compileFun-main-EffUU (C.CScope.cimps sc) (C.cpolys sc) (C.declImps (C.CScope.ctele sc)) ty (funBody fi) irFun
               (subst (λ nm → C.compileFun C.Heap false (C.CScope.cimps sc) (C.cpolys sc) (C.declImps (C.CScope.ctele sc)) nm ty (funBody fi) ≡ inj₂ irFun) p cf))
      , ce-mains (C.extendScope sc (funName fi) ty) rest
          (proj₂ (AS.consCF-inj _ (subst (λ r → C.ce-mono-ir C.Heap false sc fi es ty r ≡ inj₂ cfs) cf eq′)))

ce-mainexists : ∀ (sc : C.CScope) {es} (mt : ModTele (scopeOf sc) es) {cfs} {ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋}
  → C.compileEntries C.Heap false sc es ≡ inj₂ cfs → findMain cfs ≡ just ir → MainIn mt
ce-mainexists sc [] eq fm = case subst (λ c → findMain c ≡ just _) (sym (inj₂-injective eq)) fm of λ ()
ce-mainexists sc (ffi {fi = fi} {ty = ty} {es = es} ep et c h g rest) {cfs} {ir} eq fm =
  let eq′ = subst (λ r → r ≡ inj₂ cfs)
              (trans (cong (C.ce-fun C.Heap false sc fi es) ep)
                (trans (cong (C.ce-prim C.Heap false sc fi es) et)
                       (cong₃ (C.ce-prim-conc C.Heap false sc fi es ty) (proj₂ (isConcrete?-complete c)) (proj₂ (honest?-complete {ty} h)) (rigidFree?-complete g))))
              eq
      cfP = C.mkCompiledFun (bare (funName fi)) ty
              (elaborateFull C.Heap (Srf.sigOp {Γ = Srf.∅} (bare (funName fi)) (proj₁ (isConcrete?-complete c)))) true
      (rest-cfs , rec) = AS.consCF-inj {cf = cfP} _ eq′
      cons-eq = trans (sym eq′) (cong (C.consCF cfP) rec)
      fm′ = subst (λ c → findMain c ≡ just ir) (inj₂-injective cons-eq) fm
  in ce-mainexists (C.extendScope sc (funName fi) ty) rest rec (trans (sym (findMain-skip-prim cfP rest-cfs refl)) fm′)
ce-mainexists sc (poly {pfi = pfi} {es = es} deriv rest) eq fm =
  let (_ , _ , _ , ce) = check-complete deriv
  in ce-mainexists (C.addEntry sc pfi) rest
       (subst (λ r → r ≡ inj₂ _) (cong (C.ce-poly C.Heap false sc pfi es) (checkOK-complete _ ce)) eq) fm
ce-mainexists sc (mono {fi = fi} {ty = ty} {es = es} ep er g deriv rest) {cfs} {ir} eq fm = go _ refl
  where
    eq′ = subst (λ r → r ≡ inj₂ cfs)
            (trans (cong (C.ce-fun C.Heap false sc fi es) ep)
              (trans (cong (C.ce-mono C.Heap false sc fi es) er) (cong (C.ce-mono-g C.Heap false sc fi es ty) (rigidFree?-complete g)))) eq
    go : ∀ ri → C.compileFun C.Heap false (C.CScope.cimps sc) (C.cpolys sc) (C.declImps (C.CScope.ctele sc))
                  (funName fi) ty (funBody fi) ≡ ri
       → ((funName fi ≡ "main") × (ty ≡ EffUU)) ⊎ MainIn rest
    go (inj₁ _) cf = case subst (λ r → C.ce-mono-ir C.Heap false sc fi es ty r ≡ inj₂ cfs) cf eq′ of λ ()
    go (inj₂ irFun) cf = decide (funName fi ≟str "main")
      where
        decide : Dec (funName fi ≡ "main") → ((funName fi ≡ "main") × (ty ≡ EffUU)) ⊎ MainIn rest
        decide (yes p) = inj₁ (p , compileFun-main-EffUU (C.CScope.cimps sc) (C.cpolys sc) (C.declImps (C.CScope.ctele sc)) ty (funBody fi) irFun
                                    (subst (λ nm → C.compileFun C.Heap false (C.CScope.cimps sc) (C.cpolys sc) (C.declImps (C.CScope.ctele sc)) nm ty (funBody fi) ≡ inj₂ irFun) p cf))
        decide (no ¬p) =
          let eq″ = subst (λ r → C.ce-mono-ir C.Heap false sc fi es ty r ≡ inj₂ cfs) cf eq′
              cf0 = C.mkCompiledFun (bare (funName fi)) ty irFun (funIsPrimitive fi)
              (rest-cfs , rec) = AS.consCF-inj {cf = cf0} _ eq″
              cons-eq : C.consCF cf0 (C.compileEntries C.Heap false (C.extendScope sc (funName fi) ty) es) ≡ inj₂ (cf0 ∷ rest-cfs)
              cons-eq = cong (C.consCF cf0) rec
              fm′ = subst (λ c → findMain c ≡ just ir) (inj₂-injective (trans (sym eq″) cons-eq)) fm
          in inj₂ (ce-mainexists (C.extendScope sc (funName fi) ty) rest rec
                     (trans (sym (findMain-skip cf0 rest-cfs (λ e → ¬p (bare-injective e)))) fm′))

moduleToIR-sound : ∀ (m : C.Module) (mt : ModuleTyped m) {ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋} →
  moduleToIR m ≡ just ir → HasValidMain m mt
moduleToIR-sound m mt mi with C.extractFunctions (C.extractAliases m) m
... | inj₂ es with C.compileEntries C.Heap false C.emptyCScope es in ce-eq
...   | inj₁ _ = case mi of λ ()
...   | inj₂ compiled = ce-mains C.emptyCScope mt ce-eq , ce-mainexists C.emptyCScope mt ce-eq mi
