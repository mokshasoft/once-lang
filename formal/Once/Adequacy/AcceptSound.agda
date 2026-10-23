-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.AcceptSound — front-end SOUNDNESS (Plan 0.48 Phase 1)
--
-- The compiler's front-end accepts ONLY genuinely well-typed programs:
-- if `compileResolvedModule` succeeds, every function has a DECLARATIVE
-- typing derivation `ctx ⊢ᶜ body ∶ ty ⨾ Ψ` (the judgment in
-- `Once.Internal.Typing`, INDEPENDENT of the elaborator function). This
-- is what makes `⟦_⟧⊥`'s domain genuine rather than true-by-construction:
-- the meaning is defined only for programs the independent judgment admits.
--
-- Built on `VerifiedTypeChecker.tcCheck-sound` (`checkElab ≡ success ⇒ ⊢ᶜ`),
-- lifted through the explicit-arg `…-aux` compile pipeline (no `with`-bite),
-- mirroring `Once.Adequacy.MainBuilds`.
------------------------------------------------------------------------

module Once.Adequacy.AcceptSound where

open import Once.TypeCheck.DualWitness using (DI)
open import Once.Internal.Type.Instance using (kindsOf; arityOf)
open import Once.TypeCheck.Classify using (ctxAt)
open import Once.TypeCheck.Classify using (TopCtx; ctxWithImportsAndPolys)
open import Data.Bool using (Bool; false; true)
open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Once.Internal.Principal using (below)
open import Once.Adequacy.PrincipalDecide using (firstChecking-sound)
open import Data.String using (String; _==_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.IR using (IR)
open import Once.IRTy using (⌊_⌋)
open import Once.Spec.Type using (Unit; Type)
import Once.Compile as C
import Once.IR as IR
import Once.Parser as Parser
import Once.Internal.Context as Srf
import Once.Surface.Syntax as Srf
open import Once.TypeCheck.Elaborate as TE using ()
import Once.Internal.Typing.Scope as Classify
open import Once.Internal.Typing.Scope using (NamedCtx)
open import Once.Internal.Syntax using (RawExpr)
open import Once.Internal.Typing using (_⊢ᶜ_∶_⨾_; _⊢ᵢ_∶_⨾_)
open import Once.Internal.Type.DecEq using (_≟T_)
open import Relation.Nullary using (Dec; yes; no)
open import Once.Internal.Module
  using (Scope; scope; ModTele; []; ffi; mono; poly; ModuleTyped-ef; ModuleTyped; MonoBody; MonoWit; mder)
open import Once.Internal.Type.Instance using (rigidOf)
open import Once.Internal.Type.WellFormed using (IsConcrete)
open import Once.Functor.Decide using (isConcrete?)
open import Once.Internal.Type.Honest using (HonestFFI; honest?)
open import Once.Internal.Context using (zeroUsage)
import Once.Surface.Context
open import Data.Maybe using (Maybe; nothing)
-- Import `check-sound` DIRECTLY from `Soundness` (not via `Verified`, which
-- transitively pulls in the still-rotted `ErrorProofs`; soundness needs only
-- this): `checkElab ctx e T ≡ success … ⇒ ctx ⊢ᶜ e ∶ T ⨾ Ψ`.
open import Once.TypeCheck.Soundness using (check-sound)
open import Once.Compile using (moduleToIR)
open import Once.Adequacy.MainBuilds using (moduleToIR-inj₂)
import Once.Parser.Module.Core as P
import Data.String as String
import Once.Parser.Module as Module

------------------------------------------------------------------------
-- Leaf — a successful `compileFunBody` means `checkElab` succeeded, so its
-- body has a declarative check-mode derivation.
------------------------------------------------------------------------

compileFunBody-aux-success : ∀ {nctx : NamedCtx 0} {body : RawExpr}
  (doOpt : Bool) (ctx : TopCtx) (polys : Classify.PolyCtx) (impsOf : String.String → TopCtx)
  (name : String) (ty : Type) (δ : Srf.⟦ NamedCtx.debruijn nctx ⟧ᶜ ≡ Unit)
  (cr : TE.VerifiedCheckResult nctx body ty) {ir : IR ⌊ Unit {0} ⌋ ⌊ ty ⌋} →
  C.compileFunBody-aux IR.Heap doOpt ctx polys impsOf name ty δ cr ≡ inj₂ ir →
  Σ-syntax (Srf.Usage (NamedCtx.size nctx)) (λ Ψ → Σ-syntax (Srf.Expr (NamedCtx.debruijn nctx) Ψ ty) (λ se →
    Σ-syntax ℕ (λ d → Σ-syntax ℕ (λ f → proj₁ cr ≡ TE.success Ψ se d f))))
compileFunBody-aux-success doOpt ctx polys impsOf name ty δ (TE.failure err , _) ()
compileFunBody-aux-success doOpt ctx polys impsOf name ty δ (TE.success Ψ se d f , _) eq =
  Ψ , se , d , f , refl

-- …and its witness.
compileFunBody-aux-wit : ∀ {nctx : NamedCtx 0} {body : RawExpr}
  (doOpt : Bool) (ctx : TopCtx) (polys : Classify.PolyCtx) (impsOf : String.String → TopCtx)
  (name : String) (ty : Type) (δ : Srf.⟦ NamedCtx.debruijn nctx ⟧ᶜ ≡ Unit)
  (cr : TE.VerifiedCheckResult nctx body ty) → TE.checkElabV nctx body ty ≡ cr → {ir : IR ⌊ Unit {0} ⌋ ⌊ ty ⌋} →
  C.compileFunBody-aux IR.Heap doOpt ctx polys impsOf name ty δ cr ≡ inj₂ ir →
  Σ-syntax (Srf.Usage (NamedCtx.size nctx)) (λ Ψ → MonoWit (just ty) nctx body ty Ψ)
compileFunBody-aux-wit doOpt ctx polys impsOf name ty δ (TE.failure err , _) _ ()
compileFunBody-aux-wit doOpt ctx polys impsOf name ty δ (TE.success Ψ se d f , w) ec eq = Ψ , se , d , f , w , ec

compileFunBody-sound : ∀ (doOpt : Bool) (ctx : TopCtx) (polys : Classify.PolyCtx) (impsOf : String.String → TopCtx)
  (name : String) (ty : Type) (expr : RawExpr) {ir : IR ⌊ Unit {0} ⌋ ⌊ ty ⌋} →
  C.compileFunBody IR.Heap doOpt ctx polys impsOf name ty expr ≡ inj₂ ir →
  Σ-syntax (Srf.Usage (NamedCtx.size (ctxWithImportsAndPolys ctx polys)))
    (λ Ψ → MonoWit (just ty) (ctxWithImportsAndPolys ctx polys) expr ty Ψ)
compileFunBody-sound doOpt ctx polys impsOf name ty expr eq =
  compileFunBody-aux-wit doOpt ctx polys impsOf name ty refl (TE.checkElabV (ctxWithImportsAndPolys ctx polys) expr ty) refl eq

------------------------------------------------------------------------
-- The INDEPENDENT module-validity predicate: every function (threading the
-- accumulated `FunCtx`) resolves a type and has a DECLARATIVE check-mode
-- derivation. Mirrors `compileAllFuns-go`'s context threading, but speaks
-- ONLY the judgment `_⊢ᶜ_∶_⨾_` — no elaborator function appears.
------------------------------------------------------------------------

-- The relation is in `Once.Internal.Module` (plan 0.84).

------------------------------------------------------------------------
-- Layer 1 — `compileFun` accepts ⇒ its body has a derivation.
------------------------------------------------------------------------

compileFun-main-aux-sound : ∀ (doOpt : Bool) (ctx : TopCtx) (polys : Classify.PolyCtx) (impsOf : String.String → TopCtx)
  (name : String) (ty : Type) (expr : RawExpr) (vm : String ⊎ ⊤) {ir : IR ⌊ Unit {0} ⌋ ⌊ ty ⌋} →
  C.compileFun-main-aux IR.Heap doOpt ctx polys impsOf name ty expr vm ≡ inj₂ ir →
  Σ-syntax (Srf.Usage (NamedCtx.size (ctxWithImportsAndPolys ctx polys)))
    (λ Ψ → MonoWit (just ty) (ctxWithImportsAndPolys ctx polys) expr ty Ψ)
compileFun-main-aux-sound doOpt ctx polys impsOf name ty expr (inj₁ err) ()
compileFun-main-aux-sound doOpt ctx polys impsOf name ty expr (inj₂ _) eq =
  compileFunBody-sound doOpt ctx polys impsOf name ty expr eq

compileFun-aux-sound : ∀ (doOpt : Bool) (ctx : TopCtx) (polys : Classify.PolyCtx) (impsOf : String.String → TopCtx)
  (name : String) (ty : Type) (expr : RawExpr) (b : Bool) {ir : IR ⌊ Unit {0} ⌋ ⌊ ty ⌋} →
  C.compileFun-aux IR.Heap doOpt ctx polys impsOf name ty expr b ≡ inj₂ ir →
  Σ-syntax (Srf.Usage (NamedCtx.size (ctxWithImportsAndPolys ctx polys)))
    (λ Ψ → MonoWit (just ty) (ctxWithImportsAndPolys ctx polys) expr ty Ψ)
compileFun-aux-sound doOpt ctx polys impsOf name ty expr true eq =
  compileFun-main-aux-sound doOpt ctx polys impsOf name ty expr (C.validateMain ty) eq
compileFun-aux-sound doOpt ctx polys impsOf name ty expr false eq =
  compileFunBody-sound doOpt ctx polys impsOf name ty expr eq

compileFun-sound : ∀ (doOpt : Bool) (ctx : TopCtx) (polys : Classify.PolyCtx) (impsOf : String.String → TopCtx)
  (name : String) (ty : Type) (expr : RawExpr) {ir : IR ⌊ Unit {0} ⌋ ⌊ ty ⌋} →
  C.compileFun IR.Heap doOpt ctx polys impsOf name ty expr ≡ inj₂ ir →
  Σ-syntax (Srf.Usage (NamedCtx.size (ctxWithImportsAndPolys ctx polys)))
    (λ Ψ → MonoWit (just ty) (ctxWithImportsAndPolys ctx polys) expr ty Ψ)
compileFun-sound doOpt ctx polys impsOf name ty expr eq =
  compileFun-aux-sound doOpt ctx polys impsOf name ty expr (name == "main") eq

-- R8: a definition without a signature — its body's synthesis derivation.
compileFunBodyI-at-success : ∀ {nctx : NamedCtx 0} {body : RawExpr} {T : Type} {Ψ : Srf.Usage (NamedCtx.size nctx)} {eE : Srf.Expr (NamedCtx.debruijn nctx) Ψ T}
  (doOpt : Bool) (ctx : TopCtx) (polys : Classify.PolyCtx) (impsOf : String.String → TopCtx)
  (name : String) (ty : Type) (δ : Srf.⟦ NamedCtx.debruijn nctx ⟧ᶜ ≡ Unit)
  (w : DI nctx body T Ψ eE) {dd ff : ℕ} → TE.inferElabV nctx body ≡ (TE.success T Ψ eE dd ff , w) → (d : Dec (T ≡ ty)) {ir : IR ⌊ Unit {0} ⌋ ⌊ ty ⌋} →
  C.compileFunBodyI-at IR.Heap doOpt ctx polys impsOf name ty δ w d ≡ inj₂ ir → MonoWit nothing nctx body ty Ψ
compileFunBodyI-at-success doOpt ctx polys impsOf name ty δ w ei (yes refl) _ = _ , _ , _ , w , ei
compileFunBodyI-at-success doOpt ctx polys impsOf name ty δ w ei (no _) ()

compileFunBodyI-aux-success : ∀ {nctx : NamedCtx 0} {body : RawExpr}
  (doOpt : Bool) (ctx : TopCtx) (polys : Classify.PolyCtx) (impsOf : String.String → TopCtx)
  (name : String) (ty : Type) (δ : Srf.⟦ NamedCtx.debruijn nctx ⟧ᶜ ≡ Unit)
  (cr : TE.VerifiedInferResult nctx body) → TE.inferElabV nctx body ≡ cr → {ir : IR ⌊ Unit {0} ⌋ ⌊ ty ⌋} →
  C.compileFunBodyI-aux IR.Heap doOpt ctx polys impsOf name ty δ cr ≡ inj₂ ir →
  Σ-syntax (Srf.Usage (NamedCtx.size nctx)) (λ Ψ → MonoWit nothing nctx body ty Ψ)
compileFunBodyI-aux-success doOpt ctx polys impsOf name ty δ (TE.failure err , _) _ ()
compileFunBodyI-aux-success doOpt ctx polys impsOf name ty δ (TE.success T Ψ se d f , w) ei eq =
  Ψ , compileFunBodyI-at-success doOpt ctx polys impsOf name ty δ w ei (T ≟T ty) eq

compileFunI-sound : ∀ (doOpt : Bool) (ctx : TopCtx) (polys : Classify.PolyCtx) (impsOf : String.String → TopCtx)
  (name : String) (ty : Type) (expr : RawExpr) {ir : IR ⌊ Unit {0} ⌋ ⌊ ty ⌋} →
  C.compileFunI IR.Heap doOpt ctx polys impsOf name ty expr ≡ inj₂ ir →
  Σ-syntax (Srf.Usage (NamedCtx.size (ctxWithImportsAndPolys ctx polys)))
    (λ Ψ → MonoWit nothing (ctxWithImportsAndPolys ctx polys) expr ty Ψ)
compileFunI-sound doOpt ctx polys impsOf name ty expr eq = aux (name == "main") eq
  where
    body : ∀ {ir} → C.compileFunBodyI IR.Heap doOpt ctx polys impsOf name ty expr ≡ inj₂ ir
         → Σ-syntax (Srf.Usage (NamedCtx.size (ctxWithImportsAndPolys ctx polys))) (λ Ψ → MonoWit nothing (ctxWithImportsAndPolys ctx polys) expr ty Ψ)
    body e = compileFunBodyI-aux-success doOpt ctx polys impsOf name ty refl (TE.inferElabV (ctxWithImportsAndPolys ctx polys) expr) refl e
    main : (vm : String ⊎ ⊤) → ∀ {ir} → C.compileFunI-main-aux IR.Heap doOpt ctx polys impsOf name ty expr vm ≡ inj₂ ir
         → Σ-syntax (Srf.Usage (NamedCtx.size (ctxWithImportsAndPolys ctx polys))) (λ Ψ → MonoWit nothing (ctxWithImportsAndPolys ctx polys) expr ty Ψ)
    main (inj₁ _) ()
    main (inj₂ _) e = body e
    aux : (b : Bool) → ∀ {ir} → C.compileFunI-aux IR.Heap doOpt ctx polys impsOf name ty expr b ≡ inj₂ ir
        → Σ-syntax (Srf.Usage (NamedCtx.size (ctxWithImportsAndPolys ctx polys))) (λ Ψ → MonoWit nothing (ctxWithImportsAndPolys ctx polys) expr ty Ψ)
    aux true  e = main (C.validateMain ty) e
    aux false e = body e

-- A definition, in its own mode.
compileFunM-sound : ∀ (ft : Maybe Type) (doOpt : Bool) (ctx : TopCtx) (polys : Classify.PolyCtx) (impsOf : String.String → TopCtx)
  (name : String) (ty : Type) (expr : RawExpr) {ir : IR ⌊ Unit {0} ⌋ ⌊ ty ⌋} →
  C.compileFunM ft IR.Heap doOpt ctx polys impsOf name ty expr ≡ inj₂ ir →
  Σ-syntax (Srf.Usage (NamedCtx.size (ctxWithImportsAndPolys ctx polys)))
    (λ Ψ → MonoWit ft (ctxWithImportsAndPolys ctx polys) expr ty Ψ)
compileFunM-sound (just _) = compileFun-sound
compileFunM-sound nothing  = compileFunI-sound

------------------------------------------------------------------------
-- Layer 2 — `compileAllFuns-go` accepts ⇒ `AllFunsTyped` (mutual).
------------------------------------------------------------------------

------------------------------------------------------------------------
-- D241 (plan 0.103 6c′): the compiler's telescope walk is SOUND for the
-- Spec's telescope — each accepted entry is typed in its scope.
------------------------------------------------------------------------

-- The Spec's scope is the compile scope with the declaration imports forgotten.
scopeOf : C.CScope → Scope
scopeOf sc = scope (C.CScope.csig sc) (C.CScope.cimps sc) (C.telePolys (C.CScope.ctele sc))

consCF-inj : ∀ {cf} (r : String ⊎ List C.CompiledFun) {cfs} → C.consCF cf r ≡ inj₂ cfs
  → Σ-syntax (List C.CompiledFun) (λ rest → r ≡ inj₂ rest)
consCF-inj (inj₁ _) ()
consCF-inj (inj₂ rest) _ = rest , refl

ce-sound      : ∀ (doOpt : Bool) (sc : C.CScope) (es : List Parser.Entry) {cfs}
              → C.compileEntries IR.Heap doOpt sc es ≡ inj₂ cfs → ModTele (scopeOf sc) es
ce-fun-sound  : ∀ (doOpt : Bool) (sc : C.CScope) (fi : Parser.FunInfo) (es : List Parser.Entry) (b : Bool)
              → Parser.FunInfo.funIsPrimitive fi ≡ b → ∀ {cfs}
              → C.ce-fun IR.Heap doOpt sc fi es b ≡ inj₂ cfs → ModTele (scopeOf sc) (Parser.e-fun fi ∷ es)
ce-prim-sound : ∀ (doOpt : Bool) (sc : C.CScope) (fi : Parser.FunInfo) (es : List Parser.Entry)
              → Parser.FunInfo.funIsPrimitive fi ≡ true
              → (mt : Maybe Type) → Parser.FunInfo.funType fi ≡ mt → ∀ {cfs}
              → C.ce-prim IR.Heap doOpt sc fi es mt ≡ inj₂ cfs → ModTele (scopeOf sc) (Parser.e-fun fi ∷ es)
ce-mono-sound : ∀ (doOpt : Bool) (sc : C.CScope) (fi : Parser.FunInfo) (es : List Parser.Entry)
              → Parser.FunInfo.funIsPrimitive fi ≡ false
              → (rt : String ⊎ Type)
              → C.resolveFunType (C.ctop sc) (C.cpolys sc) (Parser.FunInfo.funType fi) (Parser.FunInfo.funBody fi) ≡ rt
              → ∀ {cfs} → C.ce-mono IR.Heap doOpt sc fi es rt ≡ inj₂ cfs → ModTele (scopeOf sc) (Parser.e-fun fi ∷ es)
ce-poly-sound : ∀ (doOpt : Bool) (sc : C.CScope) (pfi : Parser.PolyFunInfo) (es : List Parser.Entry) {cfs}
              → C.compileEntries IR.Heap doOpt sc (Parser.e-poly pfi ∷ es) ≡ inj₂ cfs
              → ModTele (scopeOf sc) (Parser.e-poly pfi ∷ es)

ce-sound doOpt sc [] eq = []
ce-sound doOpt sc (Parser.e-fun fi ∷ es) eq =
  ce-fun-sound doOpt sc fi es (Parser.FunInfo.funIsPrimitive fi) refl eq
ce-sound doOpt sc (Parser.e-poly pfi ∷ es) eq = ce-poly-sound doOpt sc pfi es eq

ce-fun-sound doOpt sc fi es true  ep eq = ce-prim-sound doOpt sc fi es ep (Parser.FunInfo.funType fi) refl eq
ce-fun-sound doOpt sc fi es false ep eq =
  ce-mono-sound doOpt sc fi es ep _ refl eq

ce-prim-sound doOpt sc fi es ep nothing et ()
ce-prim-sound doOpt sc fi es ep (just ty) et eq =
  conc (isConcrete? ty) refl (honest? ty) refl eq
  where
    conc : (mc : Maybe (IsConcrete ty)) → isConcrete? ty ≡ mc
         → (mh : Maybe (HonestFFI ty)) → honest? ty ≡ mh → ∀ {cfs}
         → C.ce-prim-conc IR.Heap doOpt sc fi es ty mc mh ≡ inj₂ cfs → ModTele (scopeOf sc) (Parser.e-fun fi ∷ es)
    conc nothing _ _ _ ()
    conc (just _) _ nothing _ ()
    conc (just c) _ (just h) _ eq′ =
      ffi ep et c h (ce-sound doOpt (C.extendSig sc (Parser.FunInfo.funName fi) ty) es eq′)

ce-mono-sound doOpt sc fi es ep (inj₁ _) er ()
ce-mono-sound doOpt sc fi es ep (inj₂ ty) er eq = pstep _ refl eq
  where
    ctx = ctxWithImportsAndPolys (C.ctop sc) (C.cpolys sc)
    -- D314/D321: the body checks at no type strictly below its type.
    pstep : (mx : Maybe Type) → C.firstChecking ctx (Parser.FunInfo.funBody fi) (below ty) ≡ mx
          → ∀ {cfs} → C.ce-mono-p IR.Heap doOpt sc fi es ty mx ≡ inj₂ cfs
          → ModTele (scopeOf sc) (Parser.e-fun fi ∷ es)
    grd : C.firstChecking ctx (Parser.FunInfo.funBody fi) (below ty) ≡ nothing
        → ∀ {cfs} → C.ce-mono-p IR.Heap doOpt sc fi es ty nothing ≡ inj₂ cfs
        → ModTele (scopeOf sc) (Parser.e-fun fi ∷ es)
    pstep (just _) _ ()
    pstep nothing fc eqp = grd fc eqp
    grd fc eqg = step
      (C.compileFunM (Parser.FunInfo.funType fi) IR.Heap doOpt (C.ctop sc) (C.cpolys sc) (C.declImps (C.CScope.ctele sc))
         (Parser.FunInfo.funName fi) ty (Parser.FunInfo.funBody fi)) refl eqg
      where
        step : (ri : String ⊎ IR ⌊ Unit {0} ⌋ ⌊ ty ⌋)
             → C.compileFunM (Parser.FunInfo.funType fi) IR.Heap doOpt (C.ctop sc) (C.cpolys sc) (C.declImps (C.CScope.ctele sc))
                 (Parser.FunInfo.funName fi) ty (Parser.FunInfo.funBody fi) ≡ ri
             → ∀ {cfs} → C.ce-mono-ir IR.Heap doOpt sc fi es ty ri ≡ inj₂ cfs → ModTele (scopeOf sc) (Parser.e-fun fi ∷ es)
        step (inj₁ _) _ ()
        step (inj₂ ir) cf eq′ =
          let (Ψ , jud) = compileFunM-sound (Parser.FunInfo.funType fi) doOpt (C.ctop sc) (C.cpolys sc) (C.declImps (C.CScope.ctele sc))
                            (Parser.FunInfo.funName fi) ty (Parser.FunInfo.funBody fi) cf
          in mono ep er (firstChecking-sound ctx (Parser.FunInfo.funBody fi) (below ty) fc) (mder (Parser.FunInfo.funType fi) jud) jud
               (ce-sound doOpt (C.extendScope sc (Parser.FunInfo.funName fi) ty) es (proj₂ (consCF-inj _ eq′)))

ce-poly-sound doOpt sc pfi es eq = pstep _ refl eq
  where
    ctx = ctxAt (kindsOf (Parser.PolyFunInfo.pfunType pfi)) (C.ctop sc) (C.cpolys sc)
    low = below (rigidOf (Parser.PolyFunInfo.pfunType pfi))
    step : C.firstChecking ctx (Parser.PolyFunInfo.pfunBody pfi) low ≡ nothing
         → (r : TE.VerifiedCheckResult ctx (Parser.PolyFunInfo.pfunBody pfi) (rigidOf (Parser.PolyFunInfo.pfunType pfi)))
         → TE.checkElabV ctx (Parser.PolyFunInfo.pfunBody pfi) (rigidOf (Parser.PolyFunInfo.pfunType pfi)) ≡ r
         → ∀ {cfs} → C.ce-poly IR.Heap doOpt sc pfi es (C.checkOK r) ≡ inj₂ cfs
         → ModTele (scopeOf sc) (Parser.e-poly pfi ∷ es)
    step fc r@(TE.failure _ , _) _ ()
    step fc r@(TE.success Ψ se _ _ , w) _ eq′ =
      poly (firstChecking-sound ctx (Parser.PolyFunInfo.pfunBody pfi) low fc) (proj₁ w) (se , w) (ce-sound doOpt (C.addEntry sc pfi) es eq′)
    pstep : (mx : Maybe (Once.Spec.Type.Ty (arityOf (Parser.PolyFunInfo.pfunType pfi)))) → C.firstChecking ctx (Parser.PolyFunInfo.pfunBody pfi) low ≡ mx
          → ∀ {cfs} → C.ce-poly-p IR.Heap doOpt sc pfi es mx ≡ inj₂ cfs
          → ModTele (scopeOf sc) (Parser.e-poly pfi ∷ es)
    pstep (just _) _ ()
    pstep nothing fc eqp = step fc _ refl eqp

crm-aux-sound : ∀ (doOpt : Bool) (m : P.Module)
  (ef : String ⊎ List Parser.Entry) {compiled : List C.CompiledFun} →
  C.compileResolvedModule-aux IR.Heap doOpt m ef ≡ inj₂ compiled →
  ModuleTyped-ef m ef
crm-aux-sound doOpt m (inj₁ err) ()
crm-aux-sound doOpt m (inj₂ es) eq = ce-sound doOpt C.emptyCScope es eq

crm-sound : ∀ (doOpt : Bool) (m : P.Module) {compiled : List C.CompiledFun} →
  C.compileResolvedModule IR.Heap doOpt m ≡ inj₂ compiled →
  ModuleTyped m
crm-sound doOpt m eq =
  crm-aux-sound doOpt m (Parser.extractFunctions m) eq

moduleToIR-typed : ∀ (m : P.Module) {ir : IR ⌊ Unit {0} ⌋ ⌊ Unit {0} ⌋} →
  moduleToIR m ≡ just ir →
  ModuleTyped m
moduleToIR-typed m mi =
  crm-sound false m (proj₂ (moduleToIR-inj₂ m mi))
