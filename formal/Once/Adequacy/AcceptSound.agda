-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.AcceptSound — front-end SOUNDNESS (Plan 0.48 Phase 1)
--
-- The compiler's front-end accepts ONLY genuinely well-typed programs:
-- if `compileResolvedModule` succeeds, every function has a DECLARATIVE
-- typing derivation `ctx ⊢ᶜ body ∶ ty ⨾ Ψ` (the judgment in
-- `Once.TypeCheck.Judgment`, INDEPENDENT of the elaborator function). This
-- is what makes `⟦_⟧⊥`'s domain genuine rather than true-by-construction:
-- the meaning is defined only for programs the independent judgment admits.
--
-- Built on `VerifiedTypeChecker.tcCheck-sound` (`checkElab ≡ success ⇒ ⊢ᶜ`),
-- lifted through the explicit-arg `…-aux` compile pipeline (no `with`-bite),
-- mirroring `Once.Adequacy.MainBuilds`.
------------------------------------------------------------------------

module Once.Adequacy.AcceptSound where

open import Data.Bool using (Bool; false; true)
open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; Σ-syntax; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just)
open import Data.String using (String; _==_)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (case_of_)

open import Once.IR using (IR)
open import Once.IRTy using (⌊_⌋)
open import Once.Type using (Unit; Type)
import Once.Compile as C
import Once.Surface.Syntax as Srf
open import Once.TypeCheck.Elaborate as TE using (CheckElabResult; checkElab; ctxWithImportsAndSelfAndPolys)
open import Once.TypeCheck.Classify using (NamedCtx; SigEffectCtx)
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.TypeCheck.Judgment using (_⊢ᶜ_∶_⨾_)
open import Once.Spec.Module
  using (AllFunsTyped; tnil; tcons; ModuleTyped-ef; ModuleTyped)
-- Import `check-sound` DIRECTLY from `Soundness` (not via `Verified`, which
-- transitively pulls in the still-rotted `ErrorProofs`; soundness needs only
-- this): `checkElab ctx e T ≡ success … ⇒ ctx ⊢ᶜ e ∶ T ⨾ Ψ`.
open import Once.TypeCheck.Soundness using (check-sound)
open import Once.Adequacy.SourceTrace using (moduleToIR)
open import Once.Adequacy.MainBuilds using (moduleToIR-inj₂)
import Once.Parser.Module.Core as P

------------------------------------------------------------------------
-- Leaf — a successful `compileFunBody` means `checkElab` succeeded, so its
-- body has a declarative check-mode derivation.
------------------------------------------------------------------------

compileFunBody-aux-success : ∀ {n} {Δ : Srf.Ctx n}
  (doOpt : Bool) (ctx : C.FunCtx) (polys : TE.PolyCtx)
  (name : String) (ty : Type) (δ : Srf.⟦ Δ ⟧ᶜ ≡ Unit)
  (cr : CheckElabResult Δ ty) {ir : IR ⌊ Unit ⌋ ⌊ ty ⌋} →
  C.compileFunBody-aux C.Heap doOpt ctx polys name ty δ cr ≡ inj₂ ir →
  Σ-syntax (Srf.Usage n) (λ Ψ → Σ-syntax (Srf.Expr Δ Ψ ty) (λ se →
    Σ-syntax ℕ (λ d → Σ-syntax ℕ (λ f → cr ≡ TE.success Ψ se d f))))
compileFunBody-aux-success doOpt ctx polys name ty δ (TE.failure err) ()
compileFunBody-aux-success doOpt ctx polys name ty δ (TE.success Ψ se d f) eq =
  Ψ , se , d , f , refl

compileFunBody-sound : ∀ (doOpt : Bool) (ctx : C.FunCtx) (polys : TE.PolyCtx)
  (sigEffs : SigEffectCtx) (name : String) (ty : Type) (expr : RawExpr) {ir : IR ⌊ Unit ⌋ ⌊ ty ⌋} →
  C.compileFunBody C.Heap doOpt ctx polys sigEffs name ty expr ≡ inj₂ ir →
  Σ-syntax (Srf.Usage (NamedCtx.size (ctxWithImportsAndSelfAndPolys ctx polys sigEffs name ty)))
    (λ Ψ → (ctxWithImportsAndSelfAndPolys ctx polys sigEffs name ty) ⊢ᶜ expr ∶ ty ⨾ Ψ)
compileFunBody-sound doOpt ctx polys sigEffs name ty expr eq =
  let ce-ctx = ctxWithImportsAndSelfAndPolys ctx polys sigEffs name ty
      (Ψ , se , d , f , ce) = compileFunBody-aux-success doOpt ctx polys name ty refl
                                (checkElab ce-ctx expr ty) eq
  in Ψ , check-sound ce-ctx expr ty ce

------------------------------------------------------------------------
-- The INDEPENDENT module-validity predicate: every function (threading the
-- accumulated `FunCtx`) resolves a type and has a DECLARATIVE check-mode
-- derivation. Mirrors `compileAllFuns-go`'s context threading, but speaks
-- ONLY the judgment `_⊢ᶜ_∶_⨾_` — no elaborator function appears.
------------------------------------------------------------------------

-- The relation is in `Once.Spec.Module` (plan 0.84).

------------------------------------------------------------------------
-- Layer 1 — `compileFun` accepts ⇒ its body has a derivation.
------------------------------------------------------------------------

compileFun-main-aux-sound : ∀ (doOpt : Bool) (ctx : C.FunCtx) (polys : TE.PolyCtx)
  (sigEffs : SigEffectCtx) (name : String) (ty : Type) (expr : RawExpr) (vm : String ⊎ ⊤) {ir : IR ⌊ Unit ⌋ ⌊ ty ⌋} →
  C.compileFun-main-aux C.Heap doOpt ctx polys sigEffs name ty expr vm ≡ inj₂ ir →
  Σ-syntax (Srf.Usage (NamedCtx.size (ctxWithImportsAndSelfAndPolys ctx polys sigEffs name ty)))
    (λ Ψ → (ctxWithImportsAndSelfAndPolys ctx polys sigEffs name ty) ⊢ᶜ expr ∶ ty ⨾ Ψ)
compileFun-main-aux-sound doOpt ctx polys sigEffs name ty expr (inj₁ err) ()
compileFun-main-aux-sound doOpt ctx polys sigEffs name ty expr (inj₂ _) eq =
  compileFunBody-sound doOpt ctx polys sigEffs name ty expr eq

compileFun-aux-sound : ∀ (doOpt : Bool) (ctx : C.FunCtx) (polys : TE.PolyCtx)
  (sigEffs : SigEffectCtx) (name : String) (ty : Type) (expr : RawExpr) (b : Bool) {ir : IR ⌊ Unit ⌋ ⌊ ty ⌋} →
  C.compileFun-aux C.Heap doOpt ctx polys sigEffs name ty expr b ≡ inj₂ ir →
  Σ-syntax (Srf.Usage (NamedCtx.size (ctxWithImportsAndSelfAndPolys ctx polys sigEffs name ty)))
    (λ Ψ → (ctxWithImportsAndSelfAndPolys ctx polys sigEffs name ty) ⊢ᶜ expr ∶ ty ⨾ Ψ)
compileFun-aux-sound doOpt ctx polys sigEffs name ty expr true eq =
  compileFun-main-aux-sound doOpt ctx polys sigEffs name ty expr (C.validateMain ty) eq
compileFun-aux-sound doOpt ctx polys sigEffs name ty expr false eq =
  compileFunBody-sound doOpt ctx polys sigEffs name ty expr eq

compileFun-sound : ∀ (doOpt : Bool) (ctx : C.FunCtx) (polys : TE.PolyCtx)
  (sigEffs : SigEffectCtx) (name : String) (ty : Type) (expr : RawExpr) {ir : IR ⌊ Unit ⌋ ⌊ ty ⌋} →
  C.compileFun C.Heap doOpt ctx polys sigEffs name ty expr ≡ inj₂ ir →
  Σ-syntax (Srf.Usage (NamedCtx.size (ctxWithImportsAndSelfAndPolys ctx polys sigEffs name ty)))
    (λ Ψ → (ctxWithImportsAndSelfAndPolys ctx polys sigEffs name ty) ⊢ᶜ expr ∶ ty ⨾ Ψ)
compileFun-sound doOpt ctx polys sigEffs name ty expr eq =
  compileFun-aux-sound doOpt ctx polys sigEffs name ty expr (name == "main") eq

------------------------------------------------------------------------
-- Layer 2 — `compileAllFuns-go` accepts ⇒ `AllFunsTyped` (mutual).
------------------------------------------------------------------------

caf-go-sound : ∀ (doOpt : Bool) (polys : TE.PolyCtx) (sigEffs : SigEffectCtx)
  (funs : List C.FunInfo) (ctx : C.FunCtx) {compiled : List C.CompiledFun} →
  C.compileAllFuns-go C.Heap doOpt polys sigEffs funs ctx ≡ inj₂ compiled →
  AllFunsTyped polys sigEffs funs ctx
caf-go-cf-sound : ∀ (doOpt : Bool) (polys : TE.PolyCtx) (sigEffs : SigEffectCtx)
  (fi : C.FunInfo) (rest : List C.FunInfo) (ctx : C.FunCtx) (ty : Type) {compiled : List C.CompiledFun} →
  C.resolveFunType ctx polys (C.FunInfo.funType fi) (C.FunInfo.funBody fi) ≡ inj₂ ty →
  C.caf-go-cf-aux C.Heap doOpt polys sigEffs fi rest ctx ty (C.compileFun C.Heap doOpt ctx polys sigEffs (C.FunInfo.funName fi) ty (C.FunInfo.funBody fi)) ≡ inj₂ compiled →
  AllFunsTyped polys sigEffs (fi ∷ rest) ctx
caf-go-rf-sound : ∀ (doOpt : Bool) (polys : TE.PolyCtx) (sigEffs : SigEffectCtx)
  (fi : C.FunInfo) (rest : List C.FunInfo) (ctx : C.FunCtx) (rf : String ⊎ Type) {compiled : List C.CompiledFun} →
  C.resolveFunType ctx polys (C.FunInfo.funType fi) (C.FunInfo.funBody fi) ≡ rf →
  C.caf-go-rf-aux C.Heap doOpt polys sigEffs fi rest ctx rf ≡ inj₂ compiled →
  AllFunsTyped polys sigEffs (fi ∷ rest) ctx

caf-go-sound doOpt polys sigEffs [] ctx eq = tnil
caf-go-sound doOpt polys sigEffs (fi ∷ rest) ctx eq =
  caf-go-rf-sound doOpt polys sigEffs fi rest ctx
    (C.resolveFunType ctx polys (C.FunInfo.funType fi) (C.FunInfo.funBody fi)) refl eq

caf-go-rf-sound doOpt polys sigEffs fi rest ctx (inj₁ err) rf-conn ()
caf-go-rf-sound doOpt polys sigEffs fi rest ctx (inj₂ ty) rf-conn eq =
  caf-go-cf-sound doOpt polys sigEffs fi rest ctx ty rf-conn eq

caf-go-cf-sound doOpt polys sigEffs fi rest ctx ty rf-eq eq
  with C.compileFun C.Heap doOpt ctx polys sigEffs (C.FunInfo.funName fi) ty (C.FunInfo.funBody fi) in cf-eq
... | inj₁ err = case eq of λ ()
... | inj₂ ir
      with C.compileAllFuns-go C.Heap doOpt polys sigEffs rest (C.extendFunCtx ctx (C.FunInfo.funName fi) ty) in rec-eq
...   | inj₁ err = case eq of λ ()
...   | inj₂ compiled-rest =
        let (Ψ , jud)  = compileFun-sound doOpt ctx polys sigEffs (C.FunInfo.funName fi) ty (C.FunInfo.funBody fi) cf-eq
            rest-typed = caf-go-sound doOpt polys sigEffs rest (C.extendFunCtx ctx (C.FunInfo.funName fi) ty) rec-eq
        in tcons rf-eq jud rest-typed

caf-sound : ∀ (doOpt : Bool) (funs : List C.FunInfo) (polys : TE.PolyCtx) (sigEffs : SigEffectCtx)
  {compiled : List C.CompiledFun} →
  C.compileAllFuns C.Heap doOpt funs polys sigEffs ≡ inj₂ compiled →
  AllFunsTyped polys sigEffs funs C.emptyFunCtx
caf-sound doOpt funs polys sigEffs eq =
  caf-go-sound doOpt polys sigEffs funs C.emptyFunCtx eq

------------------------------------------------------------------------
-- Layer 3 — module level. `ModuleTyped m` = the independent fact that
-- `m`'s functions are all declaratively well-typed.
------------------------------------------------------------------------

-- `ModuleTyped-ef`/`ModuleTyped` are in `Once.Spec.Module` (plan 0.84).

crm-aux-sound : ∀ (doOpt : Bool) (m : P.Module)
  (ef : String ⊎ (List C.FunInfo × List C.PolyFunInfo)) {compiled : List C.CompiledFun} →
  C.compileResolvedModule-aux C.Heap doOpt m ef ≡ inj₂ compiled →
  ModuleTyped-ef m ef
crm-aux-sound doOpt m (inj₁ err) ()
crm-aux-sound doOpt m (inj₂ (funs , polys)) eq =
  caf-sound doOpt funs (C.buildPolyCtx polys) (C.collectSigEffects (C.Module.decls m)) eq

crm-sound : ∀ (doOpt : Bool) (m : P.Module) {compiled : List C.CompiledFun} →
  C.compileResolvedModule C.Heap doOpt m ≡ inj₂ compiled →
  ModuleTyped m
crm-sound doOpt m eq =
  crm-aux-sound doOpt m (C.extractFunctions (C.extractAliases m) m) eq

------------------------------------------------------------------------
-- THE front-end soundness: a module with a compilable `main` is
-- declaratively well-typed. Hence `⟦_⟧⊥`'s `just` domain admits only
-- genuinely well-typed programs (no longer true-by-construction).
------------------------------------------------------------------------

moduleToIR-typed : ∀ (m : P.Module) {ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋} →
  moduleToIR m ≡ just ir →
  ModuleTyped m
moduleToIR-typed m mi =
  crm-sound false m (proj₂ (moduleToIR-inj₂ m mi))
