-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.MainBuilds — `main⇒built` (Plan 0.48)
--
-- Discharges the `main⇒built` obligation of `Once.Adequacy.Compile`:
-- a module with a compilable `main` (`moduleToIR m ≡ just ir`) Builds for
-- EVERY `doOpt`. Proved bottom-up through the compile pipeline. The crux is
-- that `doOpt` only chooses `optimize ir` vs `ir` inside `compileFunBody`
-- (the `inj₁`/`inj₂` SUCCESS decision is `doOpt`-free), so SUCCESS is
-- `doOpt`-independent. Each layer reasons over the explicit-argument `…-aux`
-- form introduced in `Once.Compile` (no `with`-bite).
------------------------------------------------------------------------

module Once.Adequacy.MainBuilds where

open import Data.Bool using (Bool; false; true)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Once.Denotation.Admissible using (AdmissibleM; admissibleM?)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; Σ-syntax; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just)
open import Data.String using (String; _==_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import Function using (case_of_)

open import Once.IR using (IR)
open import Once.IRTy using (⌊_⌋)
open import Once.Type using (Unit)
import Once.Compile as C
open import Once.Adequacy.SourceTrace using (moduleToIR; moduleToIR-aux)
import Once.Surface.Syntax as Srf
open import Once.TypeCheck.Elaborate as TE using (CheckElabResult)
open import Once.TypeCheck.Classify using (SigEffectCtx)
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.Adequacy.CPU.Interface using (Arch)
import Once.Parser.Module.Core as P

------------------------------------------------------------------------
-- Layer 0 — `compileFunBody-aux` success is `doOpt`-independent.
------------------------------------------------------------------------

cfb-aux-doOpt : ∀ {n} {Δ : Srf.Ctx n}
  (doOpt : Bool) (ctx : C.FunCtx) (polys : TE.PolyCtx)
  (name : String) (ty : C.Type) (δ : Srf.⟦ Δ ⟧ᶜ ≡ Unit)
  (cr : CheckElabResult Δ ty) {ir : IR ⌊ Unit ⌋ ⌊ ty ⌋} →
  C.compileFunBody-aux C.Heap false ctx polys name ty δ cr ≡ inj₂ ir →
  Σ-syntax (IR ⌊ Unit ⌋ ⌊ ty ⌋) (λ ir' → C.compileFunBody-aux C.Heap doOpt ctx polys name ty δ cr ≡ inj₂ ir')
cfb-aux-doOpt doOpt ctx polys name ty δ (TE.failure err) ()
cfb-aux-doOpt doOpt ctx polys name ty δ (TE.success _ se _ _) eq = _ , refl

cfb-doOpt : ∀ (doOpt : Bool) (ctx : C.FunCtx) (polys : TE.PolyCtx) (sigEffs : SigEffectCtx)
  (name : String) (ty : C.Type) (expr : RawExpr) {ir : IR ⌊ Unit ⌋ ⌊ ty ⌋} →
  C.compileFunBody C.Heap false ctx polys sigEffs name ty expr ≡ inj₂ ir →
  Σ-syntax (IR ⌊ Unit ⌋ ⌊ ty ⌋) (λ ir' → C.compileFunBody C.Heap doOpt ctx polys sigEffs name ty expr ≡ inj₂ ir')
cfb-doOpt doOpt ctx polys sigEffs name ty expr eq =
  cfb-aux-doOpt doOpt ctx polys name ty refl
    (TE.checkElab (TE.ctxWithImportsAndSelfAndPolys ctx polys sigEffs name ty) expr ty) eq

------------------------------------------------------------------------
-- Layer 1 — `compileFun` success is `doOpt`-independent.
------------------------------------------------------------------------

cfun-main-aux-doOpt : ∀ (doOpt : Bool) (ctx : C.FunCtx) (polys : TE.PolyCtx) (sigEffs : SigEffectCtx)
  (name : String) (ty : C.Type) (expr : RawExpr) (vm : String ⊎ ⊤) {ir : IR ⌊ Unit ⌋ ⌊ ty ⌋} →
  C.compileFun-main-aux C.Heap false ctx polys sigEffs name ty expr vm ≡ inj₂ ir →
  Σ-syntax (IR ⌊ Unit ⌋ ⌊ ty ⌋) (λ ir' → C.compileFun-main-aux C.Heap doOpt ctx polys sigEffs name ty expr vm ≡ inj₂ ir')
cfun-main-aux-doOpt doOpt ctx polys sigEffs name ty expr (inj₁ err) ()
cfun-main-aux-doOpt doOpt ctx polys sigEffs name ty expr (inj₂ _) eq =
  cfb-doOpt doOpt ctx polys sigEffs name ty expr eq

cfun-aux-doOpt : ∀ (doOpt : Bool) (ctx : C.FunCtx) (polys : TE.PolyCtx) (sigEffs : SigEffectCtx)
  (name : String) (ty : C.Type) (expr : RawExpr) (b : Bool) {ir : IR ⌊ Unit ⌋ ⌊ ty ⌋} →
  C.compileFun-aux C.Heap false ctx polys sigEffs name ty expr b ≡ inj₂ ir →
  Σ-syntax (IR ⌊ Unit ⌋ ⌊ ty ⌋) (λ ir' → C.compileFun-aux C.Heap doOpt ctx polys sigEffs name ty expr b ≡ inj₂ ir')
cfun-aux-doOpt doOpt ctx polys sigEffs name ty expr true eq =
  cfun-main-aux-doOpt doOpt ctx polys sigEffs name ty expr (C.validateMain ty) eq
cfun-aux-doOpt doOpt ctx polys sigEffs name ty expr false eq =
  cfb-doOpt doOpt ctx polys sigEffs name ty expr eq

cfun-doOpt : ∀ (doOpt : Bool) (ctx : C.FunCtx) (polys : TE.PolyCtx) (sigEffs : SigEffectCtx)
  (name : String) (ty : C.Type) (expr : RawExpr) {ir : IR ⌊ Unit ⌋ ⌊ ty ⌋} →
  C.compileFun C.Heap false ctx polys sigEffs name ty expr ≡ inj₂ ir →
  Σ-syntax (IR ⌊ Unit ⌋ ⌊ ty ⌋) (λ ir' → C.compileFun C.Heap doOpt ctx polys sigEffs name ty expr ≡ inj₂ ir')
cfun-doOpt doOpt ctx polys sigEffs name ty expr eq =
  cfun-aux-doOpt doOpt ctx polys sigEffs name ty expr (name == "main") eq

------------------------------------------------------------------------
-- Layer 2 — `compileAllFuns-go` success is `doOpt`-independent (mutual).
------------------------------------------------------------------------

caf-go-doOpt : ∀ (doOpt : Bool) (polys : TE.PolyCtx) (sigEffs : SigEffectCtx)
  (funs : List C.FunInfo) (ctx : C.FunCtx) {c : List C.CompiledFun} →
  C.compileAllFuns-go C.Heap false polys sigEffs funs ctx ≡ inj₂ c →
  Σ-syntax (List C.CompiledFun) (λ c' → C.compileAllFuns-go C.Heap doOpt polys sigEffs funs ctx ≡ inj₂ c')
caf-go-cf-doOpt : ∀ (doOpt : Bool) (polys : TE.PolyCtx) (sigEffs : SigEffectCtx)
  (fi : C.FunInfo) (rest : List C.FunInfo) (ctx : C.FunCtx) (ty : C.Type) {c : List C.CompiledFun} →
  C.caf-go-cf-aux C.Heap false polys sigEffs fi rest ctx ty (C.compileFun C.Heap false ctx polys sigEffs (C.FunInfo.funName fi) ty (C.FunInfo.funBody fi)) ≡ inj₂ c →
  Σ-syntax (List C.CompiledFun) (λ c' → C.caf-go-cf-aux C.Heap doOpt polys sigEffs fi rest ctx ty (C.compileFun C.Heap doOpt ctx polys sigEffs (C.FunInfo.funName fi) ty (C.FunInfo.funBody fi)) ≡ inj₂ c')
caf-go-rf-doOpt : ∀ (doOpt : Bool) (polys : TE.PolyCtx) (sigEffs : SigEffectCtx)
  (fi : C.FunInfo) (rest : List C.FunInfo) (ctx : C.FunCtx) (rf : String ⊎ C.Type) {c : List C.CompiledFun} →
  C.caf-go-rf-aux C.Heap false polys sigEffs fi rest ctx rf ≡ inj₂ c →
  Σ-syntax (List C.CompiledFun) (λ c' → C.caf-go-rf-aux C.Heap doOpt polys sigEffs fi rest ctx rf ≡ inj₂ c')

caf-go-doOpt doOpt polys sigEffs [] ctx eq = _ , refl
caf-go-doOpt doOpt polys sigEffs (fi ∷ rest) ctx eq =
  caf-go-rf-doOpt doOpt polys sigEffs fi rest ctx
    (C.resolveFunType ctx polys (C.FunInfo.funType fi) (C.FunInfo.funBody fi)) eq

caf-go-rf-doOpt doOpt polys sigEffs fi rest ctx (inj₁ err) ()
caf-go-rf-doOpt doOpt polys sigEffs fi rest ctx (inj₂ ty) eq =
  caf-go-cf-doOpt doOpt polys sigEffs fi rest ctx ty eq

caf-go-cf-doOpt doOpt polys sigEffs fi rest ctx ty eq
  with C.compileFun C.Heap false ctx polys sigEffs (C.FunInfo.funName fi) ty (C.FunInfo.funBody fi) in cf-eq
... | inj₁ err = case eq of λ ()
... | inj₂ ir-f
      with C.compileAllFuns-go C.Heap false polys sigEffs rest (C.extendFunCtx ctx (C.FunInfo.funName fi) ty) in rec-eq
...   | inj₁ err = case eq of λ ()
...   | inj₂ c-rec =
        let (ir-d , cfd)     = cfun-doOpt doOpt ctx polys sigEffs (C.FunInfo.funName fi) ty (C.FunInfo.funBody fi) cf-eq
            (c-rec-d , recd) = caf-go-doOpt doOpt polys sigEffs rest (C.extendFunCtx ctx (C.FunInfo.funName fi) ty) rec-eq
        in _ , trans (cong (C.caf-go-cf-aux C.Heap doOpt polys sigEffs fi rest ctx ty) cfd)
                     (cong (C.caf-go-wrap fi ty ir-d) recd)

caf-doOpt : ∀ (doOpt : Bool) (funs : List C.FunInfo) (polys : TE.PolyCtx) (sigEffs : SigEffectCtx)
  {c : List C.CompiledFun} →
  C.compileAllFuns C.Heap false funs polys sigEffs ≡ inj₂ c →
  Σ-syntax (List C.CompiledFun) (λ c' → C.compileAllFuns C.Heap doOpt funs polys sigEffs ≡ inj₂ c')
caf-doOpt doOpt funs polys sigEffs eq =
  caf-go-doOpt doOpt polys sigEffs funs C.emptyFunCtx eq

------------------------------------------------------------------------
-- Layer 3 — `compileResolvedModule` success is `doOpt`-independent.
------------------------------------------------------------------------

crm-aux-doOpt : ∀ (doOpt : Bool) (m : P.Module)
  (ef : String ⊎ (List C.FunInfo × List C.PolyFunInfo)) {c : List C.CompiledFun} →
  C.compileResolvedModule-aux C.Heap false m ef ≡ inj₂ c →
  Σ-syntax (List C.CompiledFun) (λ c' → C.compileResolvedModule-aux C.Heap doOpt m ef ≡ inj₂ c')
crm-aux-doOpt doOpt m (inj₁ err) ()
crm-aux-doOpt doOpt m (inj₂ (funs , polys)) eq =
  caf-doOpt doOpt funs (C.buildPolyCtx polys) (C.collectSigEffects (C.Module.decls m)) eq

crm-doOpt : ∀ (doOpt : Bool) (m : P.Module) {c : List C.CompiledFun} →
  C.compileResolvedModule C.Heap false m ≡ inj₂ c →
  Σ-syntax (List C.CompiledFun) (λ c' → C.compileResolvedModule C.Heap doOpt m ≡ inj₂ c')
crm-doOpt doOpt m eq =
  crm-aux-doOpt doOpt m (C.extractFunctions (C.extractAliases m) m) eq

------------------------------------------------------------------------
-- A compiled module Builds: `compileResolvedModule doOpt ≡ inj₂ _` ⇒
-- `compileFromModule Build doOpt ≡ Built _` (shared `compileAllFuns` call).
------------------------------------------------------------------------

-- D115: the BUILD stage is now gated on admissibility, so "a module with a
-- `main` builds" is only true when the target can express its literals. The
-- premise is where that shows, and the `no` branch is where it would fail —
-- which is exactly the point: an inadmissible module must NOT build.
--
-- Dispatching on the DECISION (explicit argument, no `with`) keeps the gate a
-- subterm, so this reduces for a caller who has already decided.
-- Plan 0.74 J6 step 2: there are now TWO gates, so there are two premises.
-- `AdmissibleM` is about the literals the SOURCE wrote; `AdmissibleIR` is
-- about the ones the compiled code will LOAD. The second is the one that
-- cannot currently be supplied — see `main⇒built` below.
built-lits : ∀ (arch : Arch) (c : List C.CompiledFun)
             (d : Dec (C.AdmissibleIR arch c)) → C.AdmissibleIR arch c
           → Σ-syntax String (λ asm → C.cfm-build-lits arch c d ≡ C.Built asm)
built-lits arch c (yes _)  admIR = _ , refl
built-lits arch c (no ¬p)  admIR = ⊥-elim (¬p admIR)

built-caf : ∀ (arch : Arch) {c : List C.CompiledFun} → C.AdmissibleIR arch c
          → (r : String ⊎ List C.CompiledFun) → r ≡ inj₂ c
          → Σ-syntax String (λ asm → C.cfm-build-caf arch r ≡ C.Built asm)
built-caf arch {c} admIR .(inj₂ c) refl =
  built-lits arch c (C.admissibleIR? arch c) admIR

cfm-built-gated : ∀ (doOpt : Bool) (arch : Arch) (m : P.Module)
  (funs : List C.FunInfo) (polys : List C.PolyFunInfo)
  (d : Dec (AdmissibleM arch m)) → AdmissibleM arch m →
  {c : List C.CompiledFun} → C.AdmissibleIR arch c →
  C.compileAllFuns C.Heap doOpt funs (C.buildPolyCtx polys) (C.collectSigEffects (P.Module.decls m)) ≡ inj₂ c →
  Σ-syntax String (λ asm → C.cfm-build-gated C.Heap doOpt arch m funs polys d ≡ C.Built asm)
cfm-built-gated doOpt arch m funs polys (yes _)  adm admIR eq = built-caf arch admIR _ eq
cfm-built-gated doOpt arch m funs polys (no ¬adm) adm admIR eq = ⊥-elim (¬adm adm)

cfm-built-aux : ∀ (doOpt : Bool) (arch : Arch) (m : P.Module) → AdmissibleM arch m →
  (ef : String ⊎ (List C.FunInfo × List C.PolyFunInfo)) {c : List C.CompiledFun} →
  C.AdmissibleIR arch c →
  C.compileResolvedModule-aux C.Heap doOpt m ef ≡ inj₂ c →
  Σ-syntax String (λ asm → C.cfm-ef-aux C.Heap C.Build doOpt arch m ef ≡ C.Built asm)
cfm-built-aux doOpt arch m adm (inj₁ err) admIR ()
cfm-built-aux doOpt arch m adm (inj₂ (funs , polys)) admIR eq =
  cfm-built-gated doOpt arch m funs polys (admissibleM? arch m) adm admIR eq

cfm-built-from-crm : ∀ (doOpt : Bool) (arch : Arch) (m : P.Module) → AdmissibleM arch m →
  {c : List C.CompiledFun} → C.AdmissibleIR arch c →
  C.compileResolvedModule C.Heap doOpt m ≡ inj₂ c →
  Σ-syntax String (λ asm → C.compileFromModule C.Heap C.Build doOpt arch m ≡ C.Built asm)
cfm-built-from-crm doOpt arch m adm admIR eq =
  cfm-built-aux doOpt arch m adm (C.extractFunctions (C.extractAliases m) m) admIR eq

------------------------------------------------------------------------
-- `moduleToIR m ≡ just ir` ⇒ `compileResolvedModule Heap false m ≡ inj₂ _`.
------------------------------------------------------------------------

mtir-aux-inj₂ : ∀ (r : String ⊎ List C.CompiledFun) {ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋} →
  moduleToIR-aux r ≡ just ir →
  Σ-syntax (List C.CompiledFun) (λ funs → r ≡ inj₂ funs)
mtir-aux-inj₂ (inj₁ _) ()
mtir-aux-inj₂ (inj₂ funs) eq = funs , refl

moduleToIR-inj₂ : ∀ (m : P.Module) {ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋} →
  moduleToIR m ≡ just ir →
  Σ-syntax (List C.CompiledFun) (λ funs → C.compileResolvedModule C.Heap false m ≡ inj₂ funs)
moduleToIR-inj₂ m eq = mtir-aux-inj₂ (C.compileResolvedModule C.Heap false m) eq

------------------------------------------------------------------------
-- `main⇒built` — the obligation of `Once.Adequacy.Compile`.
------------------------------------------------------------------------

-- D115: a `main` is no longer enough — the target must also be able to
-- express the module's literals. That premise is not a weakening: it is the
-- statement becoming true, since without it the theorem now has a
-- counterexample (a module whose `main` compiles but whose literal is too wide
-- for this target).
-- PLAN 0.74 J6 STEP 2 — THE SECOND PREMISE, and it is the interesting one.
--
-- `AdmissibleM arch m` says the target can express the literals the PROGRAMMER
-- WROTE. `ElabPreservesLits` says elaboration hands the machine those same
-- literals. Both are needed, and only the first used to be, because the build
-- gate read the source list twice instead of reading the IR once.
--
-- The second is currently FALSE, and that is the finding rather than a defect
-- in this lemma. `-2147483648` parses as `RUnaryOp OpNeg (RInt 2147483648)`,
-- nothing folds the sign, so the source list holds `-2147483648` (in range at
-- 32 bits) while the compiled code loads `2147483648` (out of range). The
-- premise is therefore UNDISCHARGEABLE for x86-32 until the elaborator folds a
-- minus on a numeral into the numeral, which is plan 0.74 J6 step 3.
--
-- It is stated as a PREMISE rather than postulated because postulating it
-- would be postulating a false proposition — the counterexample above is
-- explicit — and that makes the whole development inconsistent.
ElabPreservesLits : Arch → P.Module → Bool → Set
ElabPreservesLits arch m doOpt =
  ∀ {c : List C.CompiledFun}
  → C.compileResolvedModule C.Heap doOpt m ≡ inj₂ c
  → C.AdmissibleIR arch c

main⇒built : ∀ (arch : Arch) (doOpt : Bool) (m : P.Module) (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) →
  AdmissibleM arch m →
  ElabPreservesLits arch m doOpt →
  moduleToIR m ≡ just ir →
  Σ-syntax String (λ asm → C.compileFromModule C.Heap C.Build doOpt arch m ≡ C.Built asm)
main⇒built arch doOpt m ir adm epl mi =
  let (funs  , crm-false)  = moduleToIR-inj₂ m mi
      (funs' , crm-doOpt') = crm-doOpt doOpt m crm-false
  in cfm-built-from-crm doOpt arch m adm (epl crm-doOpt') crm-doOpt'
