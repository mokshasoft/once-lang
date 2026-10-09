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

open import Once.TypeCheck.Classify using (TopCtx)
open import Data.Bool using (Bool; false; true)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Once.Denotation.Admissible using (AdmissibleM; admissibleM?)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ-syntax; _,_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Once.Functor.Decide using (isConcrete?)
open import Once.Type.Honest using (honest?)
open import Once.Type.Rigid using (rigidOf; rigidFree?)
open import Data.String using (String; _==_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import Function using (case_of_)

open import Once.IR using (IR)
open import Once.IRTy using (⌊_⌋)
open import Once.Type using (Unit)
import Once.Compile as C
import Once.IR as IR
import Once.Parser as Parser
import Once.Type as Type
import Once.CanonicalName
open import Once.Compile using (moduleToIR; moduleToIR-aux)
import Once.Surface.Syntax as Srf
open import Once.TypeCheck.Elaborate as TE using ()
import Once.TypeCheck.Classify as Classify
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.Target.Arch using (Arch)
import Once.Parser.Module.Core as P
import Once.Parser.Module as Module

------------------------------------------------------------------------
-- Layer 0 — `compileFunBody-aux` success is `doOpt`-independent.
------------------------------------------------------------------------

cfb-aux-doOpt : ∀ {nctx : Classify.NamedCtx} {body : RawExpr}
  (doOpt : Bool) (ctx : TopCtx) (polys : Classify.PolyCtx) (impsOf : P.String → TopCtx)
  (name : String) (ty : Type.Type) (δ : Srf.⟦ Classify.NamedCtx.debruijn nctx ⟧ᶜ ≡ Unit)
  (cr : TE.VerifiedCheckResult nctx body ty) {ir : IR ⌊ Unit ⌋ ⌊ ty ⌋} →
  C.compileFunBody-aux IR.Heap false ctx polys impsOf name ty δ cr ≡ inj₂ ir →
  Σ-syntax (IR ⌊ Unit ⌋ ⌊ ty ⌋) (λ ir' → C.compileFunBody-aux IR.Heap doOpt ctx polys impsOf name ty δ cr ≡ inj₂ ir')
cfb-aux-doOpt doOpt ctx polys impsOf name ty δ (TE.failure err , _) ()
cfb-aux-doOpt doOpt ctx polys impsOf name ty δ (TE.success _ se _ _ , _) eq = _ , refl

cfb-doOpt : ∀ (doOpt : Bool) (ctx : TopCtx) (polys : Classify.PolyCtx) (impsOf : P.String → TopCtx)
  (name : String) (ty : Type.Type) (expr : RawExpr) {ir : IR ⌊ Unit ⌋ ⌊ ty ⌋} →
  C.compileFunBody IR.Heap false ctx polys impsOf name ty expr ≡ inj₂ ir →
  Σ-syntax (IR ⌊ Unit ⌋ ⌊ ty ⌋) (λ ir' → C.compileFunBody IR.Heap doOpt ctx polys impsOf name ty expr ≡ inj₂ ir')
cfb-doOpt doOpt ctx polys impsOf name ty expr eq =
  cfb-aux-doOpt doOpt ctx polys impsOf name ty refl
    (TE.checkElabV (Classify.ctxWithImportsAndPolys ctx polys) expr ty) eq

------------------------------------------------------------------------
-- Layer 1 — `compileFun` success is `doOpt`-independent.
------------------------------------------------------------------------

cfun-main-aux-doOpt : ∀ (doOpt : Bool) (ctx : TopCtx) (polys : Classify.PolyCtx) (impsOf : P.String → TopCtx)
  (name : String) (ty : Type.Type) (expr : RawExpr) (vm : String ⊎ ⊤) {ir : IR ⌊ Unit ⌋ ⌊ ty ⌋} →
  C.compileFun-main-aux IR.Heap false ctx polys impsOf name ty expr vm ≡ inj₂ ir →
  Σ-syntax (IR ⌊ Unit ⌋ ⌊ ty ⌋) (λ ir' → C.compileFun-main-aux IR.Heap doOpt ctx polys impsOf name ty expr vm ≡ inj₂ ir')
cfun-main-aux-doOpt doOpt ctx polys impsOf name ty expr (inj₁ err) ()
cfun-main-aux-doOpt doOpt ctx polys impsOf name ty expr (inj₂ _) eq =
  cfb-doOpt doOpt ctx polys impsOf name ty expr eq

cfun-aux-doOpt : ∀ (doOpt : Bool) (ctx : TopCtx) (polys : Classify.PolyCtx) (impsOf : P.String → TopCtx)
  (name : String) (ty : Type.Type) (expr : RawExpr) (b : Bool) {ir : IR ⌊ Unit ⌋ ⌊ ty ⌋} →
  C.compileFun-aux IR.Heap false ctx polys impsOf name ty expr b ≡ inj₂ ir →
  Σ-syntax (IR ⌊ Unit ⌋ ⌊ ty ⌋) (λ ir' → C.compileFun-aux IR.Heap doOpt ctx polys impsOf name ty expr b ≡ inj₂ ir')
cfun-aux-doOpt doOpt ctx polys impsOf name ty expr true eq =
  cfun-main-aux-doOpt doOpt ctx polys impsOf name ty expr (C.validateMain ty) eq
cfun-aux-doOpt doOpt ctx polys impsOf name ty expr false eq =
  cfb-doOpt doOpt ctx polys impsOf name ty expr eq

cfun-doOpt : ∀ (doOpt : Bool) (ctx : TopCtx) (polys : Classify.PolyCtx) (impsOf : P.String → TopCtx)
  (name : String) (ty : Type.Type) (expr : RawExpr) {ir : IR ⌊ Unit ⌋ ⌊ ty ⌋} →
  C.compileFun IR.Heap false ctx polys impsOf name ty expr ≡ inj₂ ir →
  Σ-syntax (IR ⌊ Unit ⌋ ⌊ ty ⌋) (λ ir' → C.compileFun IR.Heap doOpt ctx polys impsOf name ty expr ≡ inj₂ ir')
cfun-doOpt doOpt ctx polys impsOf name ty expr eq =
  cfun-aux-doOpt doOpt ctx polys impsOf name ty expr (name == "main") eq

------------------------------------------------------------------------
-- Layer 2 — `compileAllFuns-go` success is `doOpt`-independent (mutual).
------------------------------------------------------------------------

-- D241 (plan 0.103 6c′): acceptance of the telescope walk does not depend on
-- `doOpt` — only a monomorphic entry's IR does.
ce-doOpt      : ∀ (doOpt : Bool) (sc : C.CScope) (es : List Parser.Entry) {c : List C.CompiledFun}
              → C.compileEntries IR.Heap false sc es ≡ inj₂ c
              → Σ-syntax (List C.CompiledFun) (λ c' → C.compileEntries IR.Heap doOpt sc es ≡ inj₂ c')
ce-fun-doOpt  : ∀ (doOpt : Bool) (sc : C.CScope) (fi : Parser.FunInfo) (es : List Parser.Entry) (b : Bool) {c}
              → C.ce-fun IR.Heap false sc fi es b ≡ inj₂ c
              → Σ-syntax (List C.CompiledFun) (λ c' → C.ce-fun IR.Heap doOpt sc fi es b ≡ inj₂ c')
ce-prim-doOpt : ∀ (doOpt : Bool) (sc : C.CScope) (fi : Parser.FunInfo) (es : List Parser.Entry) (mt : Maybe Type.Type) {c}
              → C.ce-prim IR.Heap false sc fi es mt ≡ inj₂ c
              → Σ-syntax (List C.CompiledFun) (λ c' → C.ce-prim IR.Heap doOpt sc fi es mt ≡ inj₂ c')
ce-mono-doOpt : ∀ (doOpt : Bool) (sc : C.CScope) (fi : Parser.FunInfo) (es : List Parser.Entry) (rt : String ⊎ Type.Type) {c}
              → C.ce-mono IR.Heap false sc fi es rt ≡ inj₂ c
              → Σ-syntax (List C.CompiledFun) (λ c' → C.ce-mono IR.Heap doOpt sc fi es rt ≡ inj₂ c')
ce-poly-doOpt : ∀ (doOpt : Bool) (sc : C.CScope) (pfi : Parser.PolyFunInfo) (es : List Parser.Entry) (ok : String ⊎ ⊤) {c}
              → C.ce-poly IR.Heap false sc pfi es ok ≡ inj₂ c
              → Σ-syntax (List C.CompiledFun) (λ c' → C.ce-poly IR.Heap doOpt sc pfi es ok ≡ inj₂ c')

ce-doOpt doOpt sc [] eq = _ , refl
ce-doOpt doOpt sc (Parser.e-fun fi ∷ es) eq = ce-fun-doOpt doOpt sc fi es (Parser.FunInfo.funIsPrimitive fi) eq
ce-doOpt doOpt sc (Parser.e-poly pfi ∷ es) eq =
  ce-poly-doOpt doOpt sc pfi es
    (C.checkOK (TE.checkElabV (Classify.ctxWithImportsAndPolys (C.ctop sc) (C.cpolys sc)) (Parser.PolyFunInfo.pfunBody pfi) (rigidOf (Parser.PolyFunInfo.pfunType pfi)))) eq

ce-fun-doOpt doOpt sc fi es true  eq = ce-prim-doOpt doOpt sc fi es (Parser.FunInfo.funType fi) eq
ce-fun-doOpt doOpt sc fi es false eq =
  ce-mono-doOpt doOpt sc fi es (C.resolveFunType (C.ctop sc) (C.cpolys sc) (Parser.FunInfo.funType fi) (Parser.FunInfo.funBody fi)) eq

ce-prim-doOpt doOpt sc fi es nothing ()
ce-prim-doOpt doOpt sc fi es (just ty) eq = conc (isConcrete? ty) (honest? ty) (rigidFree? ty) eq
  where
    conc : ∀ mc mh mg {c} → C.ce-prim-conc IR.Heap false sc fi es ty mc mh mg ≡ inj₂ c
         → Σ-syntax (List C.CompiledFun) (λ c' → C.ce-prim-conc IR.Heap doOpt sc fi es ty mc mh mg ≡ inj₂ c')
    conc nothing _ _ ()
    conc (just _) nothing _ ()
    conc (just _) (just _) nothing ()
    -- D274: an FFI declaration extends Σ only.
    conc (just cc) (just _) (just _) eq′ = ce-doOpt doOpt (C.extendSig sc (Parser.FunInfo.funName fi) ty) es eq′

ce-mono-doOpt doOpt sc fi es (inj₁ _) ()
ce-mono-doOpt doOpt sc fi es (inj₂ ty) eq = grd (rigidFree? ty) eq
  where
    grd : ∀ mg {c} → C.ce-mono-g IR.Heap false sc fi es ty mg ≡ inj₂ c
        → Σ-syntax (List C.CompiledFun) (λ c' → C.ce-mono-g IR.Heap doOpt sc fi es ty mg ≡ inj₂ c')
    grd nothing ()
    grd (just _) eqg
      with C.compileFun IR.Heap false (C.ctop sc) (C.cpolys sc) (C.declImps (C.CScope.ctele sc))
             (Parser.FunInfo.funName fi) ty (Parser.FunInfo.funBody fi) in cf-eq
    ... | inj₁ _ = case eqg of λ ()
    ... | inj₂ _
          with C.compileEntries IR.Heap false (C.extendScope sc (Parser.FunInfo.funName fi) ty) es in rec
    ...   | inj₁ _ = case eqg of λ ()
    ...   | inj₂ _ =
            let (ir-d , cfd) = cfun-doOpt doOpt (C.ctop sc) (C.cpolys sc) (C.declImps (C.CScope.ctele sc))
                                 (Parser.FunInfo.funName fi) ty (Parser.FunInfo.funBody fi) cf-eq
                (_ , recd)   = ce-doOpt doOpt (C.extendScope sc (Parser.FunInfo.funName fi) ty) es rec
            in _ , trans (cong (C.ce-mono-ir IR.Heap doOpt sc fi es ty) cfd) (cong (C.consCF (C.mkCompiledFun (Once.CanonicalName.bare (Parser.FunInfo.funName fi)) ty ir-d)) recd)

ce-poly-doOpt doOpt sc pfi es (inj₁ _) ()
ce-poly-doOpt doOpt sc pfi es (inj₂ _) eq = ce-doOpt doOpt (C.addEntry sc pfi) es eq

crm-aux-doOpt : ∀ (doOpt : Bool) (m : P.Module)
  (ef : String ⊎ List Parser.Entry) {c : List C.CompiledFun} →
  C.compileResolvedModule-aux IR.Heap false m ef ≡ inj₂ c →
  Σ-syntax (List C.CompiledFun) (λ c' → C.compileResolvedModule-aux IR.Heap doOpt m ef ≡ inj₂ c')
crm-aux-doOpt doOpt m (inj₁ err) ()
crm-aux-doOpt doOpt m (inj₂ es) eq = ce-doOpt doOpt C.emptyCScope es eq

crm-doOpt : ∀ (doOpt : Bool) (m : P.Module) {c : List C.CompiledFun} →
  C.compileResolvedModule IR.Heap false m ≡ inj₂ c →
  Σ-syntax (List C.CompiledFun) (λ c' → C.compileResolvedModule IR.Heap doOpt m ≡ inj₂ c')
crm-doOpt doOpt m eq =
  crm-aux-doOpt doOpt m (Parser.extractFunctions (Parser.extractAliases m) m) eq

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
cfm-built-gated : ∀ (doOpt : Bool) (arch : Arch) (m : P.Module) (es : List Parser.Entry)
  (d : Dec (AdmissibleM arch m)) → AdmissibleM arch m →
  {c : List C.CompiledFun} →
  C.compileEntries IR.Heap doOpt C.emptyCScope es ≡ inj₂ c →
  Σ-syntax String (λ asm → C.built-of arch (C.cfm-file-gated IR.Heap doOpt arch m es d) ≡ C.Built asm)
cfm-built-gated doOpt arch m es (yes _)  adm eq = _ , cong (λ r → C.built-of arch (C.emitFromCompiled arch r)) eq
cfm-built-gated doOpt arch m es (no ¬adm) adm eq = ⊥-elim (¬adm adm)

cfm-built-aux : ∀ (doOpt : Bool) (arch : Arch) (m : P.Module) → AdmissibleM arch m →
  (ef : String ⊎ List Parser.Entry) {c : List C.CompiledFun} →
  C.compileResolvedModule-aux IR.Heap doOpt m ef ≡ inj₂ c →
  Σ-syntax String (λ asm → C.cfm-ef-aux IR.Heap C.Build doOpt arch m ef ≡ C.Built asm)
cfm-built-aux doOpt arch m adm (inj₁ err) ()
cfm-built-aux doOpt arch m adm (inj₂ es) eq =
  cfm-built-gated doOpt arch m es (admissibleM? arch m) adm eq

cfm-built-from-crm : ∀ (doOpt : Bool) (arch : Arch) (m : P.Module) → AdmissibleM arch m →
  {c : List C.CompiledFun} →
  C.compileResolvedModule IR.Heap doOpt m ≡ inj₂ c →
  Σ-syntax String (λ asm → C.compileFromModule IR.Heap C.Build doOpt arch m ≡ C.Built asm)
cfm-built-from-crm doOpt arch m adm eq =
  cfm-built-aux doOpt arch m adm (Parser.extractFunctions (Parser.extractAliases m) m) eq

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
  Σ-syntax (List C.CompiledFun) (λ funs → C.compileResolvedModule IR.Heap false m ≡ inj₂ funs)
moduleToIR-inj₂ m eq = mtir-aux-inj₂ (C.compileResolvedModule IR.Heap false m) eq

------------------------------------------------------------------------
-- `main⇒built` — the obligation of `Once.Adequacy.Compile`.
------------------------------------------------------------------------

-- D115: a `main` is no longer enough — the target must also be able to
-- express the module's literals. That premise is not a weakening: it is the
-- statement becoming true, since without it the theorem now has a
-- counterexample (a module whose `main` compiles but whose literal is too wide
-- for this target).
-- D121: a second premise (`ElabPreservesLits`, over the COMPILED literals)
-- lived here while the IR gate did. Both are gone — the gate was a detector,
-- it detected, and the defect it found is fixed. The invariant it stood for is
-- recorded at the gate's old site in `Once.Compile`.
main⇒built : ∀ (arch : Arch) (doOpt : Bool) (m : P.Module) (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) →
  AdmissibleM arch m →
  moduleToIR m ≡ just ir →
  Σ-syntax String (λ asm → C.compileFromModule IR.Heap C.Build doOpt arch m ≡ C.Built asm)
main⇒built arch doOpt m ir adm mi =
  let (funs  , crm-false)  = moduleToIR-inj₂ m mi
      (funs' , crm-doOpt') = crm-doOpt doOpt m crm-false
  in cfm-built-from-crm doOpt arch m adm crm-doOpt'
