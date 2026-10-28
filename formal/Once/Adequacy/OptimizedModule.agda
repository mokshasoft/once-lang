-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.OptimizedModule — THE OPTIMIZED MODULE IS THE MODULE WITH
-- EACH FUNCTION OPTIMIZED (plan 0.39 B).
--
-- `doOpt` does one thing in the compiler: `if doOpt then optimize ir else ir`
-- on each function's elaborated IR. Every decision of the walk
-- (`compileEntries` and its helpers) reads the scope, the types and the
-- check results, never a compiled IR. So the walk at `true` is the walk at
-- `false` with `optimize` on each compiled function (`crm-opt`), the program's
-- `main` is the same (it calls `main` by name, `mainEntry`), and the table is
-- the table of the optimized functions.
--
-- The layers follow `Adequacy.MainBuilds`, which shows the weaker fact that
-- success does not depend on `doOpt`.
------------------------------------------------------------------------

module Once.Adequacy.OptimizedModule where

open import Data.Bool using (Bool; false; true)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String; _==_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; subst)
open import Relation.Nullary using (Dec; yes; no)

open import Once.IR using (IR; AllocMode)
import Once.IR as IR
open import Once.IRTy using (⌊_⌋)
open import Once.Spec.Type using (Unit)
import Once.Spec.Type as Type
open import Once.Optimize using (optimize)
import Once.Compile as C
open C using (CompiledFun; mkCompiledFun; consCF)
open C.CompiledFun using (cfName; cfType; cfIR)
import Once.Parser as Parser
import Once.Spec.Name
import Once.Parser.Module.Core as P
import Once.TypeCheck.Elaborate as TE
import Once.Context as Srf
import Once.Surface.Syntax as Srf
import Once.Spec.Context as Srf
import Once.TypeCheck.Classify as Classify
import Once.TypeCheck.Scope as Classify
open import Once.TypeCheck.Classify using (TopCtx)
open import Once.Spec.Surface.Syntax using (Expr)
open import Once.Functor.Decide using (isConcrete?)
open import Once.Type.Honest using (honest?)
open import Once.Type.Instance using (rigidOf; kindsOf)
open import Once.Principal using (below)
open import Once.Type.DecEq using (_≟T_)

------------------------------------------------------------------------
-- What `doOpt` changes
------------------------------------------------------------------------

optCF : CompiledFun → CompiledFun
optCF cf = mkCompiledFun (cfName cf) (cfType cf) (optimize (cfIR cf))

optCFs : List CompiledFun → List CompiledFun
optCFs []         = []
optCFs (cf ∷ cfs) = optCF cf ∷ optCFs cfs

optRes : String ⊎ List CompiledFun → String ⊎ List CompiledFun
optRes (inj₁ e)   = inj₁ e
optRes (inj₂ cfs) = inj₂ (optCFs cfs)

optIR : ∀ {A B} → String ⊎ IR A B → String ⊎ IR A B
optIR (inj₁ e)  = inj₁ e
optIR (inj₂ ir) = inj₂ (optimize ir)

private
  subst-opt : ∀ {X Y B} (e : X ≡ Y) (x : IR X B)
            → subst (λ Z → IR Z B) e (optimize x) ≡ optimize (subst (λ Z → IR Z B) e x)
  subst-opt refl x = refl

------------------------------------------------------------------------
-- Layer 0–1: one function
------------------------------------------------------------------------

module _ (m : AllocMode) (ctx : TopCtx) (polys : Classify.PolyCtx) (impsOf : String → TopCtx) (name : String) (ty : Type.Type) where

  cfb-aux-opt : ∀ {n} {Γ : Srf.Ctx 0 n} (δ : Srf.⟦ Γ ⟧ᶜ ≡ Unit) (r : TE.CheckElabResult Γ ty)
              → C.compileFunBody-aux m true ctx polys impsOf name ty δ r ≡ optIR (C.compileFunBody-aux m false ctx polys impsOf name ty δ r)
  cfb-aux-opt δ (TE.failure _)         = refl
  cfb-aux-opt δ (TE.success _ eE _ _) = cong inj₂ (subst-opt _ _)

  cfb-opt : ∀ expr → C.compileFunBody m true ctx polys impsOf name ty expr ≡ optIR (C.compileFunBody m false ctx polys impsOf name ty expr)
  cfb-opt expr = cfb-aux-opt refl (TE.checkElab (Classify.ctxWithImportsAndPolys ctx polys) expr ty)

  cfbI-at-opt : ∀ {n} {Γ : Srf.Ctx 0 n} {T : Type.Type} {Ψ : Srf.Usage n} (eE : Srf.Expr Γ Ψ T) (δ : Srf.⟦ Γ ⟧ᶜ ≡ Unit) (d : Dec (T ≡ ty))
              → C.compileFunBodyI-at eE m true ctx polys impsOf name ty δ d
                ≡ optIR (C.compileFunBodyI-at eE m false ctx polys impsOf name ty δ d)
  cfbI-at-opt eE δ (no _)     = refl
  cfbI-at-opt eE δ (yes refl) = cong inj₂ (subst-opt _ _)

  cfbI-aux-opt : ∀ {n} {Γ : Srf.Ctx 0 n} (δ : Srf.⟦ Γ ⟧ᶜ ≡ Unit) (r : TE.InferElabResult Γ)
               → C.compileFunBodyI-aux m true ctx polys impsOf name ty δ r ≡ optIR (C.compileFunBodyI-aux m false ctx polys impsOf name ty δ r)
  cfbI-aux-opt δ (TE.failure _)           = refl
  cfbI-aux-opt δ (TE.success T _ eE _ _) = cfbI-at-opt eE δ (T ≟T ty)

  cfbI-opt : ∀ expr → C.compileFunBodyI m true ctx polys impsOf name ty expr ≡ optIR (C.compileFunBodyI m false ctx polys impsOf name ty expr)
  cfbI-opt expr = cfbI-aux-opt refl (TE.inferElab (Classify.ctxWithImportsAndPolys ctx polys) expr)

  private
    main-opt : ∀ expr (v : String ⊎ _)
             → C.compileFun-main-aux m true ctx polys impsOf name ty expr v ≡ optIR (C.compileFun-main-aux m false ctx polys impsOf name ty expr v)
    main-opt expr (inj₁ _) = refl
    main-opt expr (inj₂ _) = cfb-opt expr

    mainI-opt : ∀ expr (v : String ⊎ _)
              → C.compileFunI-main-aux m true ctx polys impsOf name ty expr v ≡ optIR (C.compileFunI-main-aux m false ctx polys impsOf name ty expr v)
    mainI-opt expr (inj₁ _) = refl
    mainI-opt expr (inj₂ _) = cfbI-opt expr

    fun-aux-opt : ∀ expr b → C.compileFun-aux m true ctx polys impsOf name ty expr b ≡ optIR (C.compileFun-aux m false ctx polys impsOf name ty expr b)
    fun-aux-opt expr true  = main-opt expr (C.validateMain ty)
    fun-aux-opt expr false = cfb-opt expr

    funI-aux-opt : ∀ expr b → C.compileFunI-aux m true ctx polys impsOf name ty expr b ≡ optIR (C.compileFunI-aux m false ctx polys impsOf name ty expr b)
    funI-aux-opt expr true  = mainI-opt expr (C.validateMain ty)
    funI-aux-opt expr false = cfbI-opt expr

  cfunM-opt : ∀ ft expr → C.compileFunM ft m true ctx polys impsOf name ty expr ≡ optIR (C.compileFunM ft m false ctx polys impsOf name ty expr)
  cfunM-opt (just _) expr = fun-aux-opt expr (name == "main")
  cfunM-opt nothing  expr = funI-aux-opt expr (name == "main")

------------------------------------------------------------------------
-- Layer 2: the walk
------------------------------------------------------------------------

private
  consCF-opt : ∀ cf r → consCF (optCF cf) (optRes r) ≡ optRes (consCF cf r)
  consCF-opt cf (inj₁ _) = refl
  consCF-opt cf (inj₂ _) = refl

module _ (m : AllocMode) where

  ce-opt : ∀ sc es → C.compileEntries m true sc es ≡ optRes (C.compileEntries m false sc es)
  ce-fun-opt : ∀ sc fi es b → C.ce-fun m true sc fi es b ≡ optRes (C.ce-fun m false sc fi es b)
  ce-prim-opt : ∀ sc fi es mt → C.ce-prim m true sc fi es mt ≡ optRes (C.ce-prim m false sc fi es mt)
  ce-prim-conc-opt : ∀ sc fi es ty c h → C.ce-prim-conc m true sc fi es ty c h ≡ optRes (C.ce-prim-conc m false sc fi es ty c h)
  ce-mono-opt : ∀ sc fi es rt → C.ce-mono m true sc fi es rt ≡ optRes (C.ce-mono m false sc fi es rt)
  ce-mono-p-opt : ∀ sc fi es ty mx → C.ce-mono-p m true sc fi es ty mx ≡ optRes (C.ce-mono-p m false sc fi es ty mx)
  ce-mono-ir-opt : ∀ sc fi es ty r → C.ce-mono-ir m true sc fi es ty (optIR r) ≡ optRes (C.ce-mono-ir m false sc fi es ty r)
  ce-poly-p-opt : ∀ sc pfi es mx → C.ce-poly-p m true sc pfi es mx ≡ optRes (C.ce-poly-p m false sc pfi es mx)
  ce-poly-opt : ∀ sc pfi es ok → C.ce-poly m true sc pfi es ok ≡ optRes (C.ce-poly m false sc pfi es ok)

  ce-opt sc []                     = refl
  ce-opt sc (Parser.e-fun fi ∷ es)   = ce-fun-opt sc fi es (Parser.FunInfo.funIsPrimitive fi)
  ce-opt sc (Parser.e-poly pfi ∷ es) = ce-poly-p-opt sc pfi es
    (C.firstChecking (Classify.ctxAt (kindsOf (Parser.PolyFunInfo.pfunType pfi)) (C.ctop sc) (C.cpolys sc)) (Parser.PolyFunInfo.pfunBody pfi) (below (rigidOf (Parser.PolyFunInfo.pfunType pfi))))

  ce-fun-opt sc fi es true  = ce-prim-opt sc fi es (Parser.FunInfo.funType fi)
  ce-fun-opt sc fi es false = ce-mono-opt sc fi es (C.resolveFunType (C.ctop sc) (C.cpolys sc) (Parser.FunInfo.funType fi) (Parser.FunInfo.funBody fi))

  ce-prim-opt sc fi es nothing   = refl
  ce-prim-opt sc fi es (just ty) = ce-prim-conc-opt sc fi es ty (isConcrete? ty) (honest? ty)

  ce-prim-conc-opt sc fi es ty nothing  _        = refl
  ce-prim-conc-opt sc fi es ty (just _) nothing  = refl
  ce-prim-conc-opt sc fi es ty (just _) (just _) = ce-opt _ es

  ce-mono-opt sc fi es (inj₁ _)  = refl
  ce-mono-opt sc fi es (inj₂ ty) = ce-mono-p-opt sc fi es ty
    (C.firstChecking (Classify.ctxWithImportsAndPolys (C.ctop sc) (C.cpolys sc)) (Parser.FunInfo.funBody fi) (below ty))

  ce-mono-p-opt sc fi es ty (just _) = refl
  ce-mono-p-opt sc fi es ty nothing  =
    trans (cong (C.ce-mono-ir m true sc fi es ty)
                (cfunM-opt m (C.ctop sc) (C.cpolys sc) (C.declImps (C.CScope.ctele sc)) (Parser.FunInfo.funName fi) ty
                           (Parser.FunInfo.funType fi) (Parser.FunInfo.funBody fi)))
          (ce-mono-ir-opt sc fi es ty
            (C.compileFunM (Parser.FunInfo.funType fi) m false (C.ctop sc) (C.cpolys sc) (C.declImps (C.CScope.ctele sc)) (Parser.FunInfo.funName fi) ty (Parser.FunInfo.funBody fi)))

  ce-mono-ir-opt sc fi es ty (inj₁ _)  = refl
  ce-mono-ir-opt sc fi es ty (inj₂ ir) =
    trans (cong (consCF (mkCompiledFun (Once.Spec.Name.bare (Parser.FunInfo.funName fi)) ty (optimize ir)))
                (ce-opt (C.extendScope sc (Parser.FunInfo.funName fi) ty) es))
          (consCF-opt (mkCompiledFun (Once.Spec.Name.bare (Parser.FunInfo.funName fi)) ty ir)
            (C.compileEntries m false (C.extendScope sc (Parser.FunInfo.funName fi) ty) es))

  ce-poly-p-opt sc pfi es (just _) = refl
  ce-poly-p-opt sc pfi es nothing  = ce-poly-opt sc pfi es
    (C.checkOK (TE.checkElab (Classify.ctxAt (kindsOf (Parser.PolyFunInfo.pfunType pfi)) (C.ctop sc) (C.cpolys sc)) (Parser.PolyFunInfo.pfunBody pfi) (rigidOf (Parser.PolyFunInfo.pfunType pfi))))

  ce-poly-opt sc pfi es (inj₁ _) = refl
  ce-poly-opt sc pfi es (inj₂ _) = ce-opt (C.addEntry sc pfi) es

------------------------------------------------------------------------
-- Layer 3: the module
------------------------------------------------------------------------

crm-opt : ∀ (m : AllocMode) (mod : P.Resolved) → C.compileResolvedModule m true mod ≡ optRes (C.compileResolvedModule m false mod)
crm-opt m mod = go (Parser.extractFunctions mod)
  where
    go : ∀ ef → C.compileResolvedModule-aux m true mod ef ≡ optRes (C.compileResolvedModule-aux m false mod ef)
    go (inj₁ _)  = refl
    go (inj₂ es) = ce-opt m C.emptyCScope es

------------------------------------------------------------------------
-- The program's entry is the same: `findMain` reads names and types only.
------------------------------------------------------------------------

private
  here-opt : ∀ cf d₁ d₂ {x y} → x ≡ y → C.findMain-here (optCF cf) d₁ d₂ x ≡ C.findMain-here cf d₁ d₂ y
  here-opt cf (yes _) (yes _) _ = refl
  here-opt cf (yes _) (no _)  e = e
  here-opt cf (no _)  _       e = e

findMain-opt : ∀ cfs → C.findMain (optCFs cfs) ≡ C.findMain cfs
findMain-opt []         = refl
findMain-opt (cf ∷ cfs) = here-opt cf _ _ (findMain-opt cfs)

moduleToIR-opt : ∀ (mod : P.Resolved) → C.moduleToIR-aux (C.compileResolvedModule IR.Heap true mod) ≡ C.moduleToIR mod
moduleToIR-opt mod = trans (cong C.moduleToIR-aux (crm-opt IR.Heap mod)) (go (C.compileResolvedModule IR.Heap false mod))
  where
    go : ∀ r → C.moduleToIR-aux (optRes r) ≡ C.moduleToIR-aux r
    go (inj₁ _)   = refl
    go (inj₂ cfs) = findMain-opt cfs
