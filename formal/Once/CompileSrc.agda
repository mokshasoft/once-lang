-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CompileSrc — plan 0.146 B1.7 (D455, D456): each compiled
-- definition's SOURCE, the elaborator's graded expression.
--
-- `Compile.compileFunM` keeps a definition's IR only; the linear core's bridge
-- (`LinCore.FromExpr`) compiles the resolved `Expr` the IR is elaborated
-- from. This module is that chain, clause for clause `Compile`'s, returning
-- the expression (`Src`), and the equation that `Compile`'s IR is its
-- `srcIR` (`compileFunM-src`). Transitional (plan 0.146 B1.7): when the old
-- lowering goes, `Compile`'s chain becomes `srcIR` of this one.
------------------------------------------------------------------------

module Once.CompileSrc where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.String using (String; _++_; _==_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Sum
open import Data.Unit using (⊤)
open import Data.Product using (_,_)
open import Data.List using (_∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong)
open import Relation.Nullary using (Dec; yes; no)

import Once.Context as Srf
import Once.Spec.Context as SC
open import Once.Spec.Type using (Type)
open import Once.Spec.Surface.Syntax using (Expr)
import Once.Surface.Syntax as SS
open import Once.IR using (IR; AllocMode)
open import Once.IRTy using (Unit; ⌊_⌋)
open import Once.Optimize using (optimize)
open import Once.Surface.Elaborate using (elaborateFull)
open import Once.TypeCheck.Scope using (PolyCtx)
open import Once.TypeCheck.Classify using (TopCtx; ctxWithImportsAndPolys)
open import Once.TypeCheck.Link using (resolveExpr)
open import Once.TypeCheck.Elaborate as TE using ()
import Once.TypeCheck.Error as Error
open import Once.Type.DecEq using (_≟T_)
open import Once.Spec.Name using (CanonicalName)
open import Once.Type using (showType)
open import Once.Compile
  using ( validateMain
        ; compileFunBody-aux; compileFunBody; compileFun-main-aux; compileFun-aux; compileFun
        ; compileFunBodyI-at; compileFunBodyI-aux; compileFunBodyI; compileFunI-main-aux; compileFunI-aux; compileFunI
        ; compileFunM
        ; CScope; ctop; cpolys; extendSig; extendScope; addEntry; declImps; firstChecking; resolveFunType; checkOK
        ; CompiledFun; mkCompiledFun; consCF; compileEntries; emptyCScope; compileResolvedModule-aux; compileResolvedModule
        ; ce-fun; ce-prim; ce-prim-conc; ce-mono; ce-mono-p; ce-mono-ir; ce-poly-p; ce-poly; ce-poly-main )
open import Once.Parser using (FunInfo; PolyFunInfo; Entry; e-fun; e-poly; module FunInfo; module PolyFunInfo; extractFunctions)
open import Once.Parser.Module.Core using (Resolved)
open import Once.TypeCheck.Classify using (ctxAt)
open import Once.Type.Instance using (rigidOf; kindsOf; arityOf)
open import Once.Principal using (below)
open import Once.Functor.Decide using (isConcrete?)
open import Once.Type.Honest using (HonestFFI; honest?)
open import Once.Type.Concrete using (IsConcrete)
open import Once.Spec.Type using (Ty)
open import Once.Spec.Name using (bare)
import Data.String.Properties as SProp
open import Data.List using (List; [])
import Data.List
open import Relation.Binary.PropositionalEquality using (trans)

------------------------------------------------------------------------
-- 1. A DEFINITION'S SOURCE, and its IR.
------------------------------------------------------------------------

-- the resolved expression a definition's IR is elaborated from
record Src (ty : Type) : Set where
  constructor src
  field
    {n}  : ℕ
    {Γ}  : SC.Ctx 0 n
    {Ψ}  : SC.Usage n
    δ    : Srf.⟦ Γ ⟧ᶜ ≡ Once.Spec.Type.Unit
    am   : AllocMode
    opt  : Bool
    expr : SS.Expr Γ Ψ ty
open Src public

-- its IR, as `compileFunBody` builds it
srcIR : ∀ {ty} → Src ty → IR ⌊ Once.Spec.Type.Unit {0} ⌋ ⌊ ty ⌋
srcIR {ty} (src δ m doOpt e) =
  subst (λ X → IR X ⌊ ty ⌋) (cong ⌊_⌋ δ) (if doOpt then optimize (elaborateFull m e) else elaborateFull m e)

mapSrc : ∀ {ty} → String ⊎ Src ty → String ⊎ IR ⌊ Once.Spec.Type.Unit {0} ⌋ ⌊ ty ⌋
mapSrc = Data.Sum.map₂ srcIR

------------------------------------------------------------------------
-- 2. THE CHAIN, clause for clause `Compile`'s.
------------------------------------------------------------------------

srcBody-aux : ∀ {n} {Γ : SC.Ctx 0 n}
  → AllocMode → Bool → TopCtx → PolyCtx → (String → TopCtx) → (name : String) (ty : Type)
  → Srf.⟦ Γ ⟧ᶜ ≡ Once.Spec.Type.Unit
  → TE.CheckElabResult Γ ty → String ⊎ Src ty
srcBody-aux m doOpt ctx polys impsOf name ty δ-unit (TE.failure err) =
  inj₁ ("Type error in " ++ name ++ ": " ++ Error.renderError err)
srcBody-aux m doOpt ctx polys impsOf name ty δ-unit (TE.success _ eE _ _) =
  inj₂ (src δ-unit m doOpt (resolveExpr polys impsOf ((name , ty) ∷ TopCtx.tdefs ctx) 0 eE))

srcBody : AllocMode → Bool → TopCtx → PolyCtx → (String → TopCtx) → (name : String) (ty : Type) → Expr → String ⊎ Src ty
srcBody m doOpt ctx polys impsOf name ty expr =
  srcBody-aux m doOpt ctx polys impsOf name ty refl (TE.checkElab (ctxWithImportsAndPolys ctx polys) expr ty)

src-main-aux : AllocMode → Bool → TopCtx → PolyCtx → (String → TopCtx) → (name : String) (ty : Type) → Expr → String ⊎ ⊤ → String ⊎ Src ty
src-main-aux m doOpt ctx polys impsOf name ty expr (inj₁ err) = inj₁ err
src-main-aux m doOpt ctx polys impsOf name ty expr (inj₂ _)   = srcBody m doOpt ctx polys impsOf name ty expr

src-aux : AllocMode → Bool → TopCtx → PolyCtx → (String → TopCtx) → (name : String) (ty : Type) → Expr → Bool → String ⊎ Src ty
src-aux m doOpt ctx polys impsOf name ty expr true  = src-main-aux m doOpt ctx polys impsOf name ty expr (validateMain ty)
src-aux m doOpt ctx polys impsOf name ty expr false = srcBody m doOpt ctx polys impsOf name ty expr

srcFun : AllocMode → Bool → TopCtx → PolyCtx → (String → TopCtx) → (name : String) (ty : Type) → Expr → String ⊎ Src ty
srcFun m doOpt ctx polys impsOf name ty expr = src-aux m doOpt ctx polys impsOf name ty expr (name == "main")

srcBodyI-at : ∀ {n} {Γ : SC.Ctx 0 n} {T : Type} {Ψ : SC.Usage n} (eE : SS.Expr Γ Ψ T)
  → AllocMode → Bool → TopCtx → PolyCtx → (String → TopCtx) → (name : String) (ty : Type)
  → Srf.⟦ Γ ⟧ᶜ ≡ Once.Spec.Type.Unit
  → Dec (T ≡ ty) → String ⊎ Src ty
srcBodyI-at eE m doOpt ctx polys impsOf name ty δ-unit (no _) =
  inj₁ ("Type error in " ++ name ++ ": its body synthesizes another type than " ++ showType ty)
srcBodyI-at eE m doOpt ctx polys impsOf name ty δ-unit (yes refl) =
  inj₂ (src δ-unit m doOpt (resolveExpr polys impsOf ((name , ty) ∷ TopCtx.tdefs ctx) 0 eE))

srcBodyI-aux : ∀ {n} {Γ : SC.Ctx 0 n}
  → AllocMode → Bool → TopCtx → PolyCtx → (String → TopCtx) → (name : String) (ty : Type)
  → Srf.⟦ Γ ⟧ᶜ ≡ Once.Spec.Type.Unit
  → TE.InferElabResult Γ → String ⊎ Src ty
srcBodyI-aux m doOpt ctx polys impsOf name ty δ-unit (TE.failure err) =
  inj₁ ("Type error in " ++ name ++ ": " ++ Error.renderError err)
srcBodyI-aux m doOpt ctx polys impsOf name ty δ-unit (TE.success T _ eE _ _) =
  srcBodyI-at eE m doOpt ctx polys impsOf name ty δ-unit (T ≟T ty)

srcBodyI : AllocMode → Bool → TopCtx → PolyCtx → (String → TopCtx) → (name : String) (ty : Type) → Expr → String ⊎ Src ty
srcBodyI m doOpt ctx polys impsOf name ty expr =
  srcBodyI-aux m doOpt ctx polys impsOf name ty refl (TE.inferElab (ctxWithImportsAndPolys ctx polys) expr)

srcI-main-aux : AllocMode → Bool → TopCtx → PolyCtx → (String → TopCtx) → (name : String) (ty : Type) → Expr → String ⊎ ⊤ → String ⊎ Src ty
srcI-main-aux m doOpt ctx polys impsOf name ty expr (inj₁ err) = inj₁ err
srcI-main-aux m doOpt ctx polys impsOf name ty expr (inj₂ _)   = srcBodyI m doOpt ctx polys impsOf name ty expr

srcI-aux : AllocMode → Bool → TopCtx → PolyCtx → (String → TopCtx) → (name : String) (ty : Type) → Expr → Bool → String ⊎ Src ty
srcI-aux m doOpt ctx polys impsOf name ty expr true  = srcI-main-aux m doOpt ctx polys impsOf name ty expr (validateMain ty)
srcI-aux m doOpt ctx polys impsOf name ty expr false = srcBodyI m doOpt ctx polys impsOf name ty expr

srcFunI : AllocMode → Bool → TopCtx → PolyCtx → (String → TopCtx) → (name : String) (ty : Type) → Expr → String ⊎ Src ty
srcFunI m doOpt ctx polys impsOf name ty expr = srcI-aux m doOpt ctx polys impsOf name ty expr (name == "main")

srcM : Maybe Type → AllocMode → Bool → TopCtx → PolyCtx → (String → TopCtx) → (name : String) (ty : Type) → Expr → String ⊎ Src ty
srcM (just _) = srcFun
srcM nothing  = srcFunI

------------------------------------------------------------------------
-- 3. ★ `Compile`'s IR is the source's (layer by layer, the same cases).
------------------------------------------------------------------------

body-aux-src : ∀ {n} {Γ : SC.Ctx 0 n} m doOpt ctx polys impsOf name ty (δ : Srf.⟦ Γ ⟧ᶜ ≡ Once.Spec.Type.Unit) r
             → compileFunBody-aux m doOpt ctx polys impsOf name ty δ r ≡ mapSrc (srcBody-aux m doOpt ctx polys impsOf name ty δ r)
body-aux-src m doOpt ctx polys impsOf name ty δ (TE.failure err)     = refl
body-aux-src m doOpt ctx polys impsOf name ty δ (TE.success _ eE _ _) = refl

body-src : ∀ m doOpt ctx polys impsOf name ty expr
         → compileFunBody m doOpt ctx polys impsOf name ty expr ≡ mapSrc (srcBody m doOpt ctx polys impsOf name ty expr)
body-src m doOpt ctx polys impsOf name ty expr =
  body-aux-src m doOpt ctx polys impsOf name ty refl (TE.checkElab (ctxWithImportsAndPolys ctx polys) expr ty)

main-aux-src : ∀ m doOpt ctx polys impsOf name ty expr v
             → compileFun-main-aux m doOpt ctx polys impsOf name ty expr v ≡ mapSrc (src-main-aux m doOpt ctx polys impsOf name ty expr v)
main-aux-src m doOpt ctx polys impsOf name ty expr (inj₁ err) = refl
main-aux-src m doOpt ctx polys impsOf name ty expr (inj₂ _)   = body-src m doOpt ctx polys impsOf name ty expr

fun-aux-src : ∀ m doOpt ctx polys impsOf name ty expr b
            → compileFun-aux m doOpt ctx polys impsOf name ty expr b ≡ mapSrc (src-aux m doOpt ctx polys impsOf name ty expr b)
fun-aux-src m doOpt ctx polys impsOf name ty expr true  = main-aux-src m doOpt ctx polys impsOf name ty expr (validateMain ty)
fun-aux-src m doOpt ctx polys impsOf name ty expr false = body-src m doOpt ctx polys impsOf name ty expr

fun-src : ∀ m doOpt ctx polys impsOf name ty expr
        → compileFun m doOpt ctx polys impsOf name ty expr ≡ mapSrc (srcFun m doOpt ctx polys impsOf name ty expr)
fun-src m doOpt ctx polys impsOf name ty expr = fun-aux-src m doOpt ctx polys impsOf name ty expr (name == "main")

bodyI-at-src : ∀ {n} {Γ : SC.Ctx 0 n} {T : Type} {Ψ : SC.Usage n} (eE : SS.Expr Γ Ψ T) m doOpt ctx polys impsOf name ty
                 (δ : Srf.⟦ Γ ⟧ᶜ ≡ Once.Spec.Type.Unit) (d : Dec (T ≡ ty))
             → compileFunBodyI-at eE m doOpt ctx polys impsOf name ty δ d ≡ mapSrc (srcBodyI-at eE m doOpt ctx polys impsOf name ty δ d)
bodyI-at-src eE m doOpt ctx polys impsOf name ty δ (no _)    = refl
bodyI-at-src eE m doOpt ctx polys impsOf name ty δ (yes refl) = refl

bodyI-aux-src : ∀ {n} {Γ : SC.Ctx 0 n} m doOpt ctx polys impsOf name ty (δ : Srf.⟦ Γ ⟧ᶜ ≡ Once.Spec.Type.Unit) r
              → compileFunBodyI-aux m doOpt ctx polys impsOf name ty δ r ≡ mapSrc (srcBodyI-aux m doOpt ctx polys impsOf name ty δ r)
bodyI-aux-src m doOpt ctx polys impsOf name ty δ (TE.failure err)       = refl
bodyI-aux-src m doOpt ctx polys impsOf name ty δ (TE.success T _ eE _ _) = bodyI-at-src eE m doOpt ctx polys impsOf name ty δ (T ≟T ty)

bodyI-src : ∀ m doOpt ctx polys impsOf name ty expr
          → compileFunBodyI m doOpt ctx polys impsOf name ty expr ≡ mapSrc (srcBodyI m doOpt ctx polys impsOf name ty expr)
bodyI-src m doOpt ctx polys impsOf name ty expr =
  bodyI-aux-src m doOpt ctx polys impsOf name ty refl (TE.inferElab (ctxWithImportsAndPolys ctx polys) expr)

mainI-aux-src : ∀ m doOpt ctx polys impsOf name ty expr v
              → compileFunI-main-aux m doOpt ctx polys impsOf name ty expr v ≡ mapSrc (srcI-main-aux m doOpt ctx polys impsOf name ty expr v)
mainI-aux-src m doOpt ctx polys impsOf name ty expr (inj₁ err) = refl
mainI-aux-src m doOpt ctx polys impsOf name ty expr (inj₂ _)   = bodyI-src m doOpt ctx polys impsOf name ty expr

funI-aux-src : ∀ m doOpt ctx polys impsOf name ty expr b
             → compileFunI-aux m doOpt ctx polys impsOf name ty expr b ≡ mapSrc (srcI-aux m doOpt ctx polys impsOf name ty expr b)
funI-aux-src m doOpt ctx polys impsOf name ty expr true  = mainI-aux-src m doOpt ctx polys impsOf name ty expr (validateMain ty)
funI-aux-src m doOpt ctx polys impsOf name ty expr false = bodyI-src m doOpt ctx polys impsOf name ty expr

funI-src : ∀ m doOpt ctx polys impsOf name ty expr
         → compileFunI m doOpt ctx polys impsOf name ty expr ≡ mapSrc (srcFunI m doOpt ctx polys impsOf name ty expr)
funI-src m doOpt ctx polys impsOf name ty expr = funI-aux-src m doOpt ctx polys impsOf name ty expr (name == "main")

-- ★ a definition's IR is its source's
compileFunM-src : ∀ mt m doOpt ctx polys impsOf name ty expr
                → compileFunM mt m doOpt ctx polys impsOf name ty expr ≡ mapSrc (srcM mt m doOpt ctx polys impsOf name ty expr)
compileFunM-src (just _) = fun-src
compileFunM-src nothing  = funI-src

------------------------------------------------------------------------
-- 4. A MODULE'S DEFINITIONS, with their sources (clause for clause
-- `compileEntries`), and `Compile`'s list their IR.
------------------------------------------------------------------------

record CompiledSrc : Set where
  constructor mkCompiledSrc
  field
    csName : CanonicalName
    csType : Type
    csSrc  : Src csType
open CompiledSrc public

toCF : CompiledSrc → CompiledFun
toCF c = mkCompiledFun (csName c) (csType c) (srcIR (csSrc c))

consCS : CompiledSrc → String ⊎ List CompiledSrc → String ⊎ List CompiledSrc
consCS c (inj₁ err) = inj₁ err
consCS c (inj₂ cs)  = inj₂ (c ∷ cs)

mapCF : String ⊎ List CompiledSrc → String ⊎ List CompiledFun
mapCF = Data.Sum.map₂ (Data.List.map toCF)

srcEntries   : AllocMode → Bool → CScope → List Entry → String ⊎ List CompiledSrc
se-fun       : AllocMode → Bool → CScope → (fi : FunInfo) → List Entry → Bool → String ⊎ List CompiledSrc
se-prim      : AllocMode → Bool → CScope → (fi : FunInfo) → List Entry → Maybe Type → String ⊎ List CompiledSrc
se-prim-conc : AllocMode → Bool → CScope → (fi : FunInfo) → List Entry → (ty : Type)
             → Maybe (IsConcrete ty) → Maybe (HonestFFI ty) → String ⊎ List CompiledSrc
se-mono      : AllocMode → Bool → CScope → (fi : FunInfo) → List Entry → String ⊎ Type → String ⊎ List CompiledSrc
se-mono-p    : AllocMode → Bool → CScope → (fi : FunInfo) → List Entry → (ty : Type) → Maybe Type → String ⊎ List CompiledSrc
se-mono-src  : AllocMode → Bool → CScope → (fi : FunInfo) → List Entry → (ty : Type) → String ⊎ Src ty → String ⊎ List CompiledSrc
se-poly-p    : AllocMode → Bool → CScope → (pfi : PolyFunInfo) → List Entry → Maybe (Ty (arityOf (PolyFunInfo.pfunType pfi))) → String ⊎ List CompiledSrc
se-poly      : AllocMode → Bool → CScope → (pfi : PolyFunInfo) → List Entry → String ⊎ ⊤ → String ⊎ List CompiledSrc
se-poly-main : AllocMode → Bool → CScope → (pfi : PolyFunInfo) → List Entry → Dec (PolyFunInfo.pfunName pfi ≡ "main") → String ⊎ List CompiledSrc

srcEntries m doOpt sc []                = inj₂ []
srcEntries m doOpt sc (e-fun fi ∷ es)   = se-fun m doOpt sc fi es (FunInfo.funIsPrimitive fi)
srcEntries m doOpt sc (e-poly pfi ∷ es) = se-poly-main m doOpt sc pfi es (PolyFunInfo.pfunName pfi SProp.≟ "main")

se-poly-main m doOpt sc pfi es (yes _) =
  inj₁ "main must be usable as Eff Unit Unit (its type below it), but its type is polymorphic or not concrete"
se-poly-main m doOpt sc pfi es (no _) =
  se-poly-p m doOpt sc pfi es
    (firstChecking (ctxAt (kindsOf (PolyFunInfo.pfunType pfi)) (ctop sc) (cpolys sc)) (PolyFunInfo.pfunBody pfi) (below (rigidOf (PolyFunInfo.pfunType pfi))))

se-fun m doOpt sc fi es true  = se-prim m doOpt sc fi es (FunInfo.funType fi)
se-fun m doOpt sc fi es false =
  se-mono m doOpt sc fi es (resolveFunType (ctop sc) (cpolys sc) (FunInfo.funType fi) (FunInfo.funBody fi))

se-prim m doOpt sc fi es nothing   = inj₁ ("FFI signature without a type: " ++ FunInfo.funName fi)
se-prim m doOpt sc fi es (just ty) = se-prim-conc m doOpt sc fi es ty (isConcrete? ty) (honest? ty)
se-prim-conc m doOpt sc fi es ty nothing _ =
  inj₁ ("FFI signature `" ++ FunInfo.funName fi ++ "` is not concrete: " ++ showType ty)
se-prim-conc m doOpt sc fi es ty (just _) nothing =
  inj₁ ("FFI signature `" ++ FunInfo.funName fi ++ "` hides an effect: " ++ showType ty)
se-prim-conc m doOpt sc fi es ty (just conc) (just _) =
  srcEntries m doOpt (extendSig sc (FunInfo.funName fi) ty) es

se-mono m doOpt sc fi es (inj₁ err) = inj₁ err
se-mono m doOpt sc fi es (inj₂ ty)  =
  se-mono-p m doOpt sc fi es ty (firstChecking (ctxWithImportsAndPolys (ctop sc) (cpolys sc)) (FunInfo.funBody fi) (below ty))
se-mono-p m doOpt sc fi es ty (just X) =
  inj₁ ("`" ++ FunInfo.funName fi ++ "` is more precise than its signature " ++ showType ty ++ ": the body also checks at "
        ++ showType X ++ ". A signature states the body's own type: write the more precise one, or give the body"
        ++ " the wider type with an annotation, " ++ FunInfo.funName fi ++ " = (... : " ++ showType ty ++ ")")
se-mono-p m doOpt sc fi es ty nothing =
  se-mono-src m doOpt sc fi es ty
    (srcM (FunInfo.funType fi) m doOpt (ctop sc) (cpolys sc) (declImps (CScope.ctele sc)) (FunInfo.funName fi) ty (FunInfo.funBody fi))
se-mono-src m doOpt sc fi es ty (inj₁ err) = inj₁ err
se-mono-src m doOpt sc fi es ty (inj₂ s)   =
  consCS (mkCompiledSrc (bare (FunInfo.funName fi)) ty s)
         (srcEntries m doOpt (extendScope sc (FunInfo.funName fi) ty) es)

se-poly-p m doOpt sc pfi es (just X) =
  inj₁ ("`" ++ PolyFunInfo.pfunName pfi ++ "` is more precise than its schema: the body also checks at " ++ showType X
        ++ ". A signature states the body's own type: write the more precise one")
se-poly-p m doOpt sc pfi es nothing =
  se-poly m doOpt sc pfi es
    (checkOK (TE.checkElab (ctxAt (kindsOf (PolyFunInfo.pfunType pfi)) (ctop sc) (cpolys sc)) (PolyFunInfo.pfunBody pfi) (rigidOf (PolyFunInfo.pfunType pfi))))
se-poly m doOpt sc pfi es (inj₁ err) = inj₁ ("Type error in " ++ PolyFunInfo.pfunName pfi ++ ": " ++ err)
se-poly m doOpt sc pfi es (inj₂ _)   = srcEntries m doOpt (addEntry sc pfi) es

-- ★ `Compile`'s definitions are the sources' IR, clause for clause
consCS-cf : ∀ c r → consCF (toCF c) (mapCF r) ≡ mapCF (consCS c r)
consCS-cf c (inj₁ err) = refl
consCS-cf c (inj₂ cs)  = refl

entries-src   : ∀ m doOpt sc es → compileEntries m doOpt sc es ≡ mapCF (srcEntries m doOpt sc es)
fun-e-src     : ∀ m doOpt sc fi es b → ce-fun m doOpt sc fi es b ≡ mapCF (se-fun m doOpt sc fi es b)
prim-e-src    : ∀ m doOpt sc fi es mt → ce-prim m doOpt sc fi es mt ≡ mapCF (se-prim m doOpt sc fi es mt)
conc-e-src    : ∀ m doOpt sc fi es ty c h → ce-prim-conc m doOpt sc fi es ty c h ≡ mapCF (se-prim-conc m doOpt sc fi es ty c h)
mono-e-src    : ∀ m doOpt sc fi es r → ce-mono m doOpt sc fi es r ≡ mapCF (se-mono m doOpt sc fi es r)
mono-p-e-src  : ∀ m doOpt sc fi es ty x → ce-mono-p m doOpt sc fi es ty x ≡ mapCF (se-mono-p m doOpt sc fi es ty x)
mono-ir-e-src : ∀ m doOpt sc fi es ty r → ce-mono-ir m doOpt sc fi es ty (mapSrc r) ≡ mapCF (se-mono-src m doOpt sc fi es ty r)
poly-p-e-src  : ∀ m doOpt sc pfi es x → ce-poly-p m doOpt sc pfi es x ≡ mapCF (se-poly-p m doOpt sc pfi es x)
poly-e-src    : ∀ m doOpt sc pfi es r → ce-poly m doOpt sc pfi es r ≡ mapCF (se-poly m doOpt sc pfi es r)
main-e-src    : ∀ m doOpt sc pfi es d → ce-poly-main m doOpt sc pfi es d ≡ mapCF (se-poly-main m doOpt sc pfi es d)

entries-src m doOpt sc []                = refl
entries-src m doOpt sc (e-fun fi ∷ es)   = fun-e-src m doOpt sc fi es (FunInfo.funIsPrimitive fi)
entries-src m doOpt sc (e-poly pfi ∷ es) = main-e-src m doOpt sc pfi es (PolyFunInfo.pfunName pfi SProp.≟ "main")

main-e-src m doOpt sc pfi es (yes _) = refl
main-e-src m doOpt sc pfi es (no _)  =
  poly-p-e-src m doOpt sc pfi es
    (firstChecking (ctxAt (kindsOf (PolyFunInfo.pfunType pfi)) (ctop sc) (cpolys sc)) (PolyFunInfo.pfunBody pfi) (below (rigidOf (PolyFunInfo.pfunType pfi))))

fun-e-src m doOpt sc fi es true  = prim-e-src m doOpt sc fi es (FunInfo.funType fi)
fun-e-src m doOpt sc fi es false =
  mono-e-src m doOpt sc fi es (resolveFunType (ctop sc) (cpolys sc) (FunInfo.funType fi) (FunInfo.funBody fi))

prim-e-src m doOpt sc fi es nothing   = refl
prim-e-src m doOpt sc fi es (just ty) = conc-e-src m doOpt sc fi es ty (isConcrete? ty) (honest? ty)
conc-e-src m doOpt sc fi es ty nothing _ = refl
conc-e-src m doOpt sc fi es ty (just _) nothing = refl
conc-e-src m doOpt sc fi es ty (just conc) (just _) = entries-src m doOpt (extendSig sc (FunInfo.funName fi) ty) es

mono-e-src m doOpt sc fi es (inj₁ err) = refl
mono-e-src m doOpt sc fi es (inj₂ ty)  =
  mono-p-e-src m doOpt sc fi es ty (firstChecking (ctxWithImportsAndPolys (ctop sc) (cpolys sc)) (FunInfo.funBody fi) (below ty))
mono-p-e-src m doOpt sc fi es ty (just X) = refl
mono-p-e-src m doOpt sc fi es ty nothing =
  trans (cong (ce-mono-ir m doOpt sc fi es ty)
              (compileFunM-src (FunInfo.funType fi) m doOpt (ctop sc) (cpolys sc) (declImps (CScope.ctele sc)) (FunInfo.funName fi) ty (FunInfo.funBody fi)))
        (mono-ir-e-src m doOpt sc fi es ty
              (srcM (FunInfo.funType fi) m doOpt (ctop sc) (cpolys sc) (declImps (CScope.ctele sc)) (FunInfo.funName fi) ty (FunInfo.funBody fi)))
mono-ir-e-src m doOpt sc fi es ty (inj₁ err) = refl
mono-ir-e-src m doOpt sc fi es ty (inj₂ s)   =
  trans (cong (consCF (mkCompiledFun (bare (FunInfo.funName fi)) ty (srcIR s)))
              (entries-src m doOpt (extendScope sc (FunInfo.funName fi) ty) es))
        (consCS-cf (mkCompiledSrc (bare (FunInfo.funName fi)) ty s) (srcEntries m doOpt (extendScope sc (FunInfo.funName fi) ty) es))

poly-p-e-src m doOpt sc pfi es (just X) = refl
poly-p-e-src m doOpt sc pfi es nothing =
  poly-e-src m doOpt sc pfi es
    (checkOK (TE.checkElab (ctxAt (kindsOf (PolyFunInfo.pfunType pfi)) (ctop sc) (cpolys sc)) (PolyFunInfo.pfunBody pfi) (rigidOf (PolyFunInfo.pfunType pfi))))
poly-e-src m doOpt sc pfi es (inj₁ err) = refl
poly-e-src m doOpt sc pfi es (inj₂ _)   = entries-src m doOpt (addEntry sc pfi) es

-- a module's definitions, with their sources (`compileResolvedModule`)
srcModule-aux : AllocMode → Bool → Resolved → String ⊎ List Entry → String ⊎ List CompiledSrc
srcModule-aux m doOpt mod (inj₁ err) = inj₁ err
srcModule-aux m doOpt mod (inj₂ es)  = srcEntries m doOpt emptyCScope es

srcModule : AllocMode → Bool → Resolved → String ⊎ List CompiledSrc
srcModule m doOpt mod = srcModule-aux m doOpt mod (extractFunctions mod)

module-aux-src : ∀ m doOpt mod r → compileResolvedModule-aux m doOpt mod r ≡ mapCF (srcModule-aux m doOpt mod r)
module-aux-src m doOpt mod (inj₁ err) = refl
module-aux-src m doOpt mod (inj₂ es)  = entries-src m doOpt emptyCScope es

-- ★ a module's compiled definitions are its sources' IR
module-src : ∀ m doOpt mod → compileResolvedModule m doOpt mod ≡ mapCF (srcModule m doOpt mod)
module-src m doOpt mod = module-aux-src m doOpt mod (extractFunctions mod)
