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
        ; compileFunM )

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
