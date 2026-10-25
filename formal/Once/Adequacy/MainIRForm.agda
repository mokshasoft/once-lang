-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.MainIRForm — compile-inversion helpers for the `main` entry.
--
-- The small set of compile-inversion lemmas consumed by
-- `ModuleComplete`/`FunBundle`/`TeleWalk`:
--   * `validateMain-EffUU`   — a compiled `main` has type `EffUU`.
--   * `compileFun-main-EffUU`— its impsOf `compileFun`-level corollary.
--   * `findMain-here-no` / `findMain-skip` — a non-`main` head is skipped.
--   * `bare-injective`       — `bare` is injective on names.
------------------------------------------------------------------------

module Once.Adequacy.MainIRForm where

open import Once.Internal.Typing.Scope using (PolyCtx)
open import Once.TypeCheck.Classify using (TopCtx)
import Once.Parser.Module as Module
import Once.Parser.Module.Core as Core
import Data.String as String
open import Data.Bool using (false)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Data.Maybe using (Maybe)
import Data.Maybe
open import Data.List using (List; _∷_)
open import Once.Spec.Name using (bare)
open import Once.CanonicalName using (_≟ᶜ_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Compile using (findMain; findMain-here)
open import Once.Spec.Sub using (_<:_)
open import Once.Type.Sub using (_<:?_)
import Once.IR as IR

open import Once.Spec.Grade using (mk-kind; Zero; One; Many; pure; eff)
open import Once.Spec.Type using (Type; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_)
open import Once.IR using (IR)
open import Once.IRTy using (⌊_⌋)
open import Once.Spec.Surface.Syntax using (Expr)
open import Once.TypeCheck.Elaborate using ()
import Once.Compile as C

EffUU : Type
EffUU = Unit ⇒[ mk-kind Many eff ] Unit

------------------------------------------------------------------------
-- (1) validateMain inversion: `validateMain ty ≡ inj₂ tt → ty <: EffUU` (D315:
-- `main` is usable as `Eff Unit Unit`).
------------------------------------------------------------------------

private
  validateMain-at-sub : ∀ (ty : Type) (d : Dec (ty <: EffUU)) → C.validateMain-at ty d ≡ inj₂ tt → ty <: EffUU
  validateMain-at-sub ty (yes p) _ = p
  validateMain-at-sub ty (no _) ()

validateMain-sub : ∀ (ty : Type) → C.validateMain ty ≡ inj₂ tt → ty <: EffUU
validateMain-sub ty eq = validateMain-at-sub ty (ty <:? EffUU) eq

------------------------------------------------------------------------
-- (2) A successfully-compiled "main" is usable as `Eff Unit Unit`.
------------------------------------------------------------------------

compileFun-main-sub : ∀ (ctx : TopCtx) (polys : PolyCtx) (impsOf : String.String → TopCtx)
  (ty : Type) (body : Expr) (irFun : IR ⌊ Unit {0} ⌋ ⌊ ty ⌋) →
  C.compileFun IR.Heap false ctx polys impsOf "main" ty body ≡ inj₂ irFun →
  ty <: EffUU
compileFun-main-sub ctx polys impsOf ty body irFun eq with C.validateMain ty in veq
... | inj₂ tt  = validateMain-sub ty veq
... | inj₁ err = case eq of λ ()

-- R8: `main` without a signature, compiled from its synthesis.
compileFunI-main-sub : ∀ (ctx : TopCtx) (polys : PolyCtx) (impsOf : String.String → TopCtx)
  (ty : Type) (body : Expr) (irFun : IR ⌊ Unit {0} ⌋ ⌊ ty ⌋) →
  C.compileFunI IR.Heap false ctx polys impsOf "main" ty body ≡ inj₂ irFun →
  ty <: EffUU
compileFunI-main-sub ctx polys impsOf ty body irFun eq = go (C.validateMain ty) refl eq
  where
    go : ∀ vm → C.validateMain ty ≡ vm → C.compileFunI-main-aux IR.Heap false ctx polys impsOf "main" ty body vm ≡ inj₂ irFun
       → ty <: EffUU
    go (inj₂ tt) veq _ = validateMain-sub ty veq
    go (inj₁ _)  _   ()

compileFunM-main-sub : ∀ (ft : Maybe Type) (ctx : TopCtx) (polys : PolyCtx) (impsOf : String.String → TopCtx)
  (ty : Type) (body : Expr) (irFun : IR ⌊ Unit {0} ⌋ ⌊ ty ⌋) →
  C.compileFunM ft IR.Heap false ctx polys impsOf "main" ty body ≡ inj₂ irFun →
  ty <: EffUU
compileFunM-main-sub (Data.Maybe.just _) = compileFun-main-sub
compileFunM-main-sub Data.Maybe.nothing  = compileFunI-main-sub

------------------------------------------------------------------------
-- (3) findMain dispatch helpers: a head whose name ≠ "main" is skipped.
------------------------------------------------------------------------

findMain-here-no : ∀ (cf : C.CompiledFun)
  (mu : Dec (C.CompiledFun.cfType cf <: EffUU)) (cont : Maybe (IR ⌊ Unit {0} ⌋ ⌊ Unit {0} ⌋))
  (¬p : ¬ (C.CompiledFun.cfName cf ≡ bare "main")) →
  findMain-here cf (no ¬p) mu cont ≡ cont
findMain-here-no cf mu cont ¬p = refl

open C.CompiledFun using (cfType; cfName)

-- `bare` is injective (single-component CanonicalName), so a String name ≠
-- "main" lifts to its CanonicalName ≠ `bare "main"`.
bare-injective : ∀ {s t} → bare s ≡ bare t → s ≡ t
bare-injective refl = refl

-- A head whose name ≠ "main" is skipped by findMain.
findMain-skip : ∀ (cf : C.CompiledFun) (rest : List C.CompiledFun) →
  ¬ (cfName cf ≡ bare "main") → findMain (cf ∷ rest) ≡ findMain rest
findMain-skip cf rest ¬p with cfName cf ≟ᶜ bare "main"
... | yes p  = ⊥-elim (¬p p)
... | no ¬q  = findMain-here-no cf (cfType cf <:? EffUU) (findMain rest) ¬q
