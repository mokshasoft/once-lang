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

open import Once.TypeCheck.Classify using (TopCtx)
open import Data.Bool using (false)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Data.Maybe using (Maybe)
open import Data.List using (List; _∷_)
open import Once.CanonicalName using (bare) renaming (_≟ᶜ_ to _≟cn_)
open import Relation.Nullary using (yes; no; ¬_)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Compile using (findMain; findMain-here; isEffUU?)

open import Once.Type
  using (Type; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ-type; ν-type; mk-kind; Zero; One; Many; pure; eff)
open import Once.IR using (IR)
open import Once.IRTy using (⌊_⌋)
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.TypeCheck.Elaborate using (PolyCtx)
import Once.Compile as C

EffUU : Type
EffUU = Unit ⇒[ mk-kind Many eff ] Unit

------------------------------------------------------------------------
-- (1) validateMain inversion: `validateMain ty ≡ inj₂ tt → ty ≡ EffUU`.
-- Every non-EffUU `ty` has a concrete mismatching component, so
-- `validateMain ty` reduces to `inj₁ …` and the equation is absurd.
------------------------------------------------------------------------

validateMain-EffUU : ∀ (ty : Type) → C.validateMain ty ≡ inj₂ tt → ty ≡ EffUU
validateMain-EffUU (Unit ⇒[ mk-kind Many eff ] Unit) eq = refl
-- non-arrow heads
validateMain-EffUU Unit       ()
validateMain-EffUU Void       ()
validateMain-EffUU Int        ()
validateMain-EffUU Float      ()
validateMain-EffUU (_ * _)    ()
validateMain-EffUU (_ + _)    ()
validateMain-EffUU (μ-type _) ()
validateMain-EffUU (ν-type _ _) ()
-- arrow with domain Unit, kind (Many,eff), but codomain ≠ Unit
validateMain-EffUU (Unit ⇒[ mk-kind Many eff ] Void)         ()
validateMain-EffUU (Unit ⇒[ mk-kind Many eff ] Int)          ()
validateMain-EffUU (Unit ⇒[ mk-kind Many eff ] Float)        ()
validateMain-EffUU (Unit ⇒[ mk-kind Many eff ] (_ * _))      ()
validateMain-EffUU (Unit ⇒[ mk-kind Many eff ] (_ + _))      ()
validateMain-EffUU (Unit ⇒[ mk-kind Many eff ] (_ ⇒[ _ ] _)) ()
validateMain-EffUU (Unit ⇒[ mk-kind Many eff ] (μ-type _))   ()
validateMain-EffUU (Unit ⇒[ mk-kind Many eff ] (ν-type _ _))   ()
-- arrow with domain Unit but kind ≠ (Many,eff)
validateMain-EffUU (Unit ⇒[ mk-kind Many pure ] B) ()
validateMain-EffUU (Unit ⇒[ mk-kind One π ] B)     ()
validateMain-EffUU (Unit ⇒[ mk-kind Zero π ] B)    ()
-- arrow with domain ≠ Unit
validateMain-EffUU (Void ⇒[ k ] B)         ()
validateMain-EffUU (Int ⇒[ k ] B)          ()
validateMain-EffUU (Float ⇒[ k ] B)        ()
validateMain-EffUU ((_ * _) ⇒[ k ] B)      ()
validateMain-EffUU ((_ + _) ⇒[ k ] B)      ()
validateMain-EffUU ((_ ⇒[ _ ] _) ⇒[ k ] B) ()
validateMain-EffUU ((μ-type _) ⇒[ k ] B)   ()
validateMain-EffUU ((ν-type _ _) ⇒[ k ] B)   ()

------------------------------------------------------------------------
-- (2) A successfully-compiled "main" has type EffUU.
------------------------------------------------------------------------

compileFun-main-EffUU : ∀ (ctx : TopCtx) (polys : PolyCtx) (impsOf : C.String → TopCtx)
  (ty : Type) (body : RawExpr) (irFun : IR ⌊ Unit ⌋ ⌊ ty ⌋) →
  C.compileFun C.Heap false ctx polys impsOf "main" ty body ≡ inj₂ irFun →
  ty ≡ EffUU
compileFun-main-EffUU ctx polys impsOf ty body irFun eq with C.validateMain ty in veq
... | inj₂ tt  = validateMain-EffUU ty veq
... | inj₁ err = case eq of λ ()

------------------------------------------------------------------------
-- (3) findMain dispatch helpers: a head whose name ≠ "main" is skipped.
------------------------------------------------------------------------

findMain-here-no : ∀ (cf : C.CompiledFun)
  (mu : Maybe (C.CompiledFun.cfType cf ≡ EffUU)) (cont : Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋))
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
findMain-skip cf rest ¬p with cfName cf ≟cn bare "main"
... | yes p  = ⊥-elim (¬p p)
... | no ¬q  = findMain-here-no cf (isEffUU? (cfType cf)) (findMain rest) ¬q
