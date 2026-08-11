-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.MainIRForm — compile-inversion helpers for the `main` entry.
--
-- Plan 0.55: the `main-ir-form`/`Form`/`Payload`/`caf-go-find-form` extraction
-- was SUPERSEDED by the bundle-based `Once.Adequacy.MainForm` (which reads the
-- selected main node off a `FunBundle`). What remains here is the small set of
-- compile-inversion lemmas still consumed by `ModuleComplete`/`FunBundle`:
--   * `validateMain-EffUU`   — a compiled `main` has type `EffUU`.
--   * `compileFun-main-EffUU`— its `compileFun`-level corollary.
--   * `findMain-here-no` / `findMain-skip` — a non-`main` head is skipped.
--   * `bare-injective`       — `bare` is injective on names.
------------------------------------------------------------------------

module Once.Adequacy.MainIRForm where

open import Data.Bool using (Bool; false; true)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Once.CanonicalName using (CanonicalName; bare) renaming (_≟ᶜ_ to _≟cn_)
open import Relation.Nullary using (yes; no; ¬_)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Adequacy.SourceTrace using (findMain; findMain-here; isUnit?)

open import Once.Type
  using (Type; Unit; Void; Int; Float; Str; Buffer; _*_; _+_; _⇒[_]_;
         μ-type; ν-type; mk-kind; Quantity; Zero; One; Many; Purity; pure; eff)
open import Once.IR using (IR)
open import Once.IRTy using (⌊_⌋)
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.TypeCheck.Classify using (SigEffectCtx; NamedCtx)
open import Once.TypeCheck.Elaborate using (PolyCtx)
import Once.Compile as C
open import Once.Parser using (FunInfo)
open FunInfo

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
validateMain-EffUU Str        ()
validateMain-EffUU Buffer     ()
validateMain-EffUU (_ * _)    ()
validateMain-EffUU (_ + _)    ()
validateMain-EffUU (μ-type _) ()
validateMain-EffUU (ν-type _) ()
-- arrow with domain Unit, kind (Many,eff), but codomain ≠ Unit
validateMain-EffUU (Unit ⇒[ mk-kind Many eff ] Void)         ()
validateMain-EffUU (Unit ⇒[ mk-kind Many eff ] Int)          ()
validateMain-EffUU (Unit ⇒[ mk-kind Many eff ] Float)        ()
validateMain-EffUU (Unit ⇒[ mk-kind Many eff ] Str)          ()
validateMain-EffUU (Unit ⇒[ mk-kind Many eff ] Buffer)       ()
validateMain-EffUU (Unit ⇒[ mk-kind Many eff ] (_ * _))      ()
validateMain-EffUU (Unit ⇒[ mk-kind Many eff ] (_ + _))      ()
validateMain-EffUU (Unit ⇒[ mk-kind Many eff ] (_ ⇒[ _ ] _)) ()
validateMain-EffUU (Unit ⇒[ mk-kind Many eff ] (μ-type _))   ()
validateMain-EffUU (Unit ⇒[ mk-kind Many eff ] (ν-type _))   ()
-- arrow with domain Unit but kind ≠ (Many,eff)
validateMain-EffUU (Unit ⇒[ mk-kind Many pure ] B) ()
validateMain-EffUU (Unit ⇒[ mk-kind One π ] B)     ()
validateMain-EffUU (Unit ⇒[ mk-kind Zero π ] B)    ()
-- arrow with domain ≠ Unit
validateMain-EffUU (Void ⇒[ k ] B)         ()
validateMain-EffUU (Int ⇒[ k ] B)          ()
validateMain-EffUU (Float ⇒[ k ] B)        ()
validateMain-EffUU (Str ⇒[ k ] B)          ()
validateMain-EffUU (Buffer ⇒[ k ] B)       ()
validateMain-EffUU ((_ * _) ⇒[ k ] B)      ()
validateMain-EffUU ((_ + _) ⇒[ k ] B)      ()
validateMain-EffUU ((_ ⇒[ _ ] _) ⇒[ k ] B) ()
validateMain-EffUU ((μ-type _) ⇒[ k ] B)   ()
validateMain-EffUU ((ν-type _) ⇒[ k ] B)   ()

------------------------------------------------------------------------
-- (2) A successfully-compiled "main" has type EffUU.
------------------------------------------------------------------------

compileFun-main-EffUU : ∀ (ctx : C.FunCtx) (polys : PolyCtx) (sigEffs : SigEffectCtx)
  (ty : Type) (body : RawExpr) (irFun : IR ⌊ Unit ⌋ ⌊ ty ⌋) →
  C.compileFun C.Heap false ctx polys sigEffs "main" ty body ≡ inj₂ irFun →
  ty ≡ EffUU
compileFun-main-EffUU ctx polys sigEffs ty body irFun eq with C.validateMain ty in veq
... | inj₂ tt  = validateMain-EffUU ty veq
... | inj₁ err = case eq of λ ()

------------------------------------------------------------------------
-- (3) findMain dispatch helpers: a head whose name ≠ "main" is skipped.
------------------------------------------------------------------------

findMain-here-no : ∀ (cf : C.CompiledFun) (b : Bool)
  (mu : Maybe (C.CompiledFun.cfType cf ≡ Unit)) (cont : Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋))
  (¬p : ¬ (C.CompiledFun.cfName cf ≡ bare "main")) →
  findMain-here cf b (no ¬p) mu cont ≡ cont
findMain-here-no cf false mu cont ¬p = refl
findMain-here-no cf true  mu cont ¬p = refl

open C.CompiledFun using (cfType; cfName; cfIsPrimitive)

-- `bare` is injective (single-component CanonicalName), so a String name ≠
-- "main" lifts to its CanonicalName ≠ `bare "main"`.
bare-injective : ∀ {s t} → bare s ≡ bare t → s ≡ t
bare-injective refl = refl

-- A head whose name ≠ "main" is skipped by findMain.
findMain-skip : ∀ (cf : C.CompiledFun) (rest : List C.CompiledFun) →
  ¬ (cfName cf ≡ bare "main") → findMain (cf ∷ rest) ≡ findMain rest
findMain-skip cf rest ¬p with cfName cf ≟cn bare "main"
... | yes p  = ⊥-elim (¬p p)
... | no ¬q  = findMain-here-no cf (cfIsPrimitive cf) (isUnit? (cfType cf)) (findMain rest) ¬q
