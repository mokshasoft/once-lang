-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.MainIRForm — discharge of `main-ir-form` (Plan 0.49 Phase 1).
--
-- `moduleToIR m ≡ just ir → ir ≡ wrapMainAsEntry (elaborate Heap seR)`: the
-- compiled `main` IR is the entry-wrap of the elaborated resolved surface term.
-- Built bottom-up:
--   (1) validateMain inversion: a successfully-compiled `main` has type EffUU.
--   (2) compileFunBody form: its IR is `elaborate Heap (resolveExpr se)`.
--   (3) compileAllFuns-go value-tracking induction: the main entry's `cfIR`.
--   (4) moduleToIR / findMain inversion: assemble.
------------------------------------------------------------------------

module Once.Adequacy.MainIRForm where

open import Data.Bool using (false)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Sum.Properties using (inj₂-injective)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ-syntax; _,_)
open import Data.List using (_∷_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Once.Type
  using (Type; Unit; Void; Int; Float; Str; Buffer; _*_; _+_; _⇒[_]_;
         μ-type; ν-type; mk-kind; Quantity; Zero; One; Many; Purity; pure; eff)
open import Once.IR using (IR)
open import Once.Surface.Syntax using (Expr; ∅; Usage)
open import Once.Surface.Elaborate using (elaborate)
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.TypeCheck.Classify using (SigEffectCtx)
open import Once.TypeCheck.Elaborate
  using (checkElab; ctxWithImportsAndSelfAndPolys; resolveExpr; PolyCtx;
         CheckElabResult; success)
import Once.Compile as C
import Once.Adequacy.AcceptSound as AS

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
-- (2) compileFunBody form: a successfully-compiled body (at EffUU, doOpt=false,
-- Heap) is `elaborate Heap (resolveExpr … se)` for the checkElab term `se`.
-- Reuses `AcceptSound.compileFunBody-aux-success` (inverts compileFunBody-aux).
------------------------------------------------------------------------

compileFunBody-form : ∀ (ctx : C.FunCtx) (polys : PolyCtx) (sigEffs : SigEffectCtx)
  (name : String) (body : RawExpr) (irFun : IR Unit EffUU) →
  C.compileFunBody C.Heap false ctx polys sigEffs name EffUU body ≡ inj₂ irFun →
  Σ-syntax (Usage 0) (λ Ψ → Σ-syntax (Expr ∅ Ψ EffUU) (λ seR → irFun ≡ elaborate C.Heap seR))
compileFunBody-form ctx polys sigEffs name body irFun eq =
  let cr = checkElab (ctxWithImportsAndSelfAndPolys ctx polys sigEffs name EffUU) body EffUU
      (Ψ , se , d , f , ce) =
        AS.compileFunBody-aux-success false ctx polys name EffUU refl cr eq
      eq2 : C.compileFunBody-aux C.Heap false ctx polys name EffUU refl (success Ψ se d f)
            ≡ inj₂ irFun
      eq2 = subst (λ c → C.compileFunBody-aux C.Heap false ctx polys name EffUU refl c ≡ inj₂ irFun)
                  ce eq
  in Ψ , resolveExpr polys ((name , EffUU) ∷ ctx) ((name , EffUU) ∷ ctx) 0 se
       , sym (inj₂-injective eq2)
