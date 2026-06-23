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

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type
  using (Type; Unit; Void; Int; Float; Str; Buffer; _*_; _+_; _⇒[_]_;
         μ-type; ν-type; mk-kind; Quantity; Zero; One; Many; Purity; pure; eff)
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
