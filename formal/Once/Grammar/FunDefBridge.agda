-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Grammar.FunDefBridge — independent relational spec for the FUNCTION
-- DEFINITION declaration parser + sound/complete bridge.
-- Bottoms at the proven `ParsesExpr` island (`Once.Grammar.ExprBridge`).
--
-- Stage 1: `ParsesParams` (parameter scanner) over the routed `parseParamsWF`.
------------------------------------------------------------------------

module Once.Grammar.FunDefBridge where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; suc; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using (≤-refl; <-trans; ≤-trans; ≤-<-trans; <-≤-trans; <⇒≤)
open import Data.List using (List; []; _∷_; length)
open import Data.String using (String)
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃; proj₁; proj₂)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst₂)

open import Once.Parser.Token
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.Parser.Module.Core using (anyWordB; ParseAtB; AllocStrategy; Decl; DFunDef; parseExprB-adapt)
open import Once.Parser.Module.FunDef.Params
  using (parseParamsB; parseParamsWF; pp-aw; pp-sep; SepK; skEq; skWord; skStop; sepClass; wrapLams)
open import Once.Parser.Module.FunDef.Body
  using (parseFunBodyB; pfb-eq; pfb-body; eqHead; drop1; drop1-≤)
open import Once.Parser.ExprRelation using (ParsesExpr)
open import Once.Parser.Expr using (parseExprWF)
open import Once.Grammar.ExprBridge using (complete-exprWFraw)
open import Once.Parser.Module.Alloc using (tryAllocB; allocStrat; drop2; drop2-≤)
open import Once.Parser.Module.FunDef.Def using (parseFunDefB; pfd-alloc; pfd-params; pfd-body)
open import Once.Parser.Module.Core using (wordHead)
open import Once.Grammar.ImportBridge using (anyWordB-inv; ij-false)
open import Once.Spec.Grammar.FunDef
  using (ParsesParams; pp-eq; pp-cons; pp-stop; pp-noword;
         ParsesFunBody; pfb-mk; ParsesAlloc; pa-some; pa-none;
         ParsesFunDef; pfd-mk)

------------------------------------------------------------------------
-- Parameter scanner.
------------------------------------------------------------------------

-- The relation moved to the spec (plan 0.84).

-- SOUNDNESS — the parser output is always a valid derivation (total parser).
sound-paramsWF : ∀ (toks : List Token) (a : Acc _<_ (length toks)) →
  ParsesParams toks (proj₁ (parseParamsWF toks a)) (proj₁ (proj₂ (parseParamsWF toks a)))
sound-paramsWF toks (acc rec) with anyWordB toks in aw
... | nothing = pp-noword (cong is-just aw)
... | just (name , tail , bnd) with anyWordB-inv aw
...   | refl with sepClass tail in sk
...     | skEq   = pp-eq sk
...     | skWord = pp-cons sk (sound-paramsWF tail (rec bnd))
...     | skStop = pp-stop sk

sound-params : ∀ (toks : List Token) →
  ParsesParams toks (proj₁ (parseParamsB toks)) (proj₁ (proj₂ (parseParamsB toks)))
sound-params toks = sound-paramsWF toks (<-wellFounded (length toks))

-- COMPLETENESS — triple-≡ (rewrite the whole total-parser result downstream).
complete-paramsWF : ∀ {toks ps rest} (a : Acc _<_ (length toks)) → ParsesParams toks ps rest →
  Σ[ b ∈ (length rest ≤ length toks) ] parseParamsWF toks a ≡ (ps , rest , b)
complete-paramsWF (acc rec) (pp-eq {name} {tail} sk) rewrite sk = _ , refl
complete-paramsWF (acc rec) (pp-cons {name} {tail} sk sub) rewrite sk
  with complete-paramsWF (rec (s≤s ≤-refl)) sub
... | (b , eqr) rewrite eqr = _ , refl
complete-paramsWF (acc rec) (pp-stop {name} {tail} sk) rewrite sk = _ , refl
complete-paramsWF (acc rec) (pp-noword {toks} wf) rewrite ij-false wf = _ , refl

complete-params : ∀ {toks ps rest} → ParsesParams toks ps rest →
  Σ[ b ∈ (length rest ≤ length toks) ] parseParamsB toks ≡ (ps , rest , b)
complete-params {toks} d = complete-paramsWF (<-wellFounded (length toks)) d

------------------------------------------------------------------------
-- Function body (after `=`). Bottoms at the proven `ParsesExpr` island:
-- `parseExprWF` already carries the derivation; `complete-exprWFraw` rebuilds it.
------------------------------------------------------------------------

-- The relation moved to the spec (plan 0.84).

sound-body : ∀ {name alloc params toks d rest bnd} →
  parseFunBodyB name alloc params toks ≡ just (d , rest , bnd) →
  ParsesFunBody name alloc params toks d rest
sound-body {name} {alloc} {params} {toks} h with eqHead toks in eh
... | false with () ← h
... | true with parseExprWF (drop1 toks) (<-wellFounded (length (drop1 toks))) in subeq
...   | nothing with () ← h
...   | just (body , rest' , d) with refl ← just-injective h = pfb-mk eh d

complete-body : ∀ {name alloc params toks d rest} → ParsesFunBody name alloc params toks d rest →
  Σ[ bnd ∈ (length rest < length toks) ] parseFunBodyB name alloc params toks ≡ just (d , rest , bnd)
complete-body (pfb-mk {toks = toks} eh pe) rewrite eh
  with complete-exprWFraw pe (<-wellFounded (length (drop1 toks)))
... | (d' , eqd) rewrite eqd = _ , refl

------------------------------------------------------------------------
-- Allocation annotation (`@stack` …). `allocStrat` classifies the head;
-- `tryAllocB` is total (none ⇒ unchanged input).
------------------------------------------------------------------------

-- The relation moved to the spec (plan 0.84).

sound-alloc : ∀ (toks : List Token) →
  ParsesAlloc toks (proj₁ (tryAllocB toks)) (proj₁ (proj₂ (tryAllocB toks)))
sound-alloc toks with allocStrat toks in as
... | just strat = pa-some as
... | nothing    = pa-none as

complete-alloc : ∀ {toks mA rest} → ParsesAlloc toks mA rest →
  Σ[ b ∈ (length rest ≤ length toks) ] tryAllocB toks ≡ (mA , rest , b)
complete-alloc (pa-some {toks} as) rewrite as = drop2-≤ toks , refl
complete-alloc (pa-none {toks} as) rewrite as = ≤-refl , refl

------------------------------------------------------------------------
-- Function definition = alloc then params then body.
------------------------------------------------------------------------

-- The relation moved to the spec (plan 0.84).

sound-fundef : ∀ {name toks d rest bnd} → parseFunDefB name toks ≡ just (d , rest , bnd) →
  ParsesFunDef name toks d rest
sound-fundef {name} {toks} h with tryAllocB toks in ta
... | (alloc , toks' , allocBnd) with parseParamsB toks' in pp
...   | (params , toks'' , paramsBnd) with parseFunBodyB name alloc params toks'' in fb
...     | nothing with () ← h
...     | just (d , rest , bodyBnd) with refl ← just-injective h =
          pfd-mk (subst₂ (ParsesAlloc toks) (cong proj₁ ta) (cong (λ z → proj₁ (proj₂ z)) ta) (sound-alloc toks))
                 (subst₂ (ParsesParams toks') (cong proj₁ pp) (cong (λ z → proj₁ (proj₂ z)) pp) (sound-params toks'))
                 (sound-body fb)

complete-fundef : ∀ {name toks d rest} → ParsesFunDef name toks d rest →
  Σ[ bnd ∈ (length rest < length toks) ] parseFunDefB name toks ≡ just (d , rest , bnd)
complete-fundef (pfd-mk pa pp pb) with complete-alloc pa
... | (aBnd , eqA) rewrite eqA with complete-params pp
...   | (pBnd , eqP) rewrite eqP with complete-body pb
...     | (bBnd , eqB) rewrite eqB = _ , refl
