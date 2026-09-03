-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Module — what it MEANS for a resolved module to be well-typed
-- and to have a valid entry point (Plan 0.84). No proof lives here.
--
-- READ THIS BEFORE TRUSTING `correct`. Unlike `Once.Spec.Parsing`, this
-- module is NOT clean, and the split exists to make that visible rather than
-- to hide it behind a proof module:
--
--   * `ModuleTyped m` is defined by RUNNING the front end —
--     `ModuleTyped-ef m (extractFunctions (extractAliases m) m)`. The spec's
--     notion of "well-typed" therefore quantifies over whatever the extractor
--     happens to produce, instead of over the module's own syntax.
--   * `AllFunsTyped` names `ctxWithImportsAndSelfAndPolys` from
--     `Once.TypeCheck.Elaborate` — the ELABORATOR — and `resolveFunType`,
--     `extendFunCtx`, `buildPolyCtx`, `collectSigEffects` from `Once.Compile`.
--
-- Its BODY premise is honest: `_⊢ᶜ_∶_⨾_`, the declarative judgment, with no
-- elaborator function in it. It is the CONTEXT CONSTRUCTION and the function
-- list that come from the implementation.
--
-- Recorded as D137's open hole; **plan 0.59 owns closing it.** Do not paper
-- over it by moving these definitions back next to their proofs.
------------------------------------------------------------------------

module Once.Spec.Module where

open import Data.Bool using (false)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Data.List using (List; []; _∷_)
open import Data.String using (String)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Type using (Type; Unit; _⇒[_]_; mk-kind; Many; eff)
import Once.Compile as C
import Once.Parser.Module.Core as P
open import Once.TypeCheck.Elaborate as TE using (ctxWithImportsAndSelfAndPolys)
open import Once.TypeCheck.Classify using (SigEffectCtx)
open import Once.TypeCheck.Judgment using (_⊢ᶜ_∶_⨾_)

open C.FunInfo using (funName; funBody; funType; funIsPrimitive)

------------------------------------------------------------------------
-- Every function (threading the accumulated `FunCtx`) resolves a type and
-- has a DECLARATIVE check-mode derivation. Mirrors `compileAllFuns-go`'s
-- context threading, but the BODY premise speaks only `_⊢ᶜ_∶_⨾_`.
------------------------------------------------------------------------

data AllFunsTyped (polys : TE.PolyCtx) (sigEffs : SigEffectCtx)
     : List C.FunInfo → C.FunCtx → Set where
  tnil  : ∀ {ctx} → AllFunsTyped polys sigEffs [] ctx
  tcons : ∀ {fi rest ctx ty Ψ} →
    C.resolveFunType ctx polys (C.FunInfo.funType fi) (C.FunInfo.funBody fi) ≡ inj₂ ty →
    (ctxWithImportsAndSelfAndPolys ctx polys sigEffs (C.FunInfo.funName fi) ty)
      ⊢ᶜ C.FunInfo.funBody fi ∶ ty ⨾ Ψ →
    AllFunsTyped polys sigEffs rest (C.extendFunCtx ctx (C.FunInfo.funName fi) ty) →
    AllFunsTyped polys sigEffs (fi ∷ rest) ctx

------------------------------------------------------------------------
-- Module level.
------------------------------------------------------------------------

ModuleTyped-ef : P.Module → (String ⊎ (List C.FunInfo × List C.PolyFunInfo)) → Set
ModuleTyped-ef m (inj₁ _)            = ⊥
ModuleTyped-ef m (inj₂ (funs , polys)) =
  AllFunsTyped (C.buildPolyCtx polys) (C.collectSigEffects (C.Module.decls m)) funs C.emptyFunCtx

ModuleTyped : P.Module → Set
ModuleTyped m = ModuleTyped-ef m (C.extractFunctions (C.extractAliases m) m)

------------------------------------------------------------------------
-- Derivation-indexed "valid main" predicates (over `AllFunsTyped`'s `ty`).
------------------------------------------------------------------------

EffUU : Type
EffUU = Unit ⇒[ mk-kind Many eff ] Unit

-- Every main-named function (in the derivation) resolved to EffUU.
AllMainEffUU : ∀ {polys sigEffs funs ctx} → AllFunsTyped polys sigEffs funs ctx → Set
AllMainEffUU tnil = ⊤
AllMainEffUU (tcons {fi = fi} {ty = ty} _ _ rest) =
  (funName fi ≡ "main" → ty ≡ EffUU) × AllMainEffUU rest

-- A non-primitive main-named function (resolved to EffUU) exists.
MainExists : ∀ {polys sigEffs funs ctx} → AllFunsTyped polys sigEffs funs ctx → Set
MainExists tnil = ⊥
MainExists (tcons {fi = fi} {ty = ty} _ _ rest) =
  ((funName fi ≡ "main") × (funIsPrimitive fi ≡ false) × (ty ≡ EffUU)) ⊎ MainExists rest

ModuleMainEffUU-ef : ∀ (m : P.Module) (ef : String ⊎ (List C.FunInfo × List C.PolyFunInfo))
  → ModuleTyped-ef m ef → Set
ModuleMainEffUU-ef m (inj₂ _) mt = AllMainEffUU mt

ModuleMainExists-ef : ∀ (m : P.Module) (ef : String ⊎ (List C.FunInfo × List C.PolyFunInfo))
  → ModuleTyped-ef m ef → Set
ModuleMainExists-ef m (inj₂ _) mt = MainExists mt

HasValidMain-decl : ∀ (m : P.Module) → ModuleTyped m → Set
HasValidMain-decl m mt =
  ModuleMainEffUU-ef m (C.extractFunctions (C.extractAliases m) m) mt
  × ModuleMainExists-ef m (C.extractFunctions (C.extractAliases m) m) mt
