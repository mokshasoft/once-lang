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
open import Once.TypeCheck.Judgment using (_⊢ᶜ_∶_⨾_)

open C.FunInfo using (funName; funBody; funType; funIsPrimitive)

------------------------------------------------------------------------
-- Every function (threading the accumulated `FunCtx`) resolves a type and
-- has a DECLARATIVE check-mode derivation. Mirrors `compileAllFuns-go`'s
-- context threading, but the BODY premise speaks only `_⊢ᶜ_∶_⨾_`.
------------------------------------------------------------------------

data AllFunsTyped (polys : TE.PolyCtx)
     : List C.FunInfo → C.FunCtx → Set where
  tnil  : ∀ {ctx} → AllFunsTyped polys [] ctx
  tcons : ∀ {fi rest ctx ty Ψ} →
    C.resolveFunType ctx polys (C.FunInfo.funType fi) (C.FunInfo.funBody fi) ≡ inj₂ ty →
    (ctxWithImportsAndSelfAndPolys ctx polys (C.FunInfo.funName fi) ty)
      ⊢ᶜ C.FunInfo.funBody fi ∶ ty ⨾ Ψ →
    AllFunsTyped polys rest (C.extendFunCtx ctx (C.FunInfo.funName fi) ty) →
    AllFunsTyped polys (fi ∷ rest) ctx

------------------------------------------------------------------------
-- Module level.
------------------------------------------------------------------------

ModuleTyped-ef : P.Module → (String ⊎ (List C.FunInfo × List C.PolyFunInfo)) → Set
ModuleTyped-ef m (inj₁ _)            = ⊥
ModuleTyped-ef m (inj₂ (funs , polys)) =
  AllFunsTyped (C.buildPolyCtx polys) funs C.emptyFunCtx

ModuleTyped : P.Module → Set
ModuleTyped m = ModuleTyped-ef m (C.extractFunctions (C.extractAliases m) m)

------------------------------------------------------------------------
-- Derivation-indexed "valid main" predicates (over `AllFunsTyped`'s `ty`).
------------------------------------------------------------------------

EffUU : Type
EffUU = Unit ⇒[ mk-kind Many eff ] Unit

-- Every main-named function (in the derivation) resolved to EffUU.
AllMainEffUU : ∀ {polys funs ctx} → AllFunsTyped polys funs ctx → Set
AllMainEffUU tnil = ⊤
AllMainEffUU (tcons {fi = fi} {ty = ty} _ _ rest) =
  (funName fi ≡ "main" → ty ≡ EffUU) × AllMainEffUU rest

-- A non-primitive main-named function (resolved to EffUU) exists.
MainExists : ∀ {polys funs ctx} → AllFunsTyped polys funs ctx → Set
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

------------------------------------------------------------------------
-- Plan 0.103 phase 1 (D234): EVERY definition is typed once, at its declaration.
--
-- `AllFunsTyped` types the monomorphic `FunInfo`s. A GROUND telescope entry
-- (a `PolyFunInfo` whose schema is ground — every `Mu`/`Nu`-typed def, which
-- concreteness routes away from `FunInfo`) was typed only at its USES, so an
-- unused one was never typed. `PolysTyped` types each ground entry ONCE, in its
-- DECLARATION context: the monomorphic defs declared before it
-- (`C.funCtxAt … (pfunAfter pfi)`) and its telescope TAIL — the entries after
-- it in the list, which is exactly what a reference's `lookupPolyPrefix`
-- returns as the prefix. Stated structurally over the telescope, so the
-- meaning of the telescope (an environment of its entries' meanings) is a
-- plain recursion. Genuinely polymorphic entries are typed parametrically in
-- phase 6.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Type using (Ground; extractGround)
open import Once.TypeCheck.Classify using (ctxWithImportsAndPolys)
open import Once.Surface.Context using (zeroUsage)
open C.PolyFunInfo using (pfunName; pfunType; pfunBody; pfunAfter)

PolyEntryTyped : C.FunCtx → C.PolyFunInfo → List C.PolyFunInfo → Set
PolyEntryTyped imps pfi tail =
  (g : Ground (pfunType pfi)) →
  ctxWithImportsAndPolys imps (C.buildPolyCtx tail) ⊢ᶜ pfunBody pfi ∶ extractGround (pfunType pfi) g ⨾ zeroUsage

EntriesTyped : (ℕ → C.FunCtx) → List C.PolyFunInfo → Set
EntriesTyped at []           = ⊤
EntriesTyped at (pfi ∷ pfis) = PolyEntryTyped (at (pfunAfter pfi)) pfi pfis × EntriesTyped at pfis

PolysTyped-ef : String ⊎ (List C.FunInfo × List C.PolyFunInfo) → Set
PolysTyped-ef (inj₁ _)               = ⊤    -- `ModuleTyped` is already uninhabited
PolysTyped-ef (inj₂ (funs , polys))  =
  EntriesTyped (C.funCtxAt funs C.emptyFunCtx (C.buildPolyCtx polys)) polys

PolysTyped : P.Module → Set
PolysTyped m = PolysTyped-ef (C.extractFunctions (C.extractAliases m) m)
