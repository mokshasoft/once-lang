-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.TypeCheck.ErrorProofs
--
-- Plan 0.3, gap G4 (partial): error-preservation theorems — proofs
-- that each elaborator failure path emits a string equal to
-- `renderError` of a specific `TypeError` variant.
--
-- These theorems close the gap between the raw-string failure API
-- and the structured-error vocabulary, without requiring a full
-- signature refactor. When the elaborator emits `failure "…"`, we
-- can point to a canonical structured error that produced that
-- string, giving tooling a well-typed contract.
--
-- Reference: plans/0.3-frontend-verification-gaps.md, gap G4.
------------------------------------------------------------------------

module Once.TypeCheck.ErrorProofs where

open import Data.String using (String; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (∃; ∃-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (Type)
open import Once.TypeCheck.Raw as Raw
  using (RawExpr; RVar; RLam; RQualified)
open import Once.TypeCheck.Elaborate
  using (NamedCtx; inferElab; checkElab; InferElabResult; CheckElabResult;
         success; failure; lookupLocal; lookupImport)
open import Once.TypeCheck.Error
  using (TypeError; renderError;
         LambdaInInferMode; InlInInferMode; InrInInferMode;
         InitialInInferMode; UnboundVariable; UnboundQualified)

------------------------------------------------------------------------
-- Bundle wrapping for lookups, reused from Soundness style
------------------------------------------------------------------------

ImportLookupBundle : (xs : _) → (q : _) → Set
ImportLookupBundle xs q = ∃[ r ] lookupImport xs q ≡ r

importLookupBundle : ∀ xs q → ImportLookupBundle xs q
importLookupBundle xs q = lookupImport xs q , refl

------------------------------------------------------------------------
-- Unconditional-failure paths
--
-- These are cases where the elaborator emits a fixed error string
-- regardless of context. The proof is a direct `refl`: pattern-match
-- on the equation, and Agda normalises the RHS to the string that
-- equals `renderError <variant>`.
------------------------------------------------------------------------

-- `RLam` in infer mode is always rejected — the elaborator has no
-- way to infer the domain type without an annotation.
lam-infer-is-LambdaInInferMode :
  ∀ (ctx : NamedCtx) (x : String) (body : RawExpr) {msg : String}
  → inferElab ctx (RLam x body) ≡ failure msg
  → msg ≡ renderError LambdaInInferMode
lam-infer-is-LambdaInInferMode ctx x body refl = refl

-- `inl` applied but used in infer mode — rejected because the sum
-- type can't be inferred from the argument alone.
inl-app-infer-is-InlInInferMode :
  ∀ (ctx : NamedCtx) (arg : RawExpr) {msg : String}
  → inferElab ctx (Raw.RApp (RVar "inl") arg) ≡ failure msg
  → msg ≡ renderError InlInInferMode
inl-app-infer-is-InlInInferMode ctx arg refl = refl

inr-app-infer-is-InrInInferMode :
  ∀ (ctx : NamedCtx) (arg : RawExpr) {msg : String}
  → inferElab ctx (Raw.RApp (RVar "inr") arg) ≡ failure msg
  → msg ≡ renderError InrInInferMode
inr-app-infer-is-InrInInferMode ctx arg refl = refl

initial-app-infer-is-InitialInInferMode :
  ∀ (ctx : NamedCtx) (arg : RawExpr) {msg : String}
  → inferElab ctx (Raw.RApp (RVar "initial") arg) ≡ failure msg
  → msg ≡ renderError InitialInInferMode
initial-app-infer-is-InitialInInferMode ctx arg refl = refl

------------------------------------------------------------------------
-- Conditional-failure paths
--
-- These require a side-condition to determine the failure variant.
-- We case-split on the relevant lookup (or sub-result) using the
-- bundle+rewrite pattern from `Soundness`, then close each branch.
------------------------------------------------------------------------

-- `RQualified name alias` fails when the imports table doesn't
-- contain `alias.name`. The emitted message equals
-- `renderError (UnboundQualified name alias)`.
qualified-not-found-is-UnboundQualified :
  ∀ (ctx : NamedCtx) (name alias : String) {msg : String}
  → lookupImport (NamedCtx.imports ctx) (alias ++ "." ++ name) ≡ nothing
  → inferElab ctx (RQualified name alias) ≡ failure msg
  → msg ≡ renderError (UnboundQualified name alias)
qualified-not-found-is-UnboundQualified ctx name alias eqLookup eqFail
  rewrite eqLookup with eqFail
... | refl = refl
