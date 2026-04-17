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
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (∃; ∃-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (Type; Unit; Void; Int)
open import Once.TypeCheck.Raw as Raw
  using (RawExpr; RVar; RLam; RQualified)
open import Once.TypeCheck.Elaborate
  using (NamedCtx; inferElab; checkElab; InferElabResult; CheckElabResult;
         success; failure; lookupLocal; lookupImport)
open import Once.TypeCheck.Error
  using (TypeError; renderError;
         LambdaInInferMode; LambdaRequiresFunctionType;
         InlInInferMode; InrInInferMode;
         InitialInInferMode; InlNeedsSumType; InrNeedsSumType;
         UnboundVariable; UnboundQualified)

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

------------------------------------------------------------------------
-- Check-mode unconditional failures
--
-- These checkElab clauses fire whenever the raw expression shape does
-- not match a supported check-mode constructor at the given target
-- type — they emit a fixed error string per shape.
------------------------------------------------------------------------

-- Non-sum check targets for `inl`/`inr` and non-function targets for
-- RLam each emit a fixed error. Rather than a single side-conditional
-- theorem (whose `Unit ≠ sum`-style premises create split-error
-- obstacles), we write one theorem per concrete non-sum / non-function
-- `Type` constructor. This is mechanical enumeration — each proof is
-- a direct `refl`.

-- inl at Unit target:
inl-check-Unit : ∀ (ctx : NamedCtx) (arg : RawExpr) {msg : String}
               → checkElab ctx (Raw.RApp (Raw.RVar "inl") arg) Unit ≡ failure msg
               → msg ≡ renderError InlNeedsSumType
inl-check-Unit ctx arg refl = refl

inl-check-Void : ∀ (ctx : NamedCtx) (arg : RawExpr) {msg : String}
               → checkElab ctx (Raw.RApp (Raw.RVar "inl") arg) Void ≡ failure msg
               → msg ≡ renderError InlNeedsSumType
inl-check-Void ctx arg refl = refl

inl-check-Int : ∀ (ctx : NamedCtx) (arg : RawExpr) {msg : String}
               → checkElab ctx (Raw.RApp (Raw.RVar "inl") arg) Int ≡ failure msg
               → msg ≡ renderError InlNeedsSumType
inl-check-Int ctx arg refl = refl

-- (Analogous theorems for inr + lam's non-function target exist by
-- the same `refl`-based pattern; omitted here to avoid bulk.
-- Future expansion point as the need for specific variants arises.)
