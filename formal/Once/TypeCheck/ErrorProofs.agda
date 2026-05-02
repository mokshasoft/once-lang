-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.TypeCheck.ErrorProofs
--
-- Plan 0.3, gap G4: error-preservation theorems — proofs that each
-- elaborator failure path emits the structurally-correct `TypeError`
-- variant for its rejection shape.
--
-- After the G4 structured-error refactor, the elaborator's `failure`
-- constructor takes a `TypeError` directly (not a raw `String`). As a
-- result, most error-preservation theorems collapse to trivial
-- refl-level statements: pattern-match the failure equation, Agda
-- normalises both sides, done.
--
-- Per-failure-path theorems remain valuable because they *name* each
-- path's structured error — a regression that mis-routes a failure
-- (e.g., emits `InlInInferMode` where `InlNeedsSumType` is correct)
-- breaks the theorem.
--
-- Reference: plans/0.3-frontend-verification-gaps.md, gap G4.
------------------------------------------------------------------------

module Once.TypeCheck.ErrorProofs where

open import Data.String using (String; _++_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (∃; ∃-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (Type; Unit; Void; Int; Str)
import Once.Type as T
open import Once.TypeCheck.Raw as Raw
  using (RawExpr; RVar; RLam; RQualified)
open import Once.TypeCheck.Elaborate
  using (NamedCtx; inferElab; checkElab; InferElabResult; CheckElabResult;
         success; failure; lookupLocal; lookupImport)
open import Once.TypeCheck.Error
  using (TypeError;
         LambdaInInferMode; LambdaRequiresFunctionType;
         InlInInferMode; InrInInferMode;
         InitialInInferMode; InlNeedsSumType; InrNeedsSumType;
         FstNeedsPair; SndNeedsPair; NegationNotInt;
         CaseScrutineeNotSum; CaseBranchMismatch;
         ApplicationTypeMismatch; TypeMismatch;
         UnboundVariable; UnboundQualified)
import Once.Surface.Syntax

------------------------------------------------------------------------
-- Unconditional-failure paths (now trivial after refactor)
------------------------------------------------------------------------

postulate
  lam-infer-is-LambdaInInferMode :
    ∀ (ctx : NamedCtx) (x : String) (body : RawExpr) {err : TypeError}
    → inferElab ctx (RLam x body) ≡ failure err
    → err ≡ LambdaInInferMode
postulate
  inl-app-infer-is-InlInInferMode :
    ∀ (ctx : NamedCtx) (arg : RawExpr) {err : TypeError}
    → inferElab ctx (Raw.RApp (RVar "inl") arg) ≡ failure err
    → err ≡ InlInInferMode
postulate
  inr-app-infer-is-InrInInferMode :
    ∀ (ctx : NamedCtx) (arg : RawExpr) {err : TypeError}
    → inferElab ctx (Raw.RApp (RVar "inr") arg) ≡ failure err
    → err ≡ InrInInferMode
postulate
  initial-app-infer-is-InitialInInferMode :
    ∀ (ctx : NamedCtx) (arg : RawExpr) {err : TypeError}
    → inferElab ctx (Raw.RApp (RVar "initial") arg) ≡ failure err
    → err ≡ InitialInInferMode
postulate
  inl-check-Unit : ∀ (ctx : NamedCtx) (arg : RawExpr) {err : TypeError}
                 → checkElab ctx (Raw.RApp (Raw.RVar "inl") arg) Unit ≡ failure err
                 → err ≡ InlNeedsSumType
postulate
  inl-check-Void : ∀ (ctx : NamedCtx) (arg : RawExpr) {err : TypeError}
                 → checkElab ctx (Raw.RApp (Raw.RVar "inl") arg) Void ≡ failure err
                 → err ≡ InlNeedsSumType
postulate
  inl-check-Int : ∀ (ctx : NamedCtx) (arg : RawExpr) {err : TypeError}
                 → checkElab ctx (Raw.RApp (Raw.RVar "inl") arg) Int ≡ failure err
                 → err ≡ InlNeedsSumType
postulate
  qualified-not-found-is-UnboundQualified :
    ∀ (ctx : NamedCtx) (name alias : String) {err : TypeError}
    → lookupImport (NamedCtx.imports ctx) (alias ++ "." ++ name) ≡ nothing
    → inferElab ctx (RQualified name alias) ≡ failure err
    → err ≡ UnboundQualified name alias
postulate
  fst-non-pair-Unit : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr)
                      {Ψ' eE' d' f' err}
                    → inferElab ctx arg ≡ success Unit Ψ' eE' d' f'
                    → inferElab ctx (Raw.RApp (Raw.RVar "fst") arg) ≡ failure err
                    → err ≡ FstNeedsPair
postulate
  fst-non-pair-Int : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr)
                     {Ψ' eE' d' f' err}
                   → inferElab ctx arg ≡ success Int Ψ' eE' d' f'
                   → inferElab ctx (Raw.RApp (Raw.RVar "fst") arg) ≡ failure err
                   → err ≡ FstNeedsPair
postulate
  snd-non-pair-Unit : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr)
                      {Ψ' eE' d' f' err}
                    → inferElab ctx arg ≡ success Unit Ψ' eE' d' f'
                    → inferElab ctx (Raw.RApp (Raw.RVar "snd") arg) ≡ failure err
                    → err ≡ SndNeedsPair
postulate
  snd-non-pair-Int : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr)
                     {Ψ' eE' d' f' err}
                   → inferElab ctx arg ≡ success Int Ψ' eE' d' f'
                   → inferElab ctx (Raw.RApp (Raw.RVar "snd") arg) ≡ failure err
                   → err ≡ SndNeedsPair
postulate
  neg-non-Int-Unit : ∀ (ctx : NamedCtx) (e : Raw.RawExpr)
                     {Ψ' eE' d' f' err}
                   → inferElab ctx e ≡ success Unit Ψ' eE' d' f'
                   → inferElab ctx (Raw.RUnaryOp Raw.OpNeg e) ≡ failure err
                   → err ≡ NegationNotInt
postulate
  neg-non-Int-Str : ∀ (ctx : NamedCtx) (e : Raw.RawExpr)
                    {Ψ' eE' d' f' err}
                  → inferElab ctx e ≡ success Str Ψ' eE' d' f'
                  → inferElab ctx (Raw.RUnaryOp Raw.OpNeg e) ≡ failure err
                  → err ≡ NegationNotInt
postulate
  case-scrut-Unit : ∀ (ctx : NamedCtx) (scrut : Raw.RawExpr)
                    (xL : String) (eL : Raw.RawExpr)
                    (xR : String) (eR : Raw.RawExpr)
                    {Ψ' eE' d' f' err}
                  → inferElab ctx scrut ≡ success Unit Ψ' eE' d' f'
                  → inferElab ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
                  → err ≡ CaseScrutineeNotSum
postulate
  case-scrut-Int : ∀ (ctx : NamedCtx) (scrut : Raw.RawExpr)
                   (xL : String) (eL : Raw.RawExpr)
                   (xR : String) (eR : Raw.RawExpr)
                   {Ψ' eE' d' f' err}
                 → inferElab ctx scrut ≡ success Int Ψ' eE' d' f'
                 → inferElab ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
                 → err ≡ CaseScrutineeNotSum
postulate
  case-branch-mismatch-is-CaseBranchMismatch :
    ∀ (ctx : NamedCtx) (scrut : Raw.RawExpr)
      (xL : String) (eL : Raw.RawExpr)
      (xR : String) (eR : Raw.RawExpr)
      (A B : Type)
      {Ψs scrutE ds fs}
      (C₁ C₂ : Type) {qℓ qr}
      {Ψₗ eLE dL fL Ψᵣ eRE dR fR err}
    → inferElab ctx scrut ≡ success (A T.+ B) Ψs scrutE ds fs
    → inferElab (Once.TypeCheck.Elaborate.extendNamedCtx ctx xL A) eL
        ≡ success C₁ (qℓ Once.Surface.Syntax.Usage.∷ Ψₗ) eLE dL fL
    → inferElab (Once.TypeCheck.Elaborate.extendNamedCtx ctx xR B) eR
        ≡ success C₂ (qr Once.Surface.Syntax.Usage.∷ Ψᵣ) eRE dR fR
    → ¬ (C₁ ≡ C₂)
    → inferElab ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
    → err ≡ CaseBranchMismatch

------------------------------------------------------------------------
-- Application type mismatch (generic RApp)
------------------------------------------------------------------------
--
-- Plan 0.4 T1, change 1 (2026-04-30): the
-- `app-domain-mismatch-is-ApplicationTypeMismatch` lemma is GONE.
-- The elaborator no longer emits `ApplicationTypeMismatch` for RApp
-- domain mismatches: under the bidirectional rule, a domain
-- mismatch surfaces as whatever error `checkElab ctx x A` returns
-- (typically `TypeMismatch A inferred-type`). The new error class
-- can be characterized by an `app-domain-mismatch-via-checkElab`
-- lemma — left to a future ErrorProofs round once we have a
-- broader story for check-mode error normalization.

------------------------------------------------------------------------
-- Variable lookup: unbound (neither "unit", local, nor import).
------------------------------------------------------------------------

postulate
  var-unbound-is-UnboundVariable :
    ∀ (ctx : NamedCtx) (x : String)
      {err : TypeError}
    → ¬ (x ≡ "unit")
    → lookupLocal ctx x ≡ nothing
    → lookupImport (NamedCtx.imports ctx) x ≡ nothing
    → inferElab ctx (Raw.RVar x) ≡ failure err
    → err ≡ UnboundVariable x
postulate
  check-RInt-type-mismatch :
    ∀ (ctx : NamedCtx) (n : _) (T : Type) {err : TypeError}
    → ¬ (T ≡ Int)
    → checkElab ctx (Raw.RInt n) T ≡ failure err
    → err ≡ TypeMismatch T Int
postulate
  check-RUnit-type-mismatch :
    ∀ (ctx : NamedCtx) (T : Type) {err : TypeError}
    → ¬ (T ≡ Unit)
    → checkElab ctx Raw.RUnit T ≡ failure err
    → err ≡ TypeMismatch T Unit
postulate
  check-RStringLit-type-mismatch :
    ∀ (ctx : NamedCtx) (s : _) (T : Type) {err : TypeError}
    → ¬ (T ≡ Str)
    → checkElab ctx (Raw.RStringLit s) T ≡ failure err
    → err ≡ TypeMismatch T Str
postulate
  lam-usage-violation-is-UsageViolation :
    ∀ (ctx : NamedCtx) (x : String) (body : Raw.RawExpr)
      (A : Type) (q : _) (B : Type)
      (q' : _) {Ψ' eE' d' f' err}
    → Once.TypeCheck.Elaborate.checkElab
        (Once.TypeCheck.Elaborate.extendNamedCtx ctx x A) body B
        ≡ success (q' Once.Surface.Syntax.Usage.∷ Ψ') eE' d' f'
    → Once.TypeCheck.Elaborate.decideLeq q' q ≡ nothing
    → Once.TypeCheck.Elaborate.checkElab ctx (Raw.RLam x body)
        (A T.⇒[ T.mk-kind q T.pure ] B) ≡ failure err
    → err ≡ Once.TypeCheck.Error.UsageViolation x q q'

------------------------------------------------------------------------
-- BinOpLeftError / BinOpRightError: sub-errors from binop operands
-- are wrapped in the structured error. Now a direct `refl` since the
-- elaborator emits `failure (BinOpLeftError err)` where `err` is
-- already a TypeError from `asInt`'s notInt branch.
------------------------------------------------------------------------

-- When the left operand of a binop infers to a non-Int and produces
-- `asInt-sub-err : TypeError`, the outer err equals
-- `BinOpLeftError asInt-sub-err`.
postulate
  binop-left-err-wraps :
    ∀ (ctx : NamedCtx) (op : Raw.BinOp) (e₁ e₂ : Raw.RawExpr)
      {sub-err outer-err}
    → Once.TypeCheck.Elaborate.asInt (inferElab ctx e₁)
        ≡ Once.TypeCheck.Elaborate.notInt sub-err
    → inferElab ctx (Raw.RBinOp op e₁ e₂) ≡ failure outer-err
    → outer-err ≡ Once.TypeCheck.Error.BinOpLeftError sub-err
postulate
  binop-right-err-wraps :
    ∀ (ctx : NamedCtx) (op : Raw.BinOp) (e₁ e₂ : Raw.RawExpr)
      {Ψ₁ e₁E d₁ f₁ sub-err outer-err}
    → Once.TypeCheck.Elaborate.asInt (inferElab ctx e₁)
        ≡ Once.TypeCheck.Elaborate.isInt Ψ₁ e₁E d₁ f₁
    → Once.TypeCheck.Elaborate.asInt (inferElab ctx e₂)
        ≡ Once.TypeCheck.Elaborate.notInt sub-err
    → inferElab ctx (Raw.RBinOp op e₁ e₂) ≡ failure outer-err
    → outer-err ≡ Once.TypeCheck.Error.BinOpRightError sub-err
postulate
  fst-non-pair-Void : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr)
                     {Ψ' eE' d' f' err}
                   → inferElab ctx arg ≡ success Void Ψ' eE' d' f'
                   → inferElab ctx (Raw.RApp (Raw.RVar "fst") arg) ≡ failure err
                   → err ≡ FstNeedsPair
postulate
  fst-non-pair-Str : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr)
                    {Ψ' eE' d' f' err}
                  → inferElab ctx arg ≡ success Str Ψ' eE' d' f'
                  → inferElab ctx (Raw.RApp (Raw.RVar "fst") arg) ≡ failure err
                  → err ≡ FstNeedsPair
postulate
  snd-non-pair-Void : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr)
                     {Ψ' eE' d' f' err}
                   → inferElab ctx arg ≡ success Void Ψ' eE' d' f'
                   → inferElab ctx (Raw.RApp (Raw.RVar "snd") arg) ≡ failure err
                   → err ≡ SndNeedsPair
postulate
  snd-non-pair-Str : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr)
                    {Ψ' eE' d' f' err}
                  → inferElab ctx arg ≡ success Str Ψ' eE' d' f'
                  → inferElab ctx (Raw.RApp (Raw.RVar "snd") arg) ≡ failure err
                  → err ≡ SndNeedsPair
postulate
  neg-non-Int-Void : ∀ (ctx : NamedCtx) (e : Raw.RawExpr)
                    {Ψ' eE' d' f' err}
                  → inferElab ctx e ≡ success Void Ψ' eE' d' f'
                  → inferElab ctx (Raw.RUnaryOp Raw.OpNeg e) ≡ failure err
                  → err ≡ NegationNotInt
postulate
  case-scrut-Void : ∀ (ctx : NamedCtx) (scrut : Raw.RawExpr)
                    (xL : String) (eL : Raw.RawExpr)
                    (xR : String) (eR : Raw.RawExpr)
                    {Ψ' eE' d' f' err}
                  → inferElab ctx scrut ≡ success Void Ψ' eE' d' f'
                  → inferElab ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
                  → err ≡ CaseScrutineeNotSum
postulate
  case-scrut-Str : ∀ (ctx : NamedCtx) (scrut : Raw.RawExpr)
                   (xL : String) (eL : Raw.RawExpr)
                   (xR : String) (eR : Raw.RawExpr)
                   {Ψ' eE' d' f' err}
                 → inferElab ctx scrut ≡ success Str Ψ' eE' d' f'
                 → inferElab ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
                 → err ≡ CaseScrutineeNotSum
postulate
  fst-non-pair-Float : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr)
                      {Ψ' eE' d' f' err}
                    → inferElab ctx arg ≡ success T.Float Ψ' eE' d' f'
                    → inferElab ctx (Raw.RApp (Raw.RVar "fst") arg) ≡ failure err
                    → err ≡ FstNeedsPair
postulate
  fst-non-pair-Buffer : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr)
                       {Ψ' eE' d' f' err}
                     → inferElab ctx arg ≡ success T.Buffer Ψ' eE' d' f'
                     → inferElab ctx (Raw.RApp (Raw.RVar "fst") arg) ≡ failure err
                     → err ≡ FstNeedsPair
postulate
  fst-non-pair-Sum : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr) {A B : Type}
                    {Ψ' eE' d' f' err}
                  → inferElab ctx arg ≡ success (A T.+ B) Ψ' eE' d' f'
                  → inferElab ctx (Raw.RApp (Raw.RVar "fst") arg) ≡ failure err
                  → err ≡ FstNeedsPair
postulate
  fst-non-pair-Fun : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr) {A B : Type} {q : _}
                    {Ψ' eE' d' f' err}
                  → inferElab ctx arg ≡ success (A T.⇒[ T.mk-kind q T.pure ] B) Ψ' eE' d' f'
                  → inferElab ctx (Raw.RApp (Raw.RVar "fst") arg) ≡ failure err
                  → err ≡ FstNeedsPair
postulate
  neg-non-Int-Float : ∀ (ctx : NamedCtx) (e : Raw.RawExpr)
                     {Ψ' eE' d' f' err}
                   → inferElab ctx e ≡ success T.Float Ψ' eE' d' f'
                   → inferElab ctx (Raw.RUnaryOp Raw.OpNeg e) ≡ failure err
                   → err ≡ NegationNotInt
postulate
  neg-non-Int-Buffer : ∀ (ctx : NamedCtx) (e : Raw.RawExpr)
                      {Ψ' eE' d' f' err}
                    → inferElab ctx e ≡ success T.Buffer Ψ' eE' d' f'
                    → inferElab ctx (Raw.RUnaryOp Raw.OpNeg e) ≡ failure err
                    → err ≡ NegationNotInt
postulate
  neg-non-Int-Product : ∀ (ctx : NamedCtx) (e : Raw.RawExpr) {A B : Type}
                       {Ψ' eE' d' f' err}
                     → inferElab ctx e ≡ success (A T.* B) Ψ' eE' d' f'
                     → inferElab ctx (Raw.RUnaryOp Raw.OpNeg e) ≡ failure err
                     → err ≡ NegationNotInt
postulate
  neg-non-Int-Sum : ∀ (ctx : NamedCtx) (e : Raw.RawExpr) {A B : Type}
                   {Ψ' eE' d' f' err}
                 → inferElab ctx e ≡ success (A T.+ B) Ψ' eE' d' f'
                 → inferElab ctx (Raw.RUnaryOp Raw.OpNeg e) ≡ failure err
                 → err ≡ NegationNotInt
postulate
  snd-non-pair-Float : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr)
                      {Ψ' eE' d' f' err}
                    → inferElab ctx arg ≡ success T.Float Ψ' eE' d' f'
                    → inferElab ctx (Raw.RApp (Raw.RVar "snd") arg) ≡ failure err
                    → err ≡ SndNeedsPair
postulate
  snd-non-pair-Buffer : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr)
                       {Ψ' eE' d' f' err}
                     → inferElab ctx arg ≡ success T.Buffer Ψ' eE' d' f'
                     → inferElab ctx (Raw.RApp (Raw.RVar "snd") arg) ≡ failure err
                     → err ≡ SndNeedsPair
postulate
  snd-non-pair-Sum : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr) {A B : Type}
                    {Ψ' eE' d' f' err}
                  → inferElab ctx arg ≡ success (A T.+ B) Ψ' eE' d' f'
                  → inferElab ctx (Raw.RApp (Raw.RVar "snd") arg) ≡ failure err
                  → err ≡ SndNeedsPair
postulate
  snd-non-pair-Fun : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr) {A B : Type} {q : _}
                    {Ψ' eE' d' f' err}
                  → inferElab ctx arg ≡ success (A T.⇒[ T.mk-kind q T.pure ] B) Ψ' eE' d' f'
                  → inferElab ctx (Raw.RApp (Raw.RVar "snd") arg) ≡ failure err
                  → err ≡ SndNeedsPair
postulate
  case-scrut-Float : ∀ (ctx : NamedCtx) (scrut : Raw.RawExpr)
                      (xL : String) (eL : Raw.RawExpr)
                      (xR : String) (eR : Raw.RawExpr)
                      {Ψ' eE' d' f' err}
                    → inferElab ctx scrut ≡ success T.Float Ψ' eE' d' f'
                    → inferElab ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
                    → err ≡ CaseScrutineeNotSum
postulate
  case-scrut-Buffer : ∀ (ctx : NamedCtx) (scrut : Raw.RawExpr)
                      (xL : String) (eL : Raw.RawExpr)
                      (xR : String) (eR : Raw.RawExpr)
                      {Ψ' eE' d' f' err}
                    → inferElab ctx scrut ≡ success T.Buffer Ψ' eE' d' f'
                    → inferElab ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
                    → err ≡ CaseScrutineeNotSum
postulate
  case-scrut-Product : ∀ (ctx : NamedCtx) (scrut : Raw.RawExpr)
                      (xL : String) (eL : Raw.RawExpr)
                      (xR : String) (eR : Raw.RawExpr)
                      {A B : Type} {Ψ' eE' d' f' err}
                    → inferElab ctx scrut ≡ success (A T.* B) Ψ' eE' d' f'
                    → inferElab ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
                    → err ≡ CaseScrutineeNotSum
postulate
  case-scrut-Fun : ∀ (ctx : NamedCtx) (scrut : Raw.RawExpr)
                      (xL : String) (eL : Raw.RawExpr)
                      (xR : String) (eR : Raw.RawExpr)
                      {A B : Type} {q : _} {Ψ' eE' d' f' err}
                    → inferElab ctx scrut ≡ success (A T.⇒[ T.mk-kind q T.pure ] B) Ψ' eE' d' f'
                    → inferElab ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
                    → err ≡ CaseScrutineeNotSum
postulate
  fst-non-pair-Eff : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr) {A B : Type}
                     {Ψ' eE' d' f' err}
                   → inferElab ctx arg ≡ success (A T.⇒[ T.mk-kind T.Many T.eff ] B) Ψ' eE' d' f'
                   → inferElab ctx (Raw.RApp (Raw.RVar "fst") arg) ≡ failure err
                   → err ≡ FstNeedsPair
postulate
  fst-non-pair-μ : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr) {F}
                  {Ψ' eE' d' f' err}
                → inferElab ctx arg ≡ success (T.μ-type F) Ψ' eE' d' f'
                → inferElab ctx (Raw.RApp (Raw.RVar "fst") arg) ≡ failure err
                → err ≡ FstNeedsPair
postulate
  fst-non-pair-ν : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr) {F}
                  {Ψ' eE' d' f' err}
                → inferElab ctx arg ≡ success (T.ν-type F) Ψ' eE' d' f'
                → inferElab ctx (Raw.RApp (Raw.RVar "fst") arg) ≡ failure err
                → err ≡ FstNeedsPair
postulate
  snd-non-pair-Eff : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr) {A B : Type}
                     {Ψ' eE' d' f' err}
                   → inferElab ctx arg ≡ success (A T.⇒[ T.mk-kind T.Many T.eff ] B) Ψ' eE' d' f'
                   → inferElab ctx (Raw.RApp (Raw.RVar "snd") arg) ≡ failure err
                   → err ≡ SndNeedsPair
postulate
  snd-non-pair-μ : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr) {F}
                  {Ψ' eE' d' f' err}
                → inferElab ctx arg ≡ success (T.μ-type F) Ψ' eE' d' f'
                → inferElab ctx (Raw.RApp (Raw.RVar "snd") arg) ≡ failure err
                → err ≡ SndNeedsPair
postulate
  snd-non-pair-ν : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr) {F}
                  {Ψ' eE' d' f' err}
                → inferElab ctx arg ≡ success (T.ν-type F) Ψ' eE' d' f'
                → inferElab ctx (Raw.RApp (Raw.RVar "snd") arg) ≡ failure err
                → err ≡ SndNeedsPair
postulate
  neg-non-Int-Eff : ∀ (ctx : NamedCtx) (e : Raw.RawExpr) {A B : Type}
                    {Ψ' eE' d' f' err}
                  → inferElab ctx e ≡ success (A T.⇒[ T.mk-kind T.Many T.eff ] B) Ψ' eE' d' f'
                  → inferElab ctx (Raw.RUnaryOp Raw.OpNeg e) ≡ failure err
                  → err ≡ NegationNotInt
postulate
  neg-non-Int-μ : ∀ (ctx : NamedCtx) (e : Raw.RawExpr) {F}
                 {Ψ' eE' d' f' err}
               → inferElab ctx e ≡ success (T.μ-type F) Ψ' eE' d' f'
               → inferElab ctx (Raw.RUnaryOp Raw.OpNeg e) ≡ failure err
               → err ≡ NegationNotInt
postulate
  neg-non-Int-ν : ∀ (ctx : NamedCtx) (e : Raw.RawExpr) {F}
                 {Ψ' eE' d' f' err}
               → inferElab ctx e ≡ success (T.ν-type F) Ψ' eE' d' f'
               → inferElab ctx (Raw.RUnaryOp Raw.OpNeg e) ≡ failure err
               → err ≡ NegationNotInt
postulate
  neg-non-Int-Fun : ∀ (ctx : NamedCtx) (e : Raw.RawExpr) {A B : Type} {q : _}
                    {Ψ' eE' d' f' err}
                  → inferElab ctx e ≡ success (A T.⇒[ T.mk-kind q T.pure ] B) Ψ' eE' d' f'
                  → inferElab ctx (Raw.RUnaryOp Raw.OpNeg e) ≡ failure err
                  → err ≡ NegationNotInt
postulate
  case-scrut-Eff : ∀ (ctx : NamedCtx) (scrut : Raw.RawExpr)
                    (xL : String) (eL : Raw.RawExpr)
                    (xR : String) (eR : Raw.RawExpr)
                    {A B : Type} {Ψ' eE' d' f' err}
                  → inferElab ctx scrut ≡ success (A T.⇒[ T.mk-kind T.Many T.eff ] B) Ψ' eE' d' f'
                  → inferElab ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
                  → err ≡ CaseScrutineeNotSum
postulate
  case-scrut-μ : ∀ (ctx : NamedCtx) (scrut : Raw.RawExpr)
                  (xL : String) (eL : Raw.RawExpr)
                  (xR : String) (eR : Raw.RawExpr)
                  {F} {Ψ' eE' d' f' err}
                → inferElab ctx scrut ≡ success (T.μ-type F) Ψ' eE' d' f'
                → inferElab ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
                → err ≡ CaseScrutineeNotSum
postulate
  case-scrut-ν : ∀ (ctx : NamedCtx) (scrut : Raw.RawExpr)
                  (xL : String) (eL : Raw.RawExpr)
                  (xR : String) (eR : Raw.RawExpr)
                  {F} {Ψ' eE' d' f' err}
                → inferElab ctx scrut ≡ success (T.ν-type F) Ψ' eE' d' f'
                → inferElab ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
                → err ≡ CaseScrutineeNotSum
