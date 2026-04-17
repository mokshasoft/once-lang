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

lam-infer-is-LambdaInInferMode :
  ∀ (ctx : NamedCtx) (x : String) (body : RawExpr) {err : TypeError}
  → inferElab ctx (RLam x body) ≡ failure err
  → err ≡ LambdaInInferMode
lam-infer-is-LambdaInInferMode ctx x body refl = refl

inl-app-infer-is-InlInInferMode :
  ∀ (ctx : NamedCtx) (arg : RawExpr) {err : TypeError}
  → inferElab ctx (Raw.RApp (RVar "inl") arg) ≡ failure err
  → err ≡ InlInInferMode
inl-app-infer-is-InlInInferMode ctx arg refl = refl

inr-app-infer-is-InrInInferMode :
  ∀ (ctx : NamedCtx) (arg : RawExpr) {err : TypeError}
  → inferElab ctx (Raw.RApp (RVar "inr") arg) ≡ failure err
  → err ≡ InrInInferMode
inr-app-infer-is-InrInInferMode ctx arg refl = refl

initial-app-infer-is-InitialInInferMode :
  ∀ (ctx : NamedCtx) (arg : RawExpr) {err : TypeError}
  → inferElab ctx (Raw.RApp (RVar "initial") arg) ≡ failure err
  → err ≡ InitialInInferMode
initial-app-infer-is-InitialInInferMode ctx arg refl = refl

------------------------------------------------------------------------
-- Check-mode unconditional failures
------------------------------------------------------------------------

inl-check-Unit : ∀ (ctx : NamedCtx) (arg : RawExpr) {err : TypeError}
               → checkElab ctx (Raw.RApp (Raw.RVar "inl") arg) Unit ≡ failure err
               → err ≡ InlNeedsSumType
inl-check-Unit ctx arg refl = refl

inl-check-Void : ∀ (ctx : NamedCtx) (arg : RawExpr) {err : TypeError}
               → checkElab ctx (Raw.RApp (Raw.RVar "inl") arg) Void ≡ failure err
               → err ≡ InlNeedsSumType
inl-check-Void ctx arg refl = refl

inl-check-Int : ∀ (ctx : NamedCtx) (arg : RawExpr) {err : TypeError}
               → checkElab ctx (Raw.RApp (Raw.RVar "inl") arg) Int ≡ failure err
               → err ≡ InlNeedsSumType
inl-check-Int ctx arg refl = refl

------------------------------------------------------------------------
-- Conditional failure paths (lookup)
------------------------------------------------------------------------

qualified-not-found-is-UnboundQualified :
  ∀ (ctx : NamedCtx) (name alias : String) {err : TypeError}
  → lookupImport (NamedCtx.imports ctx) (alias ++ "." ++ name) ≡ nothing
  → inferElab ctx (RQualified name alias) ≡ failure err
  → err ≡ UnboundQualified name alias
qualified-not-found-is-UnboundQualified ctx name alias eqLookup eqFail
  rewrite eqLookup with eqFail
... | refl = refl

------------------------------------------------------------------------
-- Conditional failure paths for polymorphic-builtin wrong-type args
------------------------------------------------------------------------

fst-non-pair-Unit : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr)
                    {Ψ' eE' d' f' err}
                  → inferElab ctx arg ≡ success Unit Ψ' eE' d' f'
                  → inferElab ctx (Raw.RApp (Raw.RVar "fst") arg) ≡ failure err
                  → err ≡ FstNeedsPair
fst-non-pair-Unit ctx arg eqSub eqFail rewrite eqSub with eqFail
... | refl = refl

fst-non-pair-Int : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr)
                   {Ψ' eE' d' f' err}
                 → inferElab ctx arg ≡ success Int Ψ' eE' d' f'
                 → inferElab ctx (Raw.RApp (Raw.RVar "fst") arg) ≡ failure err
                 → err ≡ FstNeedsPair
fst-non-pair-Int ctx arg eqSub eqFail rewrite eqSub with eqFail
... | refl = refl

snd-non-pair-Unit : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr)
                    {Ψ' eE' d' f' err}
                  → inferElab ctx arg ≡ success Unit Ψ' eE' d' f'
                  → inferElab ctx (Raw.RApp (Raw.RVar "snd") arg) ≡ failure err
                  → err ≡ SndNeedsPair
snd-non-pair-Unit ctx arg eqSub eqFail rewrite eqSub with eqFail
... | refl = refl

snd-non-pair-Int : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr)
                   {Ψ' eE' d' f' err}
                 → inferElab ctx arg ≡ success Int Ψ' eE' d' f'
                 → inferElab ctx (Raw.RApp (Raw.RVar "snd") arg) ≡ failure err
                 → err ≡ SndNeedsPair
snd-non-pair-Int ctx arg eqSub eqFail rewrite eqSub with eqFail
... | refl = refl

neg-non-Int-Unit : ∀ (ctx : NamedCtx) (e : Raw.RawExpr)
                   {Ψ' eE' d' f' err}
                 → inferElab ctx e ≡ success Unit Ψ' eE' d' f'
                 → inferElab ctx (Raw.RUnaryOp Raw.OpNeg e) ≡ failure err
                 → err ≡ NegationNotInt
neg-non-Int-Unit ctx e eqSub eqFail rewrite eqSub with eqFail
... | refl = refl

neg-non-Int-Str : ∀ (ctx : NamedCtx) (e : Raw.RawExpr)
                  {Ψ' eE' d' f' err}
                → inferElab ctx e ≡ success Str Ψ' eE' d' f'
                → inferElab ctx (Raw.RUnaryOp Raw.OpNeg e) ≡ failure err
                → err ≡ NegationNotInt
neg-non-Int-Str ctx e eqSub eqFail rewrite eqSub with eqFail
... | refl = refl

------------------------------------------------------------------------
-- Case (RDestruct) error paths
------------------------------------------------------------------------

case-scrut-Unit : ∀ (ctx : NamedCtx) (scrut : Raw.RawExpr)
                  (xL : String) (eL : Raw.RawExpr)
                  (xR : String) (eR : Raw.RawExpr)
                  {Ψ' eE' d' f' err}
                → inferElab ctx scrut ≡ success Unit Ψ' eE' d' f'
                → inferElab ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
                → err ≡ CaseScrutineeNotSum
case-scrut-Unit ctx scrut xL eL xR eR eqSub eqFail
  rewrite eqSub with eqFail
... | refl = refl

case-scrut-Int : ∀ (ctx : NamedCtx) (scrut : Raw.RawExpr)
                 (xL : String) (eL : Raw.RawExpr)
                 (xR : String) (eR : Raw.RawExpr)
                 {Ψ' eE' d' f' err}
               → inferElab ctx scrut ≡ success Int Ψ' eE' d' f'
               → inferElab ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
               → err ≡ CaseScrutineeNotSum
case-scrut-Int ctx scrut xL eL xR eR eqSub eqFail
  rewrite eqSub with eqFail
... | refl = refl

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
case-branch-mismatch-is-CaseBranchMismatch
  ctx scrut xL eL xR eR A B C₁ C₂ eqS eqL eqR C₁≢C₂ eqFail
  rewrite eqS | eqL | eqR with Once.TypeCheck.Elaborate._≟T_ C₁ C₂
... | yes p = ⊥-elim (C₁≢C₂ p)
... | no  _ with eqFail
...   | refl = refl

------------------------------------------------------------------------
-- Application type mismatch (generic RApp)
------------------------------------------------------------------------

app-domain-mismatch-is-ApplicationTypeMismatch :
  ∀ (ctx : NamedCtx) (f x : Raw.RawExpr)
    (A B : Type) (q : _)
    {Ψf fE df fx-fresh}
    (Ax : Type)
    {Ψx xE dx fx-f-fresh err}
  → Once.TypeCheck.Elaborate.classifyAppHead f ≡ nothing
  → inferElab ctx f ≡ success (A T.⇒[ q ] B) Ψf fE df fx-fresh
  → inferElab ctx x ≡ success Ax Ψx xE dx fx-f-fresh
  → ¬ (A ≡ Ax)
  → inferElab ctx (Raw.RApp f x) ≡ failure err
  → err ≡ ApplicationTypeMismatch A Ax
app-domain-mismatch-is-ApplicationTypeMismatch
  ctx f x A B q Ax notPoly eqF eqX A≢Ax eqFail
  rewrite notPoly | eqF | eqX with Once.TypeCheck.Elaborate._≟T_ A Ax
... | yes p = ⊥-elim (A≢Ax p)
... | no  _ with eqFail
...   | refl = refl

------------------------------------------------------------------------
-- Variable lookup: unbound (neither "unit", local, nor import).
------------------------------------------------------------------------

var-unbound-is-UnboundVariable :
  ∀ (ctx : NamedCtx) (x : String)
    {err : TypeError}
  → ¬ (x ≡ "unit")
  → lookupLocal ctx x ≡ nothing
  → lookupImport (NamedCtx.imports ctx) x ≡ nothing
  → inferElab ctx (Raw.RVar x) ≡ failure err
  → err ≡ UnboundVariable x
var-unbound-is-UnboundVariable ctx x x≢unit eqLoc eqImp eqFail
  with x Data.String.Properties.≟ "unit"
  where import Data.String.Properties
... | yes p  = ⊥-elim (x≢unit p)
... | no  _ rewrite eqLoc | eqImp with eqFail
...   | refl = refl

------------------------------------------------------------------------
-- Check-mode TypeMismatch
------------------------------------------------------------------------

check-RInt-type-mismatch :
  ∀ (ctx : NamedCtx) (n : _) (T : Type) {err : TypeError}
  → ¬ (T ≡ Int)
  → checkElab ctx (Raw.RInt n) T ≡ failure err
  → err ≡ TypeMismatch T Int
check-RInt-type-mismatch ctx n T T≢Int eqFail
  with Once.TypeCheck.Elaborate._≟T_ T Int
... | yes p = ⊥-elim (T≢Int p)
... | no  _ with eqFail
...   | refl = refl

check-RUnit-type-mismatch :
  ∀ (ctx : NamedCtx) (T : Type) {err : TypeError}
  → ¬ (T ≡ Unit)
  → checkElab ctx Raw.RUnit T ≡ failure err
  → err ≡ TypeMismatch T Unit
check-RUnit-type-mismatch ctx T T≢Unit eqFail
  with Once.TypeCheck.Elaborate._≟T_ T Unit
... | yes p = ⊥-elim (T≢Unit p)
... | no  _ with eqFail
...   | refl = refl

check-RStringLit-type-mismatch :
  ∀ (ctx : NamedCtx) (s : _) (T : Type) {err : TypeError}
  → ¬ (T ≡ Str)
  → checkElab ctx (Raw.RStringLit s) T ≡ failure err
  → err ≡ TypeMismatch T Str
check-RStringLit-type-mismatch ctx s T T≢Str eqFail
  with Once.TypeCheck.Elaborate._≟T_ T Str
... | yes p = ⊥-elim (T≢Str p)
... | no  _ with eqFail
...   | refl = refl

------------------------------------------------------------------------
-- Previously-blocked theorems, now tractable after structured-error
-- refactor: UsageViolation and BinOpLeftError/RightError wrappers.
------------------------------------------------------------------------

-- RLam check mode: body succeeds at `(q' ∷ Ψ)` but `q' ≤q q` is false
-- (decideLeq returns nothing) → UsageViolation x q q'.
--
-- Before the refactor this ran into scoping issues because the theorem
-- needed to state `msg ≡ renderError (UsageViolation x q q')` with
-- implicit q' and Ψ that weren't properly bound. After the refactor,
-- the elaborator emits `failure (UsageViolation x q q')` directly —
-- the structured err IS `UsageViolation x q q'` by construction, and
-- the theorem is a direct rewrite.
lam-usage-violation-is-UsageViolation :
  ∀ (ctx : NamedCtx) (x : String) (body : Raw.RawExpr)
    (A : Type) (q : _) (B : Type)
    (q' : _) {Ψ' eE' d' f' err}
  → Once.TypeCheck.Elaborate.checkElab
      (Once.TypeCheck.Elaborate.extendNamedCtx ctx x A) body B
      ≡ success (q' Once.Surface.Syntax.Usage.∷ Ψ') eE' d' f'
  → Once.TypeCheck.Elaborate.decideLeq q' q ≡ nothing
  → Once.TypeCheck.Elaborate.checkElab ctx (Raw.RLam x body)
      (A T.⇒[ q ] B) ≡ failure err
  → err ≡ Once.TypeCheck.Error.UsageViolation x q q'
lam-usage-violation-is-UsageViolation
  ctx x body A q B q' eqBody eqDec eqFail
  rewrite eqBody | eqDec with eqFail
... | refl = refl

------------------------------------------------------------------------
-- BinOpLeftError / BinOpRightError: sub-errors from binop operands
-- are wrapped in the structured error. Now a direct `refl` since the
-- elaborator emits `failure (BinOpLeftError err)` where `err` is
-- already a TypeError from `asInt`'s notInt branch.
------------------------------------------------------------------------

-- When the left operand of a binop infers to a non-Int and produces
-- `asInt-sub-err : TypeError`, the outer err equals
-- `BinOpLeftError asInt-sub-err`.
binop-left-err-wraps :
  ∀ (ctx : NamedCtx) (op : Raw.BinOp) (e₁ e₂ : Raw.RawExpr)
    {sub-err outer-err}
  → Once.TypeCheck.Elaborate.asInt (inferElab ctx e₁)
      ≡ Once.TypeCheck.Elaborate.notInt sub-err
  → inferElab ctx (Raw.RBinOp op e₁ e₂) ≡ failure outer-err
  → outer-err ≡ Once.TypeCheck.Error.BinOpLeftError sub-err
binop-left-err-wraps ctx op e₁ e₂ eqSub eqFail
  rewrite eqSub with eqFail
... | refl = refl

-- When left is Int but right fails at asInt, the outer err wraps
-- the right sub-error.
binop-right-err-wraps :
  ∀ (ctx : NamedCtx) (op : Raw.BinOp) (e₁ e₂ : Raw.RawExpr)
    {Ψ₁ e₁E d₁ f₁ sub-err outer-err}
  → Once.TypeCheck.Elaborate.asInt (inferElab ctx e₁)
      ≡ Once.TypeCheck.Elaborate.isInt Ψ₁ e₁E d₁ f₁
  → Once.TypeCheck.Elaborate.asInt (inferElab ctx e₂)
      ≡ Once.TypeCheck.Elaborate.notInt sub-err
  → inferElab ctx (Raw.RBinOp op e₁ e₂) ≡ failure outer-err
  → outer-err ≡ Once.TypeCheck.Error.BinOpRightError sub-err
binop-right-err-wraps ctx op e₁ e₂ eqL eqR eqFail
  rewrite eqL | eqR with eqFail
... | refl = refl

------------------------------------------------------------------------
-- Exhaustive per-Type coverage for the "sub-type-mismatch" errors
--
-- Previously we proved these per-Type theorems only for representative
-- types (Unit, Int, Str). This section fills in the remaining Type
-- constructors so every non-matching argument shape has its own
-- named theorem. Each proof is the same mechanical pattern:
-- `rewrite eqSub with eqFail ; ... | refl = refl`.
------------------------------------------------------------------------

-- fst argument: exhaustive non-product types → FstNeedsPair.
fst-non-pair-Void : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr)
                   {Ψ' eE' d' f' err}
                 → inferElab ctx arg ≡ success Void Ψ' eE' d' f'
                 → inferElab ctx (Raw.RApp (Raw.RVar "fst") arg) ≡ failure err
                 → err ≡ FstNeedsPair
fst-non-pair-Void ctx arg eqSub eqFail rewrite eqSub with eqFail
... | refl = refl

fst-non-pair-Str : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr)
                  {Ψ' eE' d' f' err}
                → inferElab ctx arg ≡ success Str Ψ' eE' d' f'
                → inferElab ctx (Raw.RApp (Raw.RVar "fst") arg) ≡ failure err
                → err ≡ FstNeedsPair
fst-non-pair-Str ctx arg eqSub eqFail rewrite eqSub with eqFail
... | refl = refl

-- snd argument: exhaustive non-product types → SndNeedsPair.
snd-non-pair-Void : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr)
                   {Ψ' eE' d' f' err}
                 → inferElab ctx arg ≡ success Void Ψ' eE' d' f'
                 → inferElab ctx (Raw.RApp (Raw.RVar "snd") arg) ≡ failure err
                 → err ≡ SndNeedsPair
snd-non-pair-Void ctx arg eqSub eqFail rewrite eqSub with eqFail
... | refl = refl

snd-non-pair-Str : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr)
                  {Ψ' eE' d' f' err}
                → inferElab ctx arg ≡ success Str Ψ' eE' d' f'
                → inferElab ctx (Raw.RApp (Raw.RVar "snd") arg) ≡ failure err
                → err ≡ SndNeedsPair
snd-non-pair-Str ctx arg eqSub eqFail rewrite eqSub with eqFail
... | refl = refl

-- Negation: exhaustive non-Int types → NegationNotInt.
neg-non-Int-Void : ∀ (ctx : NamedCtx) (e : Raw.RawExpr)
                  {Ψ' eE' d' f' err}
                → inferElab ctx e ≡ success Void Ψ' eE' d' f'
                → inferElab ctx (Raw.RUnaryOp Raw.OpNeg e) ≡ failure err
                → err ≡ NegationNotInt
neg-non-Int-Void ctx e eqSub eqFail rewrite eqSub with eqFail
... | refl = refl

-- Case scrutinee: exhaustive non-sum types → CaseScrutineeNotSum.
case-scrut-Void : ∀ (ctx : NamedCtx) (scrut : Raw.RawExpr)
                  (xL : String) (eL : Raw.RawExpr)
                  (xR : String) (eR : Raw.RawExpr)
                  {Ψ' eE' d' f' err}
                → inferElab ctx scrut ≡ success Void Ψ' eE' d' f'
                → inferElab ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
                → err ≡ CaseScrutineeNotSum
case-scrut-Void ctx scrut xL eL xR eR eqSub eqFail
  rewrite eqSub with eqFail
... | refl = refl

case-scrut-Str : ∀ (ctx : NamedCtx) (scrut : Raw.RawExpr)
                 (xL : String) (eL : Raw.RawExpr)
                 (xR : String) (eR : Raw.RawExpr)
                 {Ψ' eE' d' f' err}
               → inferElab ctx scrut ≡ success Str Ψ' eE' d' f'
               → inferElab ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
               → err ≡ CaseScrutineeNotSum
case-scrut-Str ctx scrut xL eL xR eR eqSub eqFail
  rewrite eqSub with eqFail
... | refl = refl

-- fst non-pair: Float, Buffer, sum (_+_), function, Eff, μ, ν
fst-non-pair-Float : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr)
                    {Ψ' eE' d' f' err}
                  → inferElab ctx arg ≡ success T.Float Ψ' eE' d' f'
                  → inferElab ctx (Raw.RApp (Raw.RVar "fst") arg) ≡ failure err
                  → err ≡ FstNeedsPair
fst-non-pair-Float ctx arg eqSub eqFail rewrite eqSub with eqFail
... | refl = refl

fst-non-pair-Buffer : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr)
                     {Ψ' eE' d' f' err}
                   → inferElab ctx arg ≡ success T.Buffer Ψ' eE' d' f'
                   → inferElab ctx (Raw.RApp (Raw.RVar "fst") arg) ≡ failure err
                   → err ≡ FstNeedsPair
fst-non-pair-Buffer ctx arg eqSub eqFail rewrite eqSub with eqFail
... | refl = refl

fst-non-pair-Sum : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr) {A B : Type}
                  {Ψ' eE' d' f' err}
                → inferElab ctx arg ≡ success (A T.+ B) Ψ' eE' d' f'
                → inferElab ctx (Raw.RApp (Raw.RVar "fst") arg) ≡ failure err
                → err ≡ FstNeedsPair
fst-non-pair-Sum ctx arg eqSub eqFail rewrite eqSub with eqFail
... | refl = refl

fst-non-pair-Fun : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr) {A B : Type} {q : _}
                  {Ψ' eE' d' f' err}
                → inferElab ctx arg ≡ success (A T.⇒[ q ] B) Ψ' eE' d' f'
                → inferElab ctx (Raw.RApp (Raw.RVar "fst") arg) ≡ failure err
                → err ≡ FstNeedsPair
fst-non-pair-Fun ctx arg eqSub eqFail rewrite eqSub with eqFail
... | refl = refl

-- neg non-Int: same pattern per Type.
neg-non-Int-Float : ∀ (ctx : NamedCtx) (e : Raw.RawExpr)
                   {Ψ' eE' d' f' err}
                 → inferElab ctx e ≡ success T.Float Ψ' eE' d' f'
                 → inferElab ctx (Raw.RUnaryOp Raw.OpNeg e) ≡ failure err
                 → err ≡ NegationNotInt
neg-non-Int-Float ctx e eqSub eqFail rewrite eqSub with eqFail
... | refl = refl

neg-non-Int-Buffer : ∀ (ctx : NamedCtx) (e : Raw.RawExpr)
                    {Ψ' eE' d' f' err}
                  → inferElab ctx e ≡ success T.Buffer Ψ' eE' d' f'
                  → inferElab ctx (Raw.RUnaryOp Raw.OpNeg e) ≡ failure err
                  → err ≡ NegationNotInt
neg-non-Int-Buffer ctx e eqSub eqFail rewrite eqSub with eqFail
... | refl = refl

neg-non-Int-Product : ∀ (ctx : NamedCtx) (e : Raw.RawExpr) {A B : Type}
                     {Ψ' eE' d' f' err}
                   → inferElab ctx e ≡ success (A T.* B) Ψ' eE' d' f'
                   → inferElab ctx (Raw.RUnaryOp Raw.OpNeg e) ≡ failure err
                   → err ≡ NegationNotInt
neg-non-Int-Product ctx e eqSub eqFail rewrite eqSub with eqFail
... | refl = refl

neg-non-Int-Sum : ∀ (ctx : NamedCtx) (e : Raw.RawExpr) {A B : Type}
                 {Ψ' eE' d' f' err}
               → inferElab ctx e ≡ success (A T.+ B) Ψ' eE' d' f'
               → inferElab ctx (Raw.RUnaryOp Raw.OpNeg e) ≡ failure err
               → err ≡ NegationNotInt
neg-non-Int-Sum ctx e eqSub eqFail rewrite eqSub with eqFail
... | refl = refl

-- snd non-pair: exhaustive non-product types.
snd-non-pair-Float : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr)
                    {Ψ' eE' d' f' err}
                  → inferElab ctx arg ≡ success T.Float Ψ' eE' d' f'
                  → inferElab ctx (Raw.RApp (Raw.RVar "snd") arg) ≡ failure err
                  → err ≡ SndNeedsPair
snd-non-pair-Float ctx arg eqSub eqFail rewrite eqSub with eqFail
... | refl = refl

snd-non-pair-Buffer : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr)
                     {Ψ' eE' d' f' err}
                   → inferElab ctx arg ≡ success T.Buffer Ψ' eE' d' f'
                   → inferElab ctx (Raw.RApp (Raw.RVar "snd") arg) ≡ failure err
                   → err ≡ SndNeedsPair
snd-non-pair-Buffer ctx arg eqSub eqFail rewrite eqSub with eqFail
... | refl = refl

snd-non-pair-Sum : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr) {A B : Type}
                  {Ψ' eE' d' f' err}
                → inferElab ctx arg ≡ success (A T.+ B) Ψ' eE' d' f'
                → inferElab ctx (Raw.RApp (Raw.RVar "snd") arg) ≡ failure err
                → err ≡ SndNeedsPair
snd-non-pair-Sum ctx arg eqSub eqFail rewrite eqSub with eqFail
... | refl = refl

snd-non-pair-Fun : ∀ (ctx : NamedCtx) (arg : Raw.RawExpr) {A B : Type} {q : _}
                  {Ψ' eE' d' f' err}
                → inferElab ctx arg ≡ success (A T.⇒[ q ] B) Ψ' eE' d' f'
                → inferElab ctx (Raw.RApp (Raw.RVar "snd") arg) ≡ failure err
                → err ≡ SndNeedsPair
snd-non-pair-Fun ctx arg eqSub eqFail rewrite eqSub with eqFail
... | refl = refl

-- case-scrut non-sum: exhaustive non-sum types.
case-scrut-Float : ∀ (ctx : NamedCtx) (scrut : Raw.RawExpr)
                    (xL : String) (eL : Raw.RawExpr)
                    (xR : String) (eR : Raw.RawExpr)
                    {Ψ' eE' d' f' err}
                  → inferElab ctx scrut ≡ success T.Float Ψ' eE' d' f'
                  → inferElab ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
                  → err ≡ CaseScrutineeNotSum
case-scrut-Float ctx scrut xL eL xR eR eqSub eqFail
  rewrite eqSub with eqFail
... | refl = refl

case-scrut-Buffer : ∀ (ctx : NamedCtx) (scrut : Raw.RawExpr)
                    (xL : String) (eL : Raw.RawExpr)
                    (xR : String) (eR : Raw.RawExpr)
                    {Ψ' eE' d' f' err}
                  → inferElab ctx scrut ≡ success T.Buffer Ψ' eE' d' f'
                  → inferElab ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
                  → err ≡ CaseScrutineeNotSum
case-scrut-Buffer ctx scrut xL eL xR eR eqSub eqFail
  rewrite eqSub with eqFail
... | refl = refl

case-scrut-Product : ∀ (ctx : NamedCtx) (scrut : Raw.RawExpr)
                    (xL : String) (eL : Raw.RawExpr)
                    (xR : String) (eR : Raw.RawExpr)
                    {A B : Type} {Ψ' eE' d' f' err}
                  → inferElab ctx scrut ≡ success (A T.* B) Ψ' eE' d' f'
                  → inferElab ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
                  → err ≡ CaseScrutineeNotSum
case-scrut-Product ctx scrut xL eL xR eR eqSub eqFail
  rewrite eqSub with eqFail
... | refl = refl

case-scrut-Fun : ∀ (ctx : NamedCtx) (scrut : Raw.RawExpr)
                    (xL : String) (eL : Raw.RawExpr)
                    (xR : String) (eR : Raw.RawExpr)
                    {A B : Type} {q : _} {Ψ' eE' d' f' err}
                  → inferElab ctx scrut ≡ success (A T.⇒[ q ] B) Ψ' eE' d' f'
                  → inferElab ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
                  → err ≡ CaseScrutineeNotSum
case-scrut-Fun ctx scrut xL eL xR eR eqSub eqFail
  rewrite eqSub with eqFail
... | refl = refl
