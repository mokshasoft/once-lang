-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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

import Once.Spec.Context as SCx
import Once.Internal.Context as Surface

open import Once.Spec.Type using (var; Ty; Fun)
open import Data.String using (String; _++_)
open import Data.String.Properties as StrProp using ()
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Once.Spec.Type using (Type; Unit; Void; Int)
open import Once.Spec.Name using (gen)
import Once.Spec.Grade as T
import Once.Internal.Type as T
import Once.Spec.Type as T
import Once.Spec.Type as T
import Once.Internal.Type.Poly as T
import Once.Type as T
open import Once.Internal.Syntax as Raw using (RawExpr; RLam; RQualified)
open import Once.Internal.Type.DecEq using (_≟T_)
open import Once.Internal.Type.Join using (UB; join?-apart)
open import Once.Spec.Sub using (sub-int; sub-unit)
open import Once.Type.Sub using (_<:?_)
open import Once.TypeCheck.Elaborate
  using (inferElab; checkElab; InferElabResult; VerifiedInferResult; success; failure; inferElabV; checkElabV; inferElabV-RNeg-aux; inferElabV-neg-aux; inferFstOn; inferSndOn; inferElabV-RDestruct-aux; NegOperandView; nov-int; nov-float; nov-other; negOperandView; inferElabV-RVar-poly-lookup-aux; inferElabV-RVar-poly-ground-aux)
open import Once.Internal.Typing.Scope using (NamedCtx; lookupImport; lookupLocal)
open import Once.TypeCheck.Classify using (lookupPoly)
import Once.Internal.Typing.Scope as Classify
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Once.TypeCheck.Error
  using (TypeError; LambdaInInferMode; InlInInferMode; InrInInferMode; InitialInInferMode; InlNeedsSumType; FstNeedsPair; SndNeedsPair; CaseScrutineeNotSum; CaseBranchMismatch; TypeMismatch; UnboundVariable; UnboundQualified)
import Once.Internal.Context

------------------------------------------------------------------------
-- Unconditional-failure paths (now trivial after refactor)
------------------------------------------------------------------------

lam-infer-is-LambdaInInferMode : ∀ {m} (ctx : NamedCtx m) (x : String) (body : RawExpr) {err : TypeError}
  → inferElab ctx (RLam x body) ≡ failure err
  → err ≡ LambdaInInferMode
lam-infer-is-LambdaInInferMode ctx x body refl = refl

inl-app-infer-is-InlInInferMode : ∀ {m} (ctx : NamedCtx m) (arg : RawExpr) {err : TypeError}
  → inferElab ctx (Raw.RApp (Raw.RResolved (gen "inl")) arg) ≡ failure err
  → err ≡ InlInInferMode
inl-app-infer-is-InlInInferMode ctx arg refl = refl

inr-app-infer-is-InrInInferMode : ∀ {m} (ctx : NamedCtx m) (arg : RawExpr) {err : TypeError}
  → inferElab ctx (Raw.RApp (Raw.RResolved (gen "inr")) arg) ≡ failure err
  → err ≡ InrInInferMode
inr-app-infer-is-InrInInferMode ctx arg refl = refl

initial-app-infer-is-InitialInInferMode : ∀ {m} (ctx : NamedCtx m) (arg : RawExpr) {err : TypeError}
  → inferElab ctx (Raw.RApp (Raw.RResolved (gen "initial")) arg) ≡ failure err
  → err ≡ InitialInInferMode
initial-app-infer-is-InitialInInferMode ctx arg refl = refl
inl-check-Unit : ∀ {m} (ctx : NamedCtx m) (arg : RawExpr) {err : TypeError}
               → checkElab ctx (Raw.RApp (Raw.RResolved (gen "inl")) arg) Unit ≡ failure err
               → err ≡ InlNeedsSumType
inl-check-Unit ctx arg refl = refl

inl-check-Void : ∀ {m} (ctx : NamedCtx m) (arg : RawExpr) {err : TypeError}
               → checkElab ctx (Raw.RApp (Raw.RResolved (gen "inl")) arg) Void ≡ failure err
               → err ≡ InlNeedsSumType
inl-check-Void ctx arg refl = refl

------------------------------------------------------------------------
-- The families below are stated at `inferElab`, but proved over the
-- operand's RESULT: the elaborator's rule is a function of that result
-- (`inferFstOn`, `inferSndOn`, `inferElabV-RDestruct-aux`,
-- `inferElabV-RNeg-aux`), so matching it is enough — no `with` that
-- abstracts the operand's inference out of the whole elaborated goal
-- (≈3 s per lemma, 117 s for the module).
------------------------------------------------------------------------

private
  fail-inj : ∀ {m} {ctx : NamedCtx m} {a b : TypeError}
           → _≡_ {A = InferElabResult (Classify.NamedCtx.debruijn ctx)} (failure a) (failure b) → b ≡ a
  fail-inj refl = refl

  -- `rule` at a result whose type the rule rejects with `e₀`.
  rejects : ∀ {m} {ctx : NamedCtx m} {x y : RawExpr} (rule : VerifiedInferResult ctx x → VerifiedInferResult ctx y)
            (r : VerifiedInferResult ctx x) {T : Ty m} {Ψ' eE' d' f'} {e₀ err : TypeError}
          → proj₁ r ≡ success T Ψ' eE' d' f'
          → (∀ {w} → proj₁ (rule (success T Ψ' eE' d' f' , w)) ≡ failure e₀)
          → proj₁ (rule r) ≡ failure err
          → err ≡ e₀
  rejects {ctx = ctx} rule (success _ _ _ _ _ , w) refl fact eq = fail-inj {ctx = ctx} (trans (sym (fact {w})) eq)

  -- `-e`: a literal operand folds (the outer equation is `success ≡ failure`);
  -- any other operand goes through `inferElabV-RNeg-aux` at its result.
  neg-rejects : ∀ {m} {ctx : NamedCtx m} (e : RawExpr) (v : NegOperandView e) {T : Ty m} {Ψ' eE' d' f'} {e₀ err : TypeError}
              → proj₁ (inferElabV ctx e) ≡ success T Ψ' eE' d' f'
              → (∀ {w} → proj₁ (inferElabV-RNeg-aux ctx e (success T Ψ' eE' d' f' , w)) ≡ failure e₀)
              → proj₁ (inferElabV-neg-aux ctx e v) ≡ failure err
              → err ≡ e₀
  neg-rejects .(Raw.RInt n) (nov-int n) _ _ ()
  neg-rejects .(Raw.RFloat i f l) (nov-float i f l) _ _ ()
  neg-rejects {ctx = ctx} e (nov-other .e) eqI fact eqO = rejects (inferElabV-RNeg-aux ctx e) (inferElabV ctx e) eqI fact eqO

inl-check-Int : ∀ {m} (ctx : NamedCtx m) (arg : RawExpr) {err : TypeError}
               → checkElab ctx (Raw.RApp (Raw.RResolved (gen "inl")) arg) Int ≡ failure err
               → err ≡ InlNeedsSumType
inl-check-Int ctx arg refl = refl
-- The resolver reads every `name@alias`, so an unresolved one is unbound.
qualified-not-found-is-UnboundQualified : ∀ {m} (ctx : NamedCtx m) (name alias : String) {err : TypeError}
  → inferElab ctx (RQualified name alias) ≡ failure err
  → err ≡ UnboundQualified name alias
qualified-not-found-is-UnboundQualified ctx name alias refl = refl
fst-non-pair-Unit : ∀ {m} (ctx : NamedCtx m) (arg : Raw.RawExpr)
                      {Ψ' eE' d' f' err}
                    → inferElab ctx arg ≡ success Unit Ψ' eE' d' f'
                    → inferElab ctx (Raw.RApp (Raw.RResolved (gen "fst")) arg) ≡ failure err
                    → err ≡ FstNeedsPair
fst-non-pair-Unit ctx arg eqInner eqOuter = rejects (inferFstOn ctx arg) (inferElabV ctx arg) eqInner refl eqOuter
fst-non-pair-Int : ∀ {m} (ctx : NamedCtx m) (arg : Raw.RawExpr)
                     {Ψ' eE' d' f' err}
                   → inferElab ctx arg ≡ success Int Ψ' eE' d' f'
                   → inferElab ctx (Raw.RApp (Raw.RResolved (gen "fst")) arg) ≡ failure err
                   → err ≡ FstNeedsPair
fst-non-pair-Int ctx arg eqInner eqOuter = rejects (inferFstOn ctx arg) (inferElabV ctx arg) eqInner refl eqOuter
snd-non-pair-Unit : ∀ {m} (ctx : NamedCtx m) (arg : Raw.RawExpr)
                      {Ψ' eE' d' f' err}
                    → inferElab ctx arg ≡ success Unit Ψ' eE' d' f'
                    → inferElab ctx (Raw.RApp (Raw.RResolved (gen "snd")) arg) ≡ failure err
                    → err ≡ SndNeedsPair
snd-non-pair-Unit ctx arg eqInner eqOuter = rejects (inferSndOn ctx arg) (inferElabV ctx arg) eqInner refl eqOuter
snd-non-pair-Int : ∀ {m} (ctx : NamedCtx m) (arg : Raw.RawExpr)
                     {Ψ' eE' d' f' err}
                   → inferElab ctx arg ≡ success Int Ψ' eE' d' f'
                   → inferElab ctx (Raw.RApp (Raw.RResolved (gen "snd")) arg) ≡ failure err
                   → err ≡ SndNeedsPair
snd-non-pair-Int ctx arg eqInner eqOuter = rejects (inferSndOn ctx arg) (inferElabV ctx arg) eqInner refl eqOuter
neg-non-Int-Unit : ∀ {m} (ctx : NamedCtx m) (e : Raw.RawExpr)
                     {Ψ' eE' d' f' err}
                   → inferElab ctx e ≡ success Unit Ψ' eE' d' f'
                   → inferElab ctx (Raw.RNeg e) ≡ failure err
                   → err ≡ TypeMismatch {0} Int Unit
neg-non-Int-Unit ctx e eqInner eqOuter = neg-rejects e (negOperandView e) eqInner refl eqOuter

case-scrut-Unit : ∀ {m} (ctx : NamedCtx m) (scrut : Raw.RawExpr)
                    (xL : String) (eL : Raw.RawExpr)
                    (xR : String) (eR : Raw.RawExpr)
                    {Ψ' eE' d' f' err}
                  → inferElab ctx scrut ≡ success Unit Ψ' eE' d' f'
                  → inferElab ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
                  → err ≡ CaseScrutineeNotSum
case-scrut-Unit ctx scrut xL eL xR eR eqInner eqOuter =
  rejects (inferElabV-RDestruct-aux ctx scrut xL eL xR eR) (inferElabV ctx scrut) eqInner refl eqOuter
case-scrut-Int : ∀ {m} (ctx : NamedCtx m) (scrut : Raw.RawExpr)
                   (xL : String) (eL : Raw.RawExpr)
                   (xR : String) (eR : Raw.RawExpr)
                   {Ψ' eE' d' f' err}
                 → inferElab ctx scrut ≡ success Int Ψ' eE' d' f'
                 → inferElab ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
                 → err ≡ CaseScrutineeNotSum
case-scrut-Int ctx scrut xL eL xR eR eqInner eqOuter =
  rejects (inferElabV-RDestruct-aux ctx scrut xL eL xR eR) (inferElabV ctx scrut) eqInner refl eqOuter
case-branch-mismatch-is-CaseBranchMismatch : ∀ {m} (ctx : NamedCtx m) (scrut : Raw.RawExpr)
    (xL : String) (eL : Raw.RawExpr)
    (xR : String) (eR : Raw.RawExpr)
    (A B : Ty m)
    {Ψs scrutE ds fs}
    (C₁ C₂ : Ty m) {qℓ qr}
    {Ψₗ eLE dL fL Ψᵣ eRE dR fR err}
  → inferElab ctx scrut ≡ success (A T.+ B) Ψs scrutE ds fs
  → inferElab (Classify.extendNamedCtx ctx xL A) eL
      ≡ success C₁ (qℓ SCx.∷ Ψₗ) eLE dL fL
  → inferElab (Classify.extendNamedCtx ctx xR B) eR
      ≡ success C₂ (qr SCx.∷ Ψᵣ) eRE dR fR
  → ¬ UB C₁ C₂
  → inferElab ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
  → err ≡ CaseBranchMismatch
case-branch-mismatch-is-CaseBranchMismatch ctx scrut xL eL xR eR A B C₁ C₂ eqS eqL eqR ¬eq eqOuter
  with inferElabV ctx scrut | eqS
... | success (_ T.+ _) _ _ _ _ , _ | refl
    with inferElabV (Classify.extendNamedCtx ctx xL A) eL | eqL
...   | success _ (_ SCx.∷ _) _ _ _ , _ | refl
      with inferElabV (Classify.extendNamedCtx ctx xR B) eR | eqR
...     | success _ (_ SCx.∷ _) _ _ _ , _ | refl =
  -- D322: branches with no upper bound have no join.
  sym (failure-inj (trans (sym (cong proj₁ (cong (Once.TypeCheck.Elaborate.inferElabV-RDestruct-join _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                                                (proj₂ (join?-apart ¬eq)))))
                          eqOuter))
  where
    failure-inj : ∀ {n} {Δ} {e e′} → _≡_ {A = InferElabResult {n} Δ} (failure e) (failure e′) → e ≡ e′
    failure-inj refl = refl

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

var-unbound-is-UnboundVariable : ∀ {m} (ctx : NamedCtx m) (x : String)
    {err : TypeError}
  → lookupLocal ctx x ≡ nothing
  → lookupImport (Classify.NamedCtx.imports ctx) x ≡ nothing
  → inferElab ctx (Raw.RVar x) ≡ failure err
  → err ≡ UnboundVariable x
-- D136: the `¬ (x ≡ "unit")` premise is gone — `unit` is `RResolved (gen
-- "unit")` now, so a bare `unit` is an ordinary variable that CAN be unbound.
var-unbound-is-UnboundVariable ctx x eqLoc eqImp eqOuter
  = go (trans (sym (cong proj₁ (trans (helperLoc _ eqLoc) (helperImp _ eqImp)))) eqOuter)
  where
    open Once.TypeCheck.Elaborate using (inferElabV-RVar-lookup-aux)
    helperLoc : ∀ (lhs : Maybe (∃[ A' ] ∃[ Ψ' ] (Surface.SVar (Classify.NamedCtx.debruijn ctx) Ψ' A')))
              → (eq' : lookupLocal ctx x ≡ lhs)
              → inferElabV-RVar-lookup-aux ctx x (lookupLocal ctx x) refl _ refl
                ≡ inferElabV-RVar-lookup-aux ctx x lhs eq' _ refl
    helperLoc _ refl = refl
    helperImp : ∀ (lhs : Maybe (Ty _))
              → (eq' : lookupImport (Classify.NamedCtx.imports ctx) x ≡ lhs)
              → inferElabV-RVar-lookup-aux ctx x nothing eqLoc (lookupImport (Classify.NamedCtx.imports ctx) x) refl
                ≡ inferElabV-RVar-lookup-aux ctx x nothing eqLoc lhs eq'
    helperImp _ refl = refl
    go : ∀ {err} → failure (UnboundVariable x) ≡ failure err
       → err ≡ UnboundVariable x
    go refl = refl
check-RInt-type-mismatch : ∀ {m} (ctx : NamedCtx m) (n : _) (T : Ty m) {err : TypeError}
  → ¬ (T ≡ Int)
  → checkElab ctx (Raw.RInt n) T ≡ failure err
  → err ≡ TypeMismatch T Int
-- D127: the value-lift is gone, so `checkElab (RInt n) T` is PLAIN
-- infer-and-match — no `isRIntVliftTarget?` dispatch to mirror. An arrow target
-- is no longer a success to refute; it is one more `TypeMismatch T Int`.
check-RInt-type-mismatch ctx n T ¬eq eq
  with Int <:? T | eq
... | yes sub-int | _    = ⊥-elim (¬eq refl)
... | no _        | refl = refl

-- D127: `cl-err` is deleted with `closed-lift-aux`. There is no lift left to
-- walk: at an arrow target the elaborator reports `TypeMismatch` directly, so
-- every leaf below is `refl`.

-- D226: the mode switch fails only on `no` to `A <:? T`, and then its error is
-- `TypeMismatch T A`. A literal's inferred type admits one supertype — itself —
-- so `yes` pins `T` and contradicts the premise.

check-RUnit-type-mismatch : ∀ {m} (ctx : NamedCtx m) (T : Ty m) {err : TypeError}
  → ¬ (T ≡ Unit)
  → checkElab ctx Raw.RUnit T ≡ failure err
  → err ≡ TypeMismatch T Unit
check-RUnit-type-mismatch ctx T ¬eq eq
  with Unit <:? T | eq
... | yes sub-unit | _    = ⊥-elim (¬eq refl)
... | no _         | refl = refl

lam-usage-violation-is-UsageViolation : ∀ {m} (ctx : NamedCtx m) (x : String) (body : Raw.RawExpr)
    (A : Ty m) (q : _) (B : Ty m)
    (q' : _) {Ψ' eE' d' f' err}
  → Once.TypeCheck.Elaborate.checkElab
      (Classify.extendNamedCtx ctx x A) body B
      ≡ success (q' SCx.∷ Ψ') eE' d' f'
  → Once.TypeCheck.Elaborate.decideLeq q' q ≡ nothing
  → Once.TypeCheck.Elaborate.checkElab ctx (Raw.RLam x body)
      (A T.⇒[ T.mk-kind q T.pure ] B) ≡ failure err
  → err ≡ Once.TypeCheck.Error.UsageViolation x q q'
lam-usage-violation-is-UsageViolation ctx x body A q B q' eqInner eqLeq eqOuter
  with checkElabV (Classify.extendNamedCtx ctx x A) body B | eqInner
... | success (_ SCx.∷ _) _ _ _ , _ | refl
    with Once.TypeCheck.Elaborate.decideLeq q' q | eqLeq
...   | nothing | refl with eqOuter
...     | refl = refl

------------------------------------------------------------------------
-- BinOpLeftError / BinOpRightError: sub-errors from binop operands
-- are wrapped in the structured error. Now a direct `refl` since the
-- elaborator emits `failure (BinOpLeftError err)` where `err` is
-- already a TypeError from `asInt`'s notInt branch.
------------------------------------------------------------------------

-- When the left operand of a binop infers to a non-Int and produces
-- `asInt-sub-err : TypeError`, the outer err equals
-- `BinOpLeftError asInt-sub-err`.
-- When the left operand of a binop is NOT NUMERIC, the outer err equals
-- `BinOpLeftError sub-err`.
--
-- PLAN 0.75 F4 CHANGED THE HYPOTHESIS, and the old one is now FALSE rather
-- than merely weaker. This was stated over `asInt`'s failure, and `asInt`
-- fails on `Float` — but a `Float` left operand is now a good operand, so
-- `1.5 + ()` reports `BinOpRightError (TypeMismatch {0} Float Unit)` while the
-- lemma claimed `BinOpLeftError (TypeMismatch {0} Int Float)`. The right
-- hypothesis is the one it always meant: the left operand is not a number at
-- all. `notNumeric` says exactly that, with `asInt`'s own error messages, so
-- nothing a user sees changes.
--
-- `binop-right-err-wraps` below needs no such repair: it requires the LEFT to
-- be `Int`, and an `Int` left with a `Float` right IS still an error.
binop-left-err-wraps : ∀ {m} (ctx : NamedCtx m) (op : Raw.BinOp) (e₁ e₂ : Raw.RawExpr)
    {sub-err outer-err}
  → Once.TypeCheck.Elaborate.notNumeric (inferElab ctx e₁) ≡ just sub-err
  → inferElab ctx (Raw.RBinOp op e₁ e₂) ≡ failure outer-err
  → outer-err ≡ Once.TypeCheck.Error.BinOpLeftError sub-err
binop-left-err-wraps ctx op e₁ e₂ eqNN eqOuter
  with inferElabV ctx e₁
... | failure _ , _                       with eqNN
...   | refl with eqOuter
...     | refl = refl
binop-left-err-wraps ctx op e₁ e₂ eqNN eqOuter
    | success Unit _ _ _ _ , _ with eqNN
...   | refl with inferElabV ctx e₂ | eqOuter
...     | failure _ , _ | refl = refl
...     | success Void _ _ _ _ , _ | refl = refl
...     | success Unit _ _ _ _ , _ | refl = refl
...     | success Int _ _ _ _ , _ | refl = refl
...     | success T.Float _ _ _ _ , _ | refl = refl
...     | success (T.var _) _ _ _ _ , _ | refl = refl
...     | success (_ T.* _) _ _ _ _ , _ | refl = refl
...     | success (_ T.+ _) _ _ _ _ , _ | refl = refl
...     | success (_ T.⇒[ _ ] _) _ _ _ _ , _ | refl = refl
...     | success (T.μ _) _ _ _ _ , _ | refl = refl
...     | success (T.ν _ _) _ _ _ _ , _ | refl = refl
binop-left-err-wraps ctx op e₁ e₂ eqNN eqOuter
    | success (T.var _) _ _ _ _ , _ with eqNN
...   | refl with inferElabV ctx e₂ | eqOuter
...     | failure _ , _ | refl = refl
...     | success Void _ _ _ _ , _ | refl = refl
...     | success Unit _ _ _ _ , _ | refl = refl
...     | success Int _ _ _ _ , _ | refl = refl
...     | success T.Float _ _ _ _ , _ | refl = refl
...     | success (T.var _) _ _ _ _ , _ | refl = refl
...     | success (_ T.* _) _ _ _ _ , _ | refl = refl
...     | success (_ T.+ _) _ _ _ _ , _ | refl = refl
...     | success (_ T.⇒[ _ ] _) _ _ _ _ , _ | refl = refl
...     | success (T.μ _) _ _ _ _ , _ | refl = refl
...     | success (T.ν _ _) _ _ _ _ , _ | refl = refl

binop-left-err-wraps ctx op e₁ e₂ eqNN eqOuter
    | success (_ T.* _) _ _ _ _ , _ with eqNN
...   | refl with inferElabV ctx e₂ | eqOuter
...     | failure _ , _ | refl = refl
...     | success Void _ _ _ _ , _ | refl = refl
...     | success Unit _ _ _ _ , _ | refl = refl
...     | success Int _ _ _ _ , _ | refl = refl
...     | success T.Float _ _ _ _ , _ | refl = refl
...     | success (T.var _) _ _ _ _ , _ | refl = refl
...     | success (_ T.* _) _ _ _ _ , _ | refl = refl
...     | success (_ T.+ _) _ _ _ _ , _ | refl = refl
...     | success (_ T.⇒[ _ ] _) _ _ _ _ , _ | refl = refl
...     | success (T.μ _) _ _ _ _ , _ | refl = refl
...     | success (T.ν _ _) _ _ _ _ , _ | refl = refl
binop-left-err-wraps ctx op e₁ e₂ eqNN eqOuter
    | success (_ T.+ _) _ _ _ _ , _ with eqNN
...   | refl with inferElabV ctx e₂ | eqOuter
...     | failure _ , _ | refl = refl
...     | success Void _ _ _ _ , _ | refl = refl
...     | success Unit _ _ _ _ , _ | refl = refl
...     | success Int _ _ _ _ , _ | refl = refl
...     | success T.Float _ _ _ _ , _ | refl = refl
...     | success (T.var _) _ _ _ _ , _ | refl = refl
...     | success (_ T.* _) _ _ _ _ , _ | refl = refl
...     | success (_ T.+ _) _ _ _ _ , _ | refl = refl
...     | success (_ T.⇒[ _ ] _) _ _ _ _ , _ | refl = refl
...     | success (T.μ _) _ _ _ _ , _ | refl = refl
...     | success (T.ν _ _) _ _ _ _ , _ | refl = refl
binop-left-err-wraps ctx op e₁ e₂ eqNN eqOuter
    | success (_ T.⇒[ _ ] _) _ _ _ _ , _ with eqNN
...   | refl with inferElabV ctx e₂ | eqOuter
...     | failure _ , _ | refl = refl
...     | success Void _ _ _ _ , _ | refl = refl
...     | success Unit _ _ _ _ , _ | refl = refl
...     | success Int _ _ _ _ , _ | refl = refl
...     | success T.Float _ _ _ _ , _ | refl = refl
...     | success (T.var _) _ _ _ _ , _ | refl = refl
...     | success (_ T.* _) _ _ _ _ , _ | refl = refl
...     | success (_ T.+ _) _ _ _ _ , _ | refl = refl
...     | success (_ T.⇒[ _ ] _) _ _ _ _ , _ | refl = refl
...     | success (T.μ _) _ _ _ _ , _ | refl = refl
...     | success (T.ν _ _) _ _ _ _ , _ | refl = refl
binop-left-err-wraps ctx op e₁ e₂ eqNN eqOuter
    | success (T.μ _) _ _ _ _ , _ with eqNN
...   | refl with inferElabV ctx e₂ | eqOuter
...     | failure _ , _ | refl = refl
...     | success Void _ _ _ _ , _ | refl = refl
...     | success Unit _ _ _ _ , _ | refl = refl
...     | success Int _ _ _ _ , _ | refl = refl
...     | success T.Float _ _ _ _ , _ | refl = refl
...     | success (T.var _) _ _ _ _ , _ | refl = refl
...     | success (_ T.* _) _ _ _ _ , _ | refl = refl
...     | success (_ T.+ _) _ _ _ _ , _ | refl = refl
...     | success (_ T.⇒[ _ ] _) _ _ _ _ , _ | refl = refl
...     | success (T.μ _) _ _ _ _ , _ | refl = refl
...     | success (T.ν _ _) _ _ _ _ , _ | refl = refl
binop-left-err-wraps ctx op e₁ e₂ eqNN eqOuter
    | success (T.ν _ _) _ _ _ _ , _ with eqNN
...   | refl with inferElabV ctx e₂ | eqOuter
...     | failure _ , _ | refl = refl
...     | success Void _ _ _ _ , _ | refl = refl
...     | success Unit _ _ _ _ , _ | refl = refl
...     | success Int _ _ _ _ , _ | refl = refl
...     | success T.Float _ _ _ _ , _ | refl = refl
...     | success (T.var _) _ _ _ _ , _ | refl = refl
...     | success (_ T.* _) _ _ _ _ , _ | refl = refl
...     | success (_ T.+ _) _ _ _ _ , _ | refl = refl
...     | success (_ T.⇒[ _ ] _) _ _ _ _ , _ | refl = refl
...     | success (T.μ _) _ _ _ _ , _ | refl = refl
...     | success (T.ν _ _) _ _ _ _ , _ | refl = refl
-- NUMERIC left types are absurd here: `notNumeric` answers `nothing` for each.
binop-left-err-wraps ctx op e₁ e₂ eqNN eqOuter
    | success Int _ _ _ _ , _             with eqNN
...   | ()
binop-left-err-wraps ctx op e₁ e₂ eqNN eqOuter
    | success T.Float _ _ _ _ , _         with eqNN
...   | ()
-- D251: a `Void` left operand is not numeric, and the dispatch rejects it
-- whatever the right one is.
binop-left-err-wraps ctx op e₁ e₂ eqNN eqOuter
    | success Void _ _ _ _ , _            with eqNN
...   | refl with eqOuter
...     | refl = refl

binop-right-err-wraps : ∀ {m} (ctx : NamedCtx m) (op : Raw.BinOp) (e₁ e₂ : Raw.RawExpr)
    {Ψ₁ e₁E d₁ f₁ sub-err outer-err}
  → Once.TypeCheck.Elaborate.asInt (inferElab ctx e₁)
      ≡ Once.TypeCheck.Elaborate.isInt Ψ₁ e₁E d₁ f₁
  → Once.TypeCheck.Elaborate.asInt (inferElab ctx e₂)
      ≡ Once.TypeCheck.Elaborate.notInt sub-err
  → inferElab ctx (Raw.RBinOp op e₁ e₂) ≡ failure outer-err
  → outer-err ≡ Once.TypeCheck.Error.BinOpRightError sub-err
binop-right-err-wraps ctx op e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
  with inferElabV ctx e₁
... | failure _ , _                       with eqAsInt₁
...   | ()
binop-right-err-wraps ctx op e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Unit _ _ _ _ , _            with eqAsInt₁
...   | ()
binop-right-err-wraps ctx op e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Void _ _ _ _ , _            with eqAsInt₁
...   | ()
binop-right-err-wraps ctx op e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success T.Float _ _ _ _ , _         with eqAsInt₁
...   | ()
binop-right-err-wraps ctx op e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success (T.var _) _ _ _ _ , _        with eqAsInt₁
...   | ()

binop-right-err-wraps ctx op e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success (_ T.* _) _ _ _ _ , _       with eqAsInt₁
...   | ()
binop-right-err-wraps ctx op e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success (_ T.+ _) _ _ _ _ , _       with eqAsInt₁
...   | ()
binop-right-err-wraps ctx op e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success (_ T.⇒[ _ ] _) _ _ _ _ , _  with eqAsInt₁
...   | ()
binop-right-err-wraps ctx op e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success (T.μ _) _ _ _ _ , _    with eqAsInt₁
...   | ()
binop-right-err-wraps ctx op e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success (T.ν _ _) _ _ _ _ , _    with eqAsInt₁
...   | ()
binop-right-err-wraps ctx op e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Int _ _ _ _ , _ with inferElabV ctx e₂
... | failure _ , _ with eqAsInt₂
...   | refl with eqOuter
...     | refl = refl
binop-right-err-wraps ctx op e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Int _ _ _ _ , _ | success Unit _ _ _ _ , _ with eqAsInt₂
... | refl with eqOuter
...   | refl = refl
binop-right-err-wraps ctx op e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Int _ _ _ _ , _ | success Void _ _ _ _ , _ with eqAsInt₂
... | refl with eqOuter
...   | refl = refl
binop-right-err-wraps ctx op e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Int _ _ _ _ , _ | success Int _ _ _ _ , _ with eqAsInt₂
... | ()
-- PLAN 0.75 F4 / D125: `Int` left with `Float` right now SPLITS ON THE
-- OPERATOR. For `+`, `−` and `×` the `Int` side widens and the binop SUCCEEDS,
-- so the failure premise is absurd; for the other eight there is no float
-- form, the error is still `BinOpRightError (TypeMismatch {0} Int Float)`, and the
-- claim holds unchanged. One clause could not cover both, which is the
-- statement noticing that the language grew.
binop-right-err-wraps ctx Raw.OpAdd e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Int _ _ _ _ , _ | success T.Float _ _ _ _ , _ with eqAsInt₂
... | refl with eqOuter
...   | ()
binop-right-err-wraps ctx Raw.OpSub e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Int _ _ _ _ , _ | success T.Float _ _ _ _ , _ with eqAsInt₂
... | refl with eqOuter
...   | ()
binop-right-err-wraps ctx Raw.OpMul e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Int _ _ _ _ , _ | success T.Float _ _ _ _ , _ with eqAsInt₂
... | refl with eqOuter
...   | ()
binop-right-err-wraps ctx Raw.OpDiv e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Int _ _ _ _ , _ | success T.Float _ _ _ _ , _ with eqAsInt₂
... | refl with eqOuter
...   | ()
binop-right-err-wraps ctx Raw.OpMod e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Int _ _ _ _ , _ | success T.Float _ _ _ _ , _ with eqAsInt₂
... | refl with eqOuter
...   | refl = refl
binop-right-err-wraps ctx Raw.OpLt e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Int _ _ _ _ , _ | success T.Float _ _ _ _ , _ with eqAsInt₂
... | refl with eqOuter
...   | refl = refl
binop-right-err-wraps ctx Raw.OpLe e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Int _ _ _ _ , _ | success T.Float _ _ _ _ , _ with eqAsInt₂
... | refl with eqOuter
...   | refl = refl
binop-right-err-wraps ctx Raw.OpGt e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Int _ _ _ _ , _ | success T.Float _ _ _ _ , _ with eqAsInt₂
... | refl with eqOuter
...   | refl = refl
binop-right-err-wraps ctx Raw.OpGe e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Int _ _ _ _ , _ | success T.Float _ _ _ _ , _ with eqAsInt₂
... | refl with eqOuter
...   | refl = refl
binop-right-err-wraps ctx Raw.OpEq e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Int _ _ _ _ , _ | success T.Float _ _ _ _ , _ with eqAsInt₂
... | refl with eqOuter
...   | refl = refl
binop-right-err-wraps ctx Raw.OpNe e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Int _ _ _ _ , _ | success T.Float _ _ _ _ , _ with eqAsInt₂
... | refl with eqOuter
...   | refl = refl
binop-right-err-wraps ctx op e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Int _ _ _ _ , _ | success (T.var _) _ _ _ _ , _ with eqAsInt₂
... | refl with eqOuter
...   | refl = refl

binop-right-err-wraps ctx op e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Int _ _ _ _ , _ | success (_ T.* _) _ _ _ _ , _ with eqAsInt₂
... | refl with eqOuter
...   | refl = refl
binop-right-err-wraps ctx op e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Int _ _ _ _ , _ | success (_ T.+ _) _ _ _ _ , _ with eqAsInt₂
... | refl with eqOuter
...   | refl = refl
binop-right-err-wraps ctx op e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Int _ _ _ _ , _ | success (_ T.⇒[ _ ] _) _ _ _ _ , _ with eqAsInt₂
... | refl with eqOuter
...   | refl = refl
binop-right-err-wraps ctx op e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Int _ _ _ _ , _ | success (T.μ _) _ _ _ _ , _ with eqAsInt₂
... | refl with eqOuter
...   | refl = refl
binop-right-err-wraps ctx op e₁ e₂ eqAsInt₁ eqAsInt₂ eqOuter
    | success Int _ _ _ _ , _ | success (T.ν _ _) _ _ _ _ , _ with eqAsInt₂
... | refl with eqOuter
...   | refl = refl
fst-non-pair-Float : ∀ {m} (ctx : NamedCtx m) (arg : Raw.RawExpr)
                      {Ψ' eE' d' f' err}
                    → inferElab ctx arg ≡ success T.Float Ψ' eE' d' f'
                    → inferElab ctx (Raw.RApp (Raw.RResolved (gen "fst")) arg) ≡ failure err
                    → err ≡ FstNeedsPair
fst-non-pair-Float ctx arg eqInner eqOuter = rejects (inferFstOn ctx arg) (inferElabV ctx arg) eqInner refl eqOuter
fst-non-pair-Sum : ∀ {m} (ctx : NamedCtx m) (arg : Raw.RawExpr) {A B : Ty m}
                    {Ψ' eE' d' f' err}
                  → inferElab ctx arg ≡ success (A T.+ B) Ψ' eE' d' f'
                  → inferElab ctx (Raw.RApp (Raw.RResolved (gen "fst")) arg) ≡ failure err
                  → err ≡ FstNeedsPair
fst-non-pair-Sum ctx arg eqInner eqOuter = rejects (inferFstOn ctx arg) (inferElabV ctx arg) eqInner refl eqOuter
fst-non-pair-Fun : ∀ {m} (ctx : NamedCtx m) (arg : Raw.RawExpr) {A B : Ty m} {q : _}
                    {Ψ' eE' d' f' err}
                  → inferElab ctx arg ≡ success (A T.⇒[ T.mk-kind q T.pure ] B) Ψ' eE' d' f'
                  → inferElab ctx (Raw.RApp (Raw.RResolved (gen "fst")) arg) ≡ failure err
                  → err ≡ FstNeedsPair
fst-non-pair-Fun ctx arg eqInner eqOuter = rejects (inferFstOn ctx arg) (inferElabV ctx arg) eqInner refl eqOuter
neg-non-Int-Float : ∀ {m} (ctx : NamedCtx m) (e : Raw.RawExpr)
                     {Ψ' eE' d' f' err}
                   → inferElab ctx e ≡ success T.Float Ψ' eE' d' f'
                   → inferElab ctx (Raw.RNeg e) ≡ failure err
                   → err ≡ TypeMismatch Int T.Float
-- PLAN 0.73 F3 CHANGES WHICH PREMISE DOES THE WORK HERE, and this is the one
-- lemma where it matters. The claim is unchanged and still TRUE, but for a
-- `RFloat` operand it is now true VACUOUSLY: `-3.14` no longer fails, so the
-- premise `inferElab ctx (RNeg e) ≡ failure err` is what cannot
-- hold. Before F3 the same case was discharged by the operand's own inference.
--
-- Read the other direction, that is the statement earning its keep: had the
-- fold been wired without a matching rule in `_⊢ᵢ_∶_⨾_`, this `()` would not
-- typecheck, because `- 3.14` would still be a failure whose error is now
-- something else. The lemma is a live check on the pair, not a formality.
neg-non-Int-Float ctx e eqInner eqOuter = neg-rejects e (negOperandView e) eqInner refl eqOuter


neg-non-Int-Product : ∀ {m} (ctx : NamedCtx m) (e : Raw.RawExpr) {A B : Ty m}
                       {Ψ' eE' d' f' err}
                     → inferElab ctx e ≡ success (A T.* B) Ψ' eE' d' f'
                     → inferElab ctx (Raw.RNeg e) ≡ failure err
                     → err ≡ TypeMismatch Int (A T.* B)
neg-non-Int-Product ctx e eqInner eqOuter = neg-rejects e (negOperandView e) eqInner refl eqOuter

neg-non-Int-Sum : ∀ {m} (ctx : NamedCtx m) (e : Raw.RawExpr) {A B : Ty m}
                   {Ψ' eE' d' f' err}
                 → inferElab ctx e ≡ success (A T.+ B) Ψ' eE' d' f'
                 → inferElab ctx (Raw.RNeg e) ≡ failure err
                 → err ≡ TypeMismatch Int (A T.+ B)
neg-non-Int-Sum ctx e eqInner eqOuter = neg-rejects e (negOperandView e) eqInner refl eqOuter
snd-non-pair-Float : ∀ {m} (ctx : NamedCtx m) (arg : Raw.RawExpr)
                      {Ψ' eE' d' f' err}
                    → inferElab ctx arg ≡ success T.Float Ψ' eE' d' f'
                    → inferElab ctx (Raw.RApp (Raw.RResolved (gen "snd")) arg) ≡ failure err
                    → err ≡ SndNeedsPair
snd-non-pair-Float ctx arg eqInner eqOuter = rejects (inferSndOn ctx arg) (inferElabV ctx arg) eqInner refl eqOuter
snd-non-pair-Sum : ∀ {m} (ctx : NamedCtx m) (arg : Raw.RawExpr) {A B : Ty m}
                    {Ψ' eE' d' f' err}
                  → inferElab ctx arg ≡ success (A T.+ B) Ψ' eE' d' f'
                  → inferElab ctx (Raw.RApp (Raw.RResolved (gen "snd")) arg) ≡ failure err
                  → err ≡ SndNeedsPair
snd-non-pair-Sum ctx arg eqInner eqOuter = rejects (inferSndOn ctx arg) (inferElabV ctx arg) eqInner refl eqOuter
snd-non-pair-Fun : ∀ {m} (ctx : NamedCtx m) (arg : Raw.RawExpr) {A B : Ty m} {q : _}
                    {Ψ' eE' d' f' err}
                  → inferElab ctx arg ≡ success (A T.⇒[ T.mk-kind q T.pure ] B) Ψ' eE' d' f'
                  → inferElab ctx (Raw.RApp (Raw.RResolved (gen "snd")) arg) ≡ failure err
                  → err ≡ SndNeedsPair
snd-non-pair-Fun ctx arg eqInner eqOuter = rejects (inferSndOn ctx arg) (inferElabV ctx arg) eqInner refl eqOuter
case-scrut-Float : ∀ {m} (ctx : NamedCtx m) (scrut : Raw.RawExpr)
                      (xL : String) (eL : Raw.RawExpr)
                      (xR : String) (eR : Raw.RawExpr)
                      {Ψ' eE' d' f' err}
                    → inferElab ctx scrut ≡ success T.Float Ψ' eE' d' f'
                    → inferElab ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
                    → err ≡ CaseScrutineeNotSum
case-scrut-Float ctx scrut xL eL xR eR eqInner eqOuter =
  rejects (inferElabV-RDestruct-aux ctx scrut xL eL xR eR) (inferElabV ctx scrut) eqInner refl eqOuter
case-scrut-Product : ∀ {m} (ctx : NamedCtx m) (scrut : Raw.RawExpr)
                      (xL : String) (eL : Raw.RawExpr)
                      (xR : String) (eR : Raw.RawExpr)
                      {A B : Ty m} {Ψ' eE' d' f' err}
                    → inferElab ctx scrut ≡ success (A T.* B) Ψ' eE' d' f'
                    → inferElab ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
                    → err ≡ CaseScrutineeNotSum
case-scrut-Product ctx scrut xL eL xR eR eqInner eqOuter =
  rejects (inferElabV-RDestruct-aux ctx scrut xL eL xR eR) (inferElabV ctx scrut) eqInner refl eqOuter
case-scrut-Fun : ∀ {m} (ctx : NamedCtx m) (scrut : Raw.RawExpr)
                      (xL : String) (eL : Raw.RawExpr)
                      (xR : String) (eR : Raw.RawExpr)
                      {A B : Ty m} {q : _} {Ψ' eE' d' f' err}
                    → inferElab ctx scrut ≡ success (A T.⇒[ T.mk-kind q T.pure ] B) Ψ' eE' d' f'
                    → inferElab ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
                    → err ≡ CaseScrutineeNotSum
case-scrut-Fun ctx scrut xL eL xR eR eqInner eqOuter =
  rejects (inferElabV-RDestruct-aux ctx scrut xL eL xR eR) (inferElabV ctx scrut) eqInner refl eqOuter
fst-non-pair-Eff : ∀ {m} (ctx : NamedCtx m) (arg : Raw.RawExpr) {A B : Ty m}
                     {Ψ' eE' d' f' err}
                   → inferElab ctx arg ≡ success (A T.⇒[ T.mk-kind T.Many T.eff ] B) Ψ' eE' d' f'
                   → inferElab ctx (Raw.RApp (Raw.RResolved (gen "fst")) arg) ≡ failure err
                   → err ≡ FstNeedsPair
fst-non-pair-Eff ctx arg eqInner eqOuter = rejects (inferFstOn ctx arg) (inferElabV ctx arg) eqInner refl eqOuter
fst-non-pair-μ : ∀ {m} (ctx : NamedCtx m) (arg : Raw.RawExpr) {F : Fun m}
                  {Ψ' eE' d' f' err}
                → inferElab ctx arg ≡ success (T.μ F) Ψ' eE' d' f'
                → inferElab ctx (Raw.RApp (Raw.RResolved (gen "fst")) arg) ≡ failure err
                → err ≡ FstNeedsPair
fst-non-pair-μ ctx arg eqInner eqOuter = rejects (inferFstOn ctx arg) (inferElabV ctx arg) eqInner refl eqOuter
fst-non-pair-ν : ∀ {m} (ctx : NamedCtx m) (arg : Raw.RawExpr) {F : Fun m} {π}
                  {Ψ' eE' d' f' err}
                → inferElab ctx arg ≡ success (T.ν F π) Ψ' eE' d' f'
                → inferElab ctx (Raw.RApp (Raw.RResolved (gen "fst")) arg) ≡ failure err
                → err ≡ FstNeedsPair
fst-non-pair-ν ctx arg eqInner eqOuter = rejects (inferFstOn ctx arg) (inferElabV ctx arg) eqInner refl eqOuter
snd-non-pair-Eff : ∀ {m} (ctx : NamedCtx m) (arg : Raw.RawExpr) {A B : Ty m}
                     {Ψ' eE' d' f' err}
                   → inferElab ctx arg ≡ success (A T.⇒[ T.mk-kind T.Many T.eff ] B) Ψ' eE' d' f'
                   → inferElab ctx (Raw.RApp (Raw.RResolved (gen "snd")) arg) ≡ failure err
                   → err ≡ SndNeedsPair
snd-non-pair-Eff ctx arg eqInner eqOuter = rejects (inferSndOn ctx arg) (inferElabV ctx arg) eqInner refl eqOuter
snd-non-pair-μ : ∀ {m} (ctx : NamedCtx m) (arg : Raw.RawExpr) {F : Fun m}
                  {Ψ' eE' d' f' err}
                → inferElab ctx arg ≡ success (T.μ F) Ψ' eE' d' f'
                → inferElab ctx (Raw.RApp (Raw.RResolved (gen "snd")) arg) ≡ failure err
                → err ≡ SndNeedsPair
snd-non-pair-μ ctx arg eqInner eqOuter = rejects (inferSndOn ctx arg) (inferElabV ctx arg) eqInner refl eqOuter
snd-non-pair-ν : ∀ {m} (ctx : NamedCtx m) (arg : Raw.RawExpr) {F : Fun m} {π}
                  {Ψ' eE' d' f' err}
                → inferElab ctx arg ≡ success (T.ν F π) Ψ' eE' d' f'
                → inferElab ctx (Raw.RApp (Raw.RResolved (gen "snd")) arg) ≡ failure err
                → err ≡ SndNeedsPair
snd-non-pair-ν ctx arg eqInner eqOuter = rejects (inferSndOn ctx arg) (inferElabV ctx arg) eqInner refl eqOuter
neg-non-Int-Eff : ∀ {m} (ctx : NamedCtx m) (e : Raw.RawExpr) {A B : Ty m}
                    {Ψ' eE' d' f' err}
                  → inferElab ctx e ≡ success (A T.⇒[ T.mk-kind T.Many T.eff ] B) Ψ' eE' d' f'
                  → inferElab ctx (Raw.RNeg e) ≡ failure err
                  → err ≡ TypeMismatch Int (A T.⇒[ T.mk-kind T.Many T.eff ] B)
neg-non-Int-Eff ctx e eqInner eqOuter = neg-rejects e (negOperandView e) eqInner refl eqOuter

neg-non-Int-μ : ∀ {m} (ctx : NamedCtx m) (e : Raw.RawExpr) {F : Fun m}
                 {Ψ' eE' d' f' err}
               → inferElab ctx e ≡ success (T.μ F) Ψ' eE' d' f'
               → inferElab ctx (Raw.RNeg e) ≡ failure err
               → err ≡ TypeMismatch Int (T.μ F)
neg-non-Int-μ ctx e eqInner eqOuter = neg-rejects e (negOperandView e) eqInner refl eqOuter

neg-non-Int-ν : ∀ {m} (ctx : NamedCtx m) (e : Raw.RawExpr) {F : Fun m} {π}
                 {Ψ' eE' d' f' err}
               → inferElab ctx e ≡ success (T.ν F π) Ψ' eE' d' f'
               → inferElab ctx (Raw.RNeg e) ≡ failure err
               → err ≡ TypeMismatch Int (T.ν F π)
neg-non-Int-ν ctx e eqInner eqOuter = neg-rejects e (negOperandView e) eqInner refl eqOuter

neg-non-Int-Fun : ∀ {m} (ctx : NamedCtx m) (e : Raw.RawExpr) {A B : Ty m} {q : _}
                    {Ψ' eE' d' f' err}
                  → inferElab ctx e ≡ success (A T.⇒[ T.mk-kind q T.pure ] B) Ψ' eE' d' f'
                  → inferElab ctx (Raw.RNeg e) ≡ failure err
                  → err ≡ TypeMismatch Int (A T.⇒[ T.mk-kind q T.pure ] B)
neg-non-Int-Fun ctx e eqInner eqOuter = neg-rejects e (negOperandView e) eqInner refl eqOuter
case-scrut-Eff : ∀ {m} (ctx : NamedCtx m) (scrut : Raw.RawExpr)
                    (xL : String) (eL : Raw.RawExpr)
                    (xR : String) (eR : Raw.RawExpr)
                    {A B : Ty m} {Ψ' eE' d' f' err}
                  → inferElab ctx scrut ≡ success (A T.⇒[ T.mk-kind T.Many T.eff ] B) Ψ' eE' d' f'
                  → inferElab ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
                  → err ≡ CaseScrutineeNotSum
case-scrut-Eff ctx scrut xL eL xR eR eqInner eqOuter =
  rejects (inferElabV-RDestruct-aux ctx scrut xL eL xR eR) (inferElabV ctx scrut) eqInner refl eqOuter
case-scrut-μ : ∀ {m} (ctx : NamedCtx m) (scrut : Raw.RawExpr)
                  (xL : String) (eL : Raw.RawExpr)
                  (xR : String) (eR : Raw.RawExpr)
                  {F : Fun m} {Ψ' eE' d' f' err}
                → inferElab ctx scrut ≡ success (T.μ F) Ψ' eE' d' f'
                → inferElab ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
                → err ≡ CaseScrutineeNotSum
case-scrut-μ ctx scrut xL eL xR eR eqInner eqOuter =
  rejects (inferElabV-RDestruct-aux ctx scrut xL eL xR eR) (inferElabV ctx scrut) eqInner refl eqOuter
case-scrut-ν : ∀ {m} (ctx : NamedCtx m) (scrut : Raw.RawExpr)
                (xL : String) (eL : Raw.RawExpr)
                (xR : String) (eR : Raw.RawExpr)
                {F : Fun m} {π} {Ψ' eE' d' f' err}
              → inferElab ctx scrut ≡ success (T.ν F π) Ψ' eE' d' f'
              → inferElab ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
              → err ≡ CaseScrutineeNotSum
case-scrut-ν ctx scrut xL eL xR eR eqInner eqOuter =
  rejects (inferElabV-RDestruct-aux ctx scrut xL eL xR eR) (inferElabV ctx scrut) eqInner refl eqOuter
