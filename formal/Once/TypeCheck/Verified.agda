-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.Verified
--
-- Bundles the type-checker entry points with the proof obligations
-- that must hold of them. The record `VerifiedTypeChecker` cannot be
-- constructed without witnesses to every proven property — so if a
-- proof regresses, the single inhabitant `verifiedTypeChecker` ceases
-- to type-check, and everything downstream that uses it fails to
-- compile.
--
-- This is how the proofs are *structurally enforced* rather than
-- loosely bolted on via imports: the public API of the type-checker
-- exposes `verifiedTypeChecker : VerifiedTypeChecker`, so the proofs
-- are part of the API surface, not an optional extra.
--
-- To add a new proven property:
--   1. Prove the property in its own module (e.g. plan 0.3 G-n).
--   2. Add a matching field to `VerifiedTypeChecker` below.
--   3. Fill the field in `verifiedTypeChecker`.
-- Steps (2) and (3) are mandatory — Agda will reject a record value
-- with missing fields, or a record type with an unfilled field.
--
-- As of plan 0.3's main pass: ~99 proof fields across G2 (soundness +
-- per-rule completeness), G3 (totality), G4 (structured errors +
-- per-Type coverage), G6 (determinism), G7 (algebraic identities),
-- and the Grammar round-trip.
--
-- Reference: plans/0.3-frontend-verification-gaps.md.
------------------------------------------------------------------------

import Once.TypeCheck.Raw as Raw

import Once.Spec.Context as SCx
open import Once.Type.Core using (wk₀)
open import Once.Spec.Type using (Ty)
open import Once.Type.Grade using (_≤qᵇ_)
import Once.Spec.Grade
module Once.TypeCheck.Verified where


import Once.Context as Surface
open import Once.Spec.Context using (Ctx)
import Once.Spec.Context as Surface

open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_; _×_; ∃-syntax)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Spec.Type using (Type)
open import Once.Type.Concrete using (IsConcrete)
import Once.Type.Sub
import Once.Spec.Sub
import Once.Type.Join
import Once.Type.Core
import Once.Spec.Type
import Once.Type
import Once.Context
import Once.Spec.Surface.Syntax as Syn
open import Once.TypeCheck.ElaborateSound
open import Once.TypeCheck.Elaborate
  using (inferElab; checkElab; InferElabResult; CheckElabResult; success; failure)
open import Once.TypeCheck.Scope using (NamedCtx; lookupImport; lookupLocal; extendNamedCtx)
import Once.TypeCheck.Scope as Classify

open import Data.Integer using (ℤ)
open import Data.Sum using (_⊎_)
import Data.String
import Data.Bool
import Data.Empty

import Once.TypeCheck.Determinism  as Det
import Once.TypeCheck.Totality     as Tot
import Once.TypeCheck.Completeness as CS
import Once.TypeCheck.Completeness.Rules as CmpR
import Once.TypeCheck.ErrorProofs  as EP
import Once.TypeCheck.Identities   as Id
import Once.Laws.Grade as Grade
import Once.Laws.Order as Ord
import Once.Type.Sub
import Once.Spec.Sub
import Once.Surface.GradeMatrix as GM
import Algebra.Structures
import Algebra.Module.Structures
import Relation.Binary.Structures
open import Once.TypeCheck.SpecWitness using (Pack; WI; WC)
open import Once.TypeCheck.ElaborateSound using (inferElabV; checkElabV; VerifiedInferResult; VerifiedCheckResult)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (refl)
open import Once.TypeCheck.Error using (TypeError; LambdaInInferMode; InlInInferMode; InrInInferMode; InitialInInferMode; UnboundQualified; UnboundVariable; FstNeedsPair; SndNeedsPair; CaseScrutineeNotSum; CaseBranchMismatch; TypeMismatch; UsageViolation; BinOpLeftError; BinOpRightError)
open import Relation.Nullary using (¬_)
open import Once.Spec.Surface.Syntax as Raw using (RInt; RUnit; RVar; RResolved; RQualified; RAnnot; RPair; RLet; RDestruct; RNeg; RBinOp; RLam; RApp; BinOp)
open import Once.Spec.Name using (gen; GenWord)
import Once.Grammar.Convert       as Conv
open import Once.Grammar using (GType)
open Conv using (typeToGType; gtypeToType)
open Tot  using (IsInferSuccess; IsInferFailure;
                 IsCheckSuccess; IsCheckFailure)

open import Once.Surface.Syntax as Surface using () renaming (Expr to SExpr)

------------------------------------------------------------------------
-- Record: the compiler front-end + its proof obligations
------------------------------------------------------------------------

record VerifiedTypeChecker {m} : Set₁ where
  field
    ----------------------------------------------------------------
    -- Implementations
    ----------------------------------------------------------------

    -- | Inference-mode type-checker / elaborator.
    tcInfer : (ctx : NamedCtx m) (e : Syn.Expr)
            → InferElabResult (Classify.NamedCtx.debruijn ctx)

    -- | Check-mode type-checker / elaborator.
    tcCheck : (ctx : NamedCtx m) (e : Syn.Expr) (T : Ty m)
            → CheckElabResult (Classify.NamedCtx.debruijn ctx) T

    ----------------------------------------------------------------
    -- G6: determinism — the type-checker is a pure function of its
    -- inputs. (plans/0.3-frontend-verification-gaps.md, gap G6.)
    ----------------------------------------------------------------

    tcInfer-refl : ∀ (ctx : NamedCtx m) (e : Syn.Expr)
                 → tcInfer ctx e ≡ tcInfer ctx e

    tcCheck-refl : ∀ (ctx : NamedCtx m) (e : Syn.Expr) (T : Ty m)
                 → tcCheck ctx e T ≡ tcCheck ctx e T

    tcInfer-cong : ∀ (ctx : NamedCtx m) {e₁ e₂ : Syn.Expr}
                 → e₁ ≡ e₂ → tcInfer ctx e₁ ≡ tcInfer ctx e₂

    tcCheck-cong : ∀ (ctx : NamedCtx m) (T : Ty m) {e₁ e₂ : Syn.Expr}
                 → e₁ ≡ e₂ → tcCheck ctx e₁ T ≡ tcCheck ctx e₂ T

    ----------------------------------------------------------------
    -- G3: totality — every input produces either a well-formed
    -- success or a failure (no third possibility).
    -- (plans/0.3-frontend-verification-gaps.md, gap G3.)
    ----------------------------------------------------------------

    tcInfer-total : ∀ (ctx : NamedCtx m) (e : Syn.Expr)
                  → IsInferSuccess (tcInfer ctx e)
                  ⊎ IsInferFailure (tcInfer ctx e)

    tcCheck-total : ∀ (ctx : NamedCtx m) (e : Syn.Expr) (T : Ty m)
                  → IsCheckSuccess (tcCheck ctx e T)
                  ⊎ IsCheckFailure (tcCheck ctx e T)

    ----------------------------------------------------------------
    -- Soundness and completeness against the Spec (plan 0.122).
    --
    -- Every success carries the Spec's derivation of the expression,
    -- annotated with its usage, at every scope Pack, whose realization
    -- is the term built (`SpecWitness.WI`/`WC`); and the checker
    -- accepts every Use-annotated Spec derivation, at its type and
    -- usage (`Completeness`). A new elaborator path without its Spec
    -- rule, or a Spec rule the checker misses, fails to inhabit these.
    ----------------------------------------------------------------

    tcInfer-sound : ∀ (ctx : NamedCtx m) (e : Syn.Expr)
      {A : Ty m} {Ψ : Surface.Usage (Classify.NamedCtx.size ctx)}
      {eE : SExpr (Classify.NamedCtx.debruijn ctx) Ψ A} {d f : _}
      → tcInfer ctx e ≡ success A Ψ eE d f
      → WI ctx e A Ψ eE

    tcCheck-sound : ∀ (ctx : NamedCtx m) (e : Syn.Expr) (T : Ty m)
      {Ψ : Surface.Usage (Classify.NamedCtx.size ctx)}
      {eE : SExpr (Classify.NamedCtx.debruijn ctx) Ψ T} {d f : _}
      → tcCheck ctx e T ≡ success Ψ eE d f
      → WC ctx e T Ψ eE

    tcCheck-complete : ∀ {ctx : NamedCtx m} (P : Pack ctx) {e A t Ψ} {D : CS.Chk P e A t}
      → CS.U⇐ P D Ψ → ∃[ eE ] ∃[ d ] ∃[ f ] tcCheck ctx e A ≡ success Ψ eE d f

    tcInfer-complete : ∀ {ctx : NamedCtx m} (P : Pack ctx) {e A t Ψ} {D : CS.Syn P e A t}
      → CS.U⇒ P D Ψ → ∃[ eE ] ∃[ d ] ∃[ f ] tcInfer ctx e ≡ success A Ψ eE d f

    ----------------------------------------------------------------
    -- G4 (partial): structured-error preservation.
    -- Each theorem pins a specific elaborator failure path to a
    -- canonical `TypeError` variant (via `renderError`).
    ----------------------------------------------------------------

    tc-err-lam-infer : ∀ (ctx : NamedCtx m) (x : String) (body : Syn.Expr) {err : TypeError}
      → tcInfer ctx (RLam x body) ≡ failure err
      → err ≡ LambdaInInferMode

    tc-err-inl-infer : ∀ (ctx : NamedCtx m) (arg : Syn.Expr) {err : TypeError}
      → tcInfer ctx (RApp (RResolved (gen "inl")) arg) ≡ failure err
      → err ≡ InlInInferMode

    tc-err-inr-infer : ∀ (ctx : NamedCtx m) (arg : Syn.Expr) {err : TypeError}
      → tcInfer ctx (RApp (RResolved (gen "inr")) arg) ≡ failure err
      → err ≡ InrInInferMode

    tc-err-initial-infer : ∀ (ctx : NamedCtx m) (arg : Syn.Expr) {err : TypeError}
      → tcInfer ctx (RApp (RResolved (gen "initial")) arg) ≡ failure err
      → err ≡ InitialInInferMode

    tc-err-qualified-unbound : ∀ (ctx : NamedCtx m) (name alias : String) {err : TypeError}
      → tcInfer ctx (RQualified name alias) ≡ failure err
      → err ≡ (UnboundQualified name alias)

    -- fst with Unit / Int argument → FstNeedsPair
    tc-err-fst-non-pair-Unit : ∀ (ctx : NamedCtx m) (arg : Syn.Expr)
        {Ψ' eE' d' f' err}
      → tcInfer ctx arg ≡ success Once.Spec.Type.Unit Ψ' eE' d' f'
      → tcInfer ctx (RApp (RResolved (gen "fst")) arg) ≡ failure err
      → err ≡ FstNeedsPair

    tc-err-fst-non-pair-Int : ∀ (ctx : NamedCtx m) (arg : Syn.Expr)
        {Ψ' eE' d' f' err}
      → tcInfer ctx arg ≡ success Once.Spec.Type.Int Ψ' eE' d' f'
      → tcInfer ctx (RApp (RResolved (gen "fst")) arg) ≡ failure err
      → err ≡ FstNeedsPair

    -- Negation with non-Int argument → TypeMismatch Int <type>
    tc-err-neg-non-Int-Unit : ∀ (ctx : NamedCtx m) (e : Syn.Expr)
        {Ψ' eE' d' f' err}
      → tcInfer ctx e ≡ success Once.Spec.Type.Unit Ψ' eE' d' f'
      → tcInfer ctx (RNeg e) ≡ failure err
      → err ≡ TypeMismatch {0} Once.Spec.Type.Int Once.Spec.Type.Unit


    -- D136: a bare name not in local/import scope. No `unit` exception any
    -- more — `unit` is `RResolved (gen "unit")`, so a bare `unit` is an
    -- ordinary variable and CAN be unbound.
    tc-err-var-unbound : ∀ (ctx : NamedCtx m) (x : String) {err : TypeError}
      → lookupLocal ctx x ≡ nothing
      → tcInfer ctx (RVar x) ≡ failure err
      → err ≡ (UnboundVariable x)

    -- snd with Unit / Int argument → SndNeedsPair
    tc-err-snd-non-pair-Unit : ∀ (ctx : NamedCtx m) (arg : Syn.Expr)
        {Ψ' eE' d' f' err}
      → tcInfer ctx arg ≡ success Once.Spec.Type.Unit Ψ' eE' d' f'
      → tcInfer ctx (RApp (RResolved (gen "snd")) arg) ≡ failure err
      → err ≡ SndNeedsPair

    tc-err-snd-non-pair-Int : ∀ (ctx : NamedCtx m) (arg : Syn.Expr)
        {Ψ' eE' d' f' err}
      → tcInfer ctx arg ≡ success Once.Spec.Type.Int Ψ' eE' d' f'
      → tcInfer ctx (RApp (RResolved (gen "snd")) arg) ≡ failure err
      → err ≡ SndNeedsPair

    -- Case scrutinee non-sum → CaseScrutineeNotSum
    tc-err-case-scrut-Unit : ∀ (ctx : NamedCtx m) (scrut : Syn.Expr) (xL : String) (eL : Syn.Expr)
        (xR : String) (eR : Syn.Expr)
        {Ψ' eE' d' f' err}
      → tcInfer ctx scrut ≡ success Once.Spec.Type.Unit Ψ' eE' d' f'
      → tcInfer ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
      → err ≡ CaseScrutineeNotSum

    tc-err-case-scrut-Int : ∀ (ctx : NamedCtx m) (scrut : Syn.Expr) (xL : String) (eL : Syn.Expr)
        (xR : String) (eR : Syn.Expr)
        {Ψ' eE' d' f' err}
      → tcInfer ctx scrut ≡ success Once.Spec.Type.Int Ψ' eE' d' f'
      → tcInfer ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
      → err ≡ CaseScrutineeNotSum

    -- Check-mode RInt at non-Int target → TypeMismatch
    tc-err-check-RInt-type-mismatch : ∀ (ctx : NamedCtx m) (n : _) (T : Ty m) {err : TypeError}
      → ¬ (T ≡ Once.Spec.Type.Int)
      → tcCheck ctx (Raw.RInt n) T ≡ failure err
      → err ≡ (TypeMismatch T Once.Spec.Type.Int)

    -- Check-mode RUnit at non-Unit target → TypeMismatch
    tc-err-check-RUnit-type-mismatch : ∀ (ctx : NamedCtx m) (T : Ty m) {err : TypeError}
      → ¬ (T ≡ Once.Spec.Type.Unit)
      → tcCheck ctx Raw.RUnit T ≡ failure err
      → err ≡ (TypeMismatch T Once.Spec.Type.Unit)

    -- RDestruct branches with no common upper bound (no join, D322) →
    -- CaseBranchMismatch.
    tc-err-case-branch-mismatch : ∀ (ctx : NamedCtx m) (scrut : Syn.Expr)
        (xL : String) (eL : Syn.Expr) (xR : String) (eR : Syn.Expr)
        (A B : Ty m)
        {Ψs scrutE ds fs}
        (C₁ C₂ : Ty m) {qℓ qr}
        {Ψₗ eLE dL fL Ψᵣ eRE dR fR err}
      → tcInfer ctx scrut ≡ success (A Once.Spec.Type.+ B) Ψs scrutE ds fs
      → tcInfer (extendNamedCtx ctx xL A) eL
          ≡ success C₁ (qℓ SCx.∷ Ψₗ) eLE dL fL
      → tcInfer (extendNamedCtx ctx xR B) eR
          ≡ success C₂ (qr SCx.∷ Ψᵣ) eRE dR fR
      → ¬ Once.Type.Join.UB C₁ C₂
      → tcInfer ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
      → err ≡ CaseBranchMismatch

    -- Plan 0.4 T1, change 1 (2026-04-30): the
    -- `tc-err-app-domain-mismatch` field was REMOVED. The
    -- elaborator no longer emits `ApplicationTypeMismatch` for
    -- RApp domain mismatches — under the bidirectional rule, a
    -- domain mismatch surfaces as whatever error `tcCheck ctx x A`
    -- returns (typically `TypeMismatch A inferred-type`). The
    -- corresponding `app-domain-mismatch-is-…` lemma in
    -- `ErrorProofs.agda` was retired for the same reason.

    -- Previously-blocked: RLam with a body usage that violates the
    -- arrow's declared grade → UsageViolation.
    tc-err-lam-usage-violation : ∀ (ctx : NamedCtx m) (x : String) (body : Syn.Expr)
        (A : Ty m) (q : _) (B : Ty m)
        (q' : _) {Ψ' eE' d' f' err}
      → tcCheck (extendNamedCtx ctx x A) body B
          ≡ success (q' SCx.∷ Ψ') eE' d' f'
      → Once.TypeCheck.Elaborate.decideLeq q' q ≡ nothing
      → tcCheck ctx (RLam x body) (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind q Once.Spec.Grade.pure ] B) ≡ failure err
      → err ≡ UsageViolation x q q'

    -- Previously-blocked: BinOp's operand sub-error is wrapped in
    -- BinOpLeftError or BinOpRightError.
    -- PLAN 0.75 F4: the hypothesis is `notNumeric`, not `asInt`'s failure.
    -- `Float` is a good binop operand now, so "the left operand is not `Int`"
    -- no longer implies a LEFT error — `1.5 + "x"` is a RIGHT error. The
    -- claim is unchanged for every type it still covers; only the type it
    -- covers changed, and it changed because the language did.
    tc-err-binop-left-wraps : ∀ (ctx : NamedCtx m) (op : BinOp) (e₁ e₂ : Syn.Expr)
        {sub-err outer-err}
      → Once.TypeCheck.Elaborate.notNumeric (tcInfer ctx e₁) ≡ just sub-err
      → tcInfer ctx (RBinOp op e₁ e₂) ≡ failure outer-err
      → outer-err ≡ BinOpLeftError sub-err

    tc-err-binop-right-wraps : ∀ (ctx : NamedCtx m) (op : BinOp) (e₁ e₂ : Syn.Expr)
        {Ψ₁ e₁E d₁ f₁ sub-err outer-err}
      → Once.TypeCheck.Elaborate.asInt (tcInfer ctx e₁)
          ≡ Once.TypeCheck.Elaborate.isInt Ψ₁ e₁E d₁ f₁
      → Once.TypeCheck.Elaborate.asInt (tcInfer ctx e₂)
          ≡ Once.TypeCheck.Elaborate.notInt sub-err
      → tcInfer ctx (RBinOp op e₁ e₂) ≡ failure outer-err
      → outer-err ≡ BinOpRightError sub-err

    -- G4 exhaustive per-Type coverage. (D229 / plan 0.94 §13: a `Void` operand
    -- is ex falso, not an error, so it has no error shape here.)



    -- Exhaustive per-Type G4 wiring (Float, Buffer, Sum, Product, Fun).
    tc-err-fst-non-pair-Float : ∀ (ctx : NamedCtx m) (arg : Syn.Expr) {Ψ' eE' d' f' err}
      → tcInfer ctx arg ≡ success Once.Spec.Type.Float Ψ' eE' d' f'
      → tcInfer ctx (RApp (RResolved (gen "fst")) arg) ≡ failure err
      → err ≡ FstNeedsPair

    tc-err-snd-non-pair-Float : ∀ (ctx : NamedCtx m) (arg : Syn.Expr) {Ψ' eE' d' f' err}
      → tcInfer ctx arg ≡ success Once.Spec.Type.Float Ψ' eE' d' f'
      → tcInfer ctx (RApp (RResolved (gen "snd")) arg) ≡ failure err
      → err ≡ SndNeedsPair

    tc-err-neg-non-Int-Float : ∀ (ctx : NamedCtx m) (e : Syn.Expr) {Ψ' eE' d' f' err}
      → tcInfer ctx e ≡ success Once.Spec.Type.Float Ψ' eE' d' f'
      → tcInfer ctx (RNeg e) ≡ failure err
      → err ≡ TypeMismatch {0} Once.Spec.Type.Int Once.Spec.Type.Float

    tc-err-case-scrut-Float : ∀ (ctx : NamedCtx m) (scrut : Syn.Expr) (xL : String) (eL : Syn.Expr)
        (xR : String) (eR : Syn.Expr) {Ψ' eE' d' f' err}
      → tcInfer ctx scrut ≡ success Once.Spec.Type.Float Ψ' eE' d' f'
      → tcInfer ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
      → err ≡ CaseScrutineeNotSum

    -- RApp polymorphic builtin specialisations
    ----------------------------------------------------------------
    -- G2 (completeness direction): if the elaborator's sub-expressions
    -- succeed (from IHs), the outer elaborator succeeds: the steps
    -- `tcCheck-complete` composes.
    ----------------------------------------------------------------

    tcInfer-complete-RInt : ∀ (ctx : NamedCtx m) (n : ℤ)
      → ∃[ eE ] ∃[ d ] ∃[ f ]
          tcInfer ctx (RInt n) ≡ success Once.Spec.Type.Int Surface.zeroUsage eE d f

    tcInfer-complete-RUnit : ∀ (ctx : NamedCtx m)
      → ∃[ eE ] ∃[ d ] ∃[ f ]
          tcInfer ctx RUnit ≡ success Once.Spec.Type.Unit Surface.zeroUsage eE d f


    tcInfer-complete-RVar-unit : ∀ (ctx : NamedCtx m)
      → ∃[ eE ] ∃[ d ] ∃[ f ]
          tcInfer ctx (RResolved (gen "unit")) ≡ success Once.Spec.Type.Unit Surface.zeroUsage eE d f

    -- RPair: both subs infer → outer succeeds.
    tcInfer-complete-RPair : ∀ (ctx : NamedCtx m) (a b : Syn.Expr) {A B : Ty m}
        {Ψ₁ Ψ₂ : Surface.Usage (Classify.NamedCtx.size ctx)}
        {aE : SExpr (Classify.NamedCtx.debruijn ctx) Ψ₁ A}
        {bE : SExpr (Classify.NamedCtx.debruijn ctx) Ψ₂ B}
        {dA dB fA fB : _}
      → tcInfer ctx a ≡ success A Ψ₁ aE dA fA
      → tcInfer ctx b ≡ success B Ψ₂ bE dB fB
      → ∃[ eE ] ∃[ d ] ∃[ f ]
          tcInfer ctx (RPair a b) ≡ success (A Once.Spec.Type.* B) (Ψ₁ Surface.+ᵘ Ψ₂) eE d f

    -- RNeg: sub at Int → outer success at Int.
    tcInfer-complete-RNeg : ∀ (ctx : NamedCtx m) (e : Syn.Expr)
        {Ψ : Surface.Usage (Classify.NamedCtx.size ctx)}
        {eE' : SExpr (Classify.NamedCtx.debruijn ctx) Ψ Once.Spec.Type.Int}
        {d' f' : _}
      → tcInfer ctx e ≡ success Once.Spec.Type.Int Ψ eE' d' f'
      → ∃[ eE ] ∃[ d ] ∃[ f ]
          tcInfer ctx (RNeg e) ≡ success Once.Spec.Type.Int Ψ eE d f

    -- RAnnot: check-mode sub success → infer-mode success.
    tcInfer-complete-RAnnot : ∀ (ctx : NamedCtx m) (e : Syn.Expr) (T : Type)
        {Ψ : Surface.Usage (Classify.NamedCtx.size ctx)}
        {eE' : SExpr (Classify.NamedCtx.debruijn ctx) Ψ (wk₀ T)}
        {d' f' : _}
      → tcCheck ctx e (wk₀ T) ≡ success Ψ eE' d' f'
      → ∃[ eE ] ∃[ d ] ∃[ f ]
          tcInfer ctx (RAnnot e T) ≡ success (wk₀ T) Ψ eE d f

    -- RLet: sub₁ + extended-context sub₂ both infer → outer success.
    tcInfer-complete-RLet : ∀ (ctx : NamedCtx m) (x : String) (e₁ e₂ : Syn.Expr)
        {A B : Ty m} {q : _}
        {Ψ₁ Ψ₂ : Surface.Usage (Classify.NamedCtx.size ctx)}
        {e₁E : SExpr (Classify.NamedCtx.debruijn ctx) Ψ₁ A}
        {e₂E : SExpr (Classify.NamedCtx.debruijn (extendNamedCtx ctx x A))
                     (q SCx.∷ Ψ₂) B}
        {d₁ d₂ f₁ f₂ : _}
      → tcInfer ctx e₁ ≡ success A Ψ₁ e₁E d₁ f₁
      → tcInfer (extendNamedCtx ctx x A) e₂
          ≡ success B (q SCx.∷ Ψ₂) e₂E d₂ f₂
      → ∃[ eE ] ∃[ d ] ∃[ f ]
          tcInfer ctx (RLet x e₁ e₂)
            ≡ success B (Ψ₂ Surface.+ᵘ (q Surface.*ᵘ Ψ₁)) eE d f

    -- RApp polymorphic builtin completenesses
    tcInfer-complete-RApp-id : ∀ (ctx : NamedCtx m) (arg : Syn.Expr) {T : Ty m}
        {Ψ : Surface.Usage (Classify.NamedCtx.size ctx)}
        {argE : SExpr (Classify.NamedCtx.debruijn ctx) Ψ T}
        {d' f' : _}
      → tcInfer ctx arg ≡ success T Ψ argE d' f'
      → ∃[ eE ] ∃[ d ] ∃[ f ]
          tcInfer ctx (RApp (RResolved (gen "id")) arg)
            ≡ success T (Surface.zeroUsage Surface.+ᵘ (Once.Spec.Grade.Many Surface.*ᵘ Ψ)) eE d f

    tcInfer-complete-RApp-fst : ∀ (ctx : NamedCtx m) (arg : Syn.Expr) {A B : Ty m}
        {Ψ : Surface.Usage (Classify.NamedCtx.size ctx)}
        {argE : SExpr (Classify.NamedCtx.debruijn ctx) Ψ (A Once.Spec.Type.* B)}
        {d' f' : _}
      → tcInfer ctx arg ≡ success (A Once.Spec.Type.* B) Ψ argE d' f'
      → ∃[ eE ] ∃[ d ] ∃[ f ]
          tcInfer ctx (RApp (RResolved (gen "fst")) arg)
            ≡ success A (Surface.zeroUsage Surface.+ᵘ (Once.Spec.Grade.Many Surface.*ᵘ Ψ)) eE d f

    tcInfer-complete-RApp-snd : ∀ (ctx : NamedCtx m) (arg : Syn.Expr) {A B : Ty m}
        {Ψ : Surface.Usage (Classify.NamedCtx.size ctx)}
        {argE : SExpr (Classify.NamedCtx.debruijn ctx) Ψ (A Once.Spec.Type.* B)}
        {d' f' : _}
      → tcInfer ctx arg ≡ success (A Once.Spec.Type.* B) Ψ argE d' f'
      → ∃[ eE ] ∃[ d ] ∃[ f ]
          tcInfer ctx (RApp (RResolved (gen "snd")) arg)
            ≡ success B (Surface.zeroUsage Surface.+ᵘ (Once.Spec.Grade.Many Surface.*ᵘ Ψ)) eE d f

    tcInfer-complete-RApp-terminal : ∀ (ctx : NamedCtx m) (arg : Syn.Expr) {T : Ty m}
        {Ψ : Surface.Usage (Classify.NamedCtx.size ctx)}
        {argE : SExpr (Classify.NamedCtx.debruijn ctx) Ψ T}
        {d' f' : _}
      → tcInfer ctx arg ≡ success T Ψ argE d' f'
      → ∃[ eE ] ∃[ d ] ∃[ f ]
          tcInfer ctx (RApp (RResolved (gen "terminal")) arg)
            ≡ success Once.Spec.Type.Unit (Surface.zeroUsage Surface.+ᵘ (Once.Spec.Grade.Many Surface.*ᵘ Ψ)) eE d f

    -- RVar local and import
    tcInfer-complete-RVar-local : ∀ (ctx : NamedCtx m) (x : String) {A : Ty m}
        {Ψ : Surface.Usage (Classify.NamedCtx.size ctx)}
        {eE' : Surface.SVar (Classify.NamedCtx.debruijn ctx) Ψ A}
      → lookupLocal ctx x ≡ just (A , Ψ , eE')
      → ∃[ eE ] ∃[ d ] ∃[ f ]
          tcInfer ctx (RVar x) ≡ success A Ψ eE d f


    -- RBinOp (arithmetic / comparison families)
    tcInfer-complete-RBinOp-arith : ∀ (ctx : NamedCtx m) (op : BinOp) (arithEq : Raw.isArithmeticOp op ≡ Data.Bool.true)
        (e₁ e₂ : Syn.Expr)
        {Ψ₁ Ψ₂ : Surface.Usage (Classify.NamedCtx.size ctx)}
        {e₁E : SExpr (Classify.NamedCtx.debruijn ctx) Ψ₁ Once.Spec.Type.Int}
        {e₂E : SExpr (Classify.NamedCtx.debruijn ctx) Ψ₂ Once.Spec.Type.Int}
        {d₁ d₂ f₁ f₂ : _}
      → tcInfer ctx e₁ ≡ success Once.Spec.Type.Int Ψ₁ e₁E d₁ f₁
      → tcInfer ctx e₂ ≡ success Once.Spec.Type.Int Ψ₂ e₂E d₂ f₂
      → ∃[ eE ] ∃[ d ] ∃[ f ]
          tcInfer ctx (RBinOp op e₁ e₂) ≡ success Once.Spec.Type.Int (Ψ₁ Surface.+ᵘ Ψ₂) eE d f

    tcInfer-complete-RBinOp-cmp : ∀ (ctx : NamedCtx m) (op : BinOp) (cmpEq : Raw.isComparisonOp op ≡ Data.Bool.true)
        (e₁ e₂ : Syn.Expr)
        {Ψ₁ Ψ₂ : Surface.Usage (Classify.NamedCtx.size ctx)}
        {e₁E : SExpr (Classify.NamedCtx.debruijn ctx) Ψ₁ Once.Spec.Type.Int}
        {e₂E : SExpr (Classify.NamedCtx.debruijn ctx) Ψ₂ Once.Spec.Type.Int}
        {d₁ d₂ f₁ f₂ : _}
      → tcInfer ctx e₁ ≡ success Once.Spec.Type.Int Ψ₁ e₁E d₁ f₁
      → tcInfer ctx e₂ ≡ success Once.Spec.Type.Int Ψ₂ e₂E d₂ f₂
      → ∃[ eE ] ∃[ d ] ∃[ f ]
          tcInfer ctx (RBinOp op e₁ e₂)
            ≡ success (Once.Spec.Type.Unit Once.Spec.Type.+ Once.Spec.Type.Unit) (Ψ₁ Surface.+ᵘ Ψ₂) eE d f

    -- RDestruct (case/sum elim)
    tcInfer-complete-RDestruct : ∀ (ctx : NamedCtx m) (scrut : Syn.Expr) (xL : String) (eL : Syn.Expr)
        (xR : String) (eR : Syn.Expr) {A B : Ty m}
        {Ψs : Surface.Usage (Classify.NamedCtx.size ctx)}
        {scrutE : SExpr (Classify.NamedCtx.debruijn ctx) Ψs (A Once.Spec.Type.+ B)}
        {ds fs : _}
        (C₁ C₂ C : Ty m) (J : Once.Spec.Sub._⊔_≔_ C₁ C₂ C) {qℓ qr : _}
        {Ψₗ : Surface.Usage (Classify.NamedCtx.size ctx)}
        {eLE : SExpr (Classify.NamedCtx.debruijn (extendNamedCtx ctx xL A))
                     (qℓ SCx.∷ Ψₗ) C₁}
        {dL fL : _}
        {Ψᵣ : Surface.Usage (Classify.NamedCtx.size ctx)}
        {eRE : SExpr (Classify.NamedCtx.debruijn (extendNamedCtx ctx xR B))
                     (qr SCx.∷ Ψᵣ) C₂}
        {dR fR : _}
      → tcInfer ctx scrut ≡ success (A Once.Spec.Type.+ B) Ψs scrutE ds fs
      → tcInfer (extendNamedCtx ctx xL A) eL
          ≡ success C₁ (qℓ SCx.∷ Ψₗ) eLE dL fL
      → tcInfer (extendNamedCtx ctx xR B) eR
          ≡ success C₂ (qr SCx.∷ Ψᵣ) eRE dR fR
      → ∃[ eE ] ∃[ d ] ∃[ f ]
          tcInfer ctx (Raw.RDestruct scrut xL eL xR eR)
            ≡ success C (Ψs Surface.+ᵘ (Ψₗ Surface.⊔ᵘ Ψᵣ)) eE d f

    -- Generic RApp.
    -- Plan 0.4 T1, change 1: x premise is now `tcCheck ctx x A`
    -- (matches the bidirectional inferElab rule).
    tcInfer-complete-RApp-generic : ∀ (ctx : NamedCtx m) (f x : Syn.Expr) (A : Ty m) {B : Ty m} {q : _}
        {Ψf : Surface.Usage (Classify.NamedCtx.size ctx)}
        {fE : SExpr (Classify.NamedCtx.debruijn ctx) Ψf (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind q Once.Spec.Grade.pure ] B)}
        {df ff : _}
        {Ψx : Surface.Usage (Classify.NamedCtx.size ctx)}
        {xE : SExpr (Classify.NamedCtx.debruijn ctx) Ψx A}
        {dx fx : _}
      → Classify.classifyAppHead f ≡ nothing
      → tcInfer ctx f ≡ success (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind q Once.Spec.Grade.pure ] B) Ψf fE df ff
      → tcCheck ctx x A ≡ success Ψx xE dx fx
      → ∃[ eE ] ∃[ d ] ∃[ f' ]
          tcInfer ctx (RApp f x) ≡ success B (Ψf Surface.+ᵘ (q Surface.*ᵘ Ψx)) eE d f'

    -- Check-mode RLam
    tcCheck-complete-RLam : ∀ (ctx : NamedCtx m) (x : String) (body : Syn.Expr)
        (A : Ty m) (q q' : _) (B : Ty m)
        {Ψ' : Surface.Usage (Classify.NamedCtx.size ctx)}
        {eE' : SExpr (Classify.NamedCtx.debruijn (extendNamedCtx ctx x A))
                     (q' SCx.∷ Ψ') B}
        {d' f' : _} {π : Once.Spec.Grade.Purity}
      → (q' Once.Type.Grade.≤qᵇ q) ≡ Data.Bool.true
      → Once.Spec.Grade._⊑π_ Once.Spec.Grade.pure π
      → tcCheck (extendNamedCtx ctx x A) body B
          ≡ success (q' SCx.∷ Ψ') eE' d' f'
      → ∃[ eE ] ∃[ d ] ∃[ f ]
          tcCheck ctx (RLam x body) (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind q π ] B) ≡ success Ψ' eE d f

    ----------------------------------------------------------------
    -- G7 (first pass): algebraic identities
    ----------------------------------------------------------------

    id-decideLeq-iff : ∀ (q' q : _)
      → ((q' Once.Type.Grade.≤qᵇ q) ≡ Data.Bool.true
          → ∃[ p ] Once.TypeCheck.Elaborate.decideLeq q' q ≡ just p)
      × (∀ {p} → Once.TypeCheck.Elaborate.decideLeq q' q ≡ just p
             → (q' Once.Type.Grade.≤qᵇ q) ≡ Data.Bool.true)

    id-binop-classification-exhaustive : ∀ (op : BinOp)
      → (Raw.isArithmeticOp op ≡ Data.Bool.true)
      ⊎ (Raw.isComparisonOp op ≡ Data.Bool.true)

    id-binop-classification-exclusive : ∀ (op : BinOp)
      → Raw.isArithmeticOp op ≡ Data.Bool.true
      → Raw.isComparisonOp op ≡ Data.Bool.true
      → Data.Empty.⊥

    id-≤q-refl : ∀ (q : _) → (q Once.Type.Grade.≤qᵇ q) ≡ Data.Bool.true

    id-≤q-trans : ∀ (q₁ q₂ q₃ : _)
      → (q₁ Once.Type.Grade.≤qᵇ q₂) ≡ Data.Bool.true
      → (q₂ Once.Type.Grade.≤qᵇ q₃) ≡ Data.Bool.true
      → (q₁ Once.Type.Grade.≤qᵇ q₃) ≡ Data.Bool.true

    id-Zero-≤q-all : ∀ (q : _) → (Once.Spec.Grade.Zero Once.Type.Grade.≤qᵇ q) ≡ Data.Bool.true

    id-all-≤q-Many : ∀ (q : _) → (q Once.Type.Grade.≤qᵇ Once.Spec.Grade.Many) ≡ Data.Bool.true

    -- Quantity algebra
    id-+q-comm : ∀ (q₁ q₂ : _) → q₁ Once.Spec.Grade.+q q₂ ≡ q₂ Once.Spec.Grade.+q q₁
    id-+q-assoc : ∀ (q₁ q₂ q₃ : _)
                → q₁ Once.Spec.Grade.+q (q₂ Once.Spec.Grade.+q q₃)
                  ≡ (q₁ Once.Spec.Grade.+q q₂) Once.Spec.Grade.+q q₃
    id-*q-distrib-+q : ∀ (q₁ q₂ q₃ : _) → q₁ Once.Spec.Grade.*q (q₂ Once.Spec.Grade.+q q₃)
                        ≡ (q₁ Once.Spec.Grade.*q q₂) Once.Spec.Grade.+q (q₁ Once.Spec.Grade.*q q₃)
    id-⊔q-comm : ∀ (q₁ q₂ : _) → q₁ Once.Type.Grade.⊔q q₂ ≡ q₂ Once.Type.Grade.⊔q q₁
    id-⊔q-idem : ∀ (q : _) → q Once.Type.Grade.⊔q q ≡ q

    -- Usage-vector algebra
    id-+ᵘ-comm : ∀ {n} (Ψ₁ Ψ₂ : Once.Spec.Context.Usage n)
                → Ψ₁ Surface.+ᵘ Ψ₂ ≡ Ψ₂ Surface.+ᵘ Ψ₁
    id-+ᵘ-assoc : ∀ {n} (Ψ₁ Ψ₂ Ψ₃ : Once.Spec.Context.Usage n)
                 → Ψ₁ Surface.+ᵘ (Ψ₂ Surface.+ᵘ Ψ₃)
                   ≡ (Ψ₁ Surface.+ᵘ Ψ₂) Surface.+ᵘ Ψ₃
    id-⊔ᵘ-comm : ∀ {n} (Ψ₁ Ψ₂ : Once.Spec.Context.Usage n)
                → Ψ₁ Surface.⊔ᵘ Ψ₂ ≡ Ψ₂ Surface.⊔ᵘ Ψ₁
    id-⊔ᵘ-idem : ∀ {n} (Ψ : Once.Spec.Context.Usage n) → Ψ Surface.⊔ᵘ Ψ ≡ Ψ
    id-*ᵘ-identity-One : ∀ {n} (Ψ : Once.Spec.Context.Usage n)
                       → Once.Spec.Grade.One Surface.*ᵘ Ψ ≡ Ψ
    id-+ᵘ-identity-left : ∀ {n} (Ψ : Once.Spec.Context.Usage n)
                        → Surface.zeroUsage Surface.+ᵘ Ψ ≡ Ψ

    -- The grade algebra as the structures it is (plan 0.112 B2–B4): the
    -- identities above are instances of these laws.
    grade-semiring   : Algebra.Structures.IsCommutativeSemiring {A = Once.Spec.Grade.Quantity} _≡_
                         Once.Spec.Grade._+q_ Once.Spec.Grade._*q_
                         Once.Spec.Grade.Zero Once.Spec.Grade.One
    grade-join       : Algebra.Structures.IsCommutativeBand {A = Once.Spec.Grade.Quantity} _≡_
                         Once.Type.Grade._⊔q_
    grade-order      : Relation.Binary.Structures.IsDecTotalOrder {A = Once.Spec.Grade.Quantity} _≡_
                         Once.Spec.Grade._≤q_
    effect-monoid    : Algebra.Structures.IsCommutativeMonoid {A = Once.Spec.Grade.Purity} _≡_
                         Once.Spec.Grade._·p_ Once.Spec.Grade.pure
    usage-semimodule : ∀ {n} → Algebra.Module.Structures.IsLeftSemimodule GM.quantity-semiring _≡_
                         (Once.Spec.Context._+ᵘ_ {n}) Once.Spec.Context.zeroUsage Once.Spec.Context._*ᵘ_
    usage-join       : ∀ {n} → Algebra.Structures.IsCommutativeBand {A = Once.Spec.Context.Usage n} _≡_
                         Once.Context._⊔ᵘ_
    -- The orders are partial orders (plan 0.112 B6).
    subtype-order    : Relation.Binary.Structures.IsPartialOrder {A = Ty m} _≡_ Once.Spec.Sub._<:_
    effect-order     : Relation.Binary.Structures.IsPartialOrder {A = Once.Spec.Grade.Purity} _≡_
                         Once.Spec.Grade._⊑π_
    usage-order      : ∀ {n} → Relation.Binary.Structures.IsPartialOrder {A = Once.Spec.Context.Usage n} _≡_
                         Once.Spec.Context._⊑ᵘ_

    ----------------------------------------------------------------
    -- Grammar connection: the surface-grammar spec round-trips
    -- through the internal `Type` representation on its expressible
    -- fragment. Pins the parser's output to the formal grammar.
    ----------------------------------------------------------------

    grammar-to-type-roundtrip : ∀ (g : GType) (t : Type)
      → gtypeToType g ≡ just t
      → typeToGType t ≡ just g

    type-to-grammar-roundtrip : ∀ (t : Type) (g : GType)
      → typeToGType t ≡ just g
      → gtypeToType g ≡ just t

------------------------------------------------------------------------
-- The inhabitant
--
-- Constructing this value is the single enforcement point: every
-- field below must be filled. Agda rejects the definition if any
-- proof is missing or incorrect.
------------------------------------------------------------------------

-- A success's witness, read off the verified result.
private
  infer-sound : ∀ {m} (ctx : NamedCtx m) (e : Syn.Expr) {A Ψ eE d f}
              → inferElab ctx e ≡ success A Ψ eE d f → WI ctx e A Ψ eE
  infer-sound ctx e = go (inferElabV ctx e)
    where
      go : ∀ {A Ψ eE d f} (r : VerifiedInferResult ctx e) → proj₁ r ≡ success A Ψ eE d f → WI ctx e A Ψ eE
      go (success _ _ _ _ _ , w) refl = w

  check-sound : ∀ {m} (ctx : NamedCtx m) (e : Syn.Expr) (T : Ty m) {Ψ eE d f}
              → checkElab ctx e T ≡ success Ψ eE d f → WC ctx e T Ψ eE
  check-sound ctx e T = go (checkElabV ctx e T)
    where
      go : ∀ {Ψ eE d f} (r : VerifiedCheckResult ctx e T) → proj₁ r ≡ success Ψ eE d f → WC ctx e T Ψ eE
      go (success _ _ _ _ , w) refl = w

verifiedTypeChecker : ∀ {m} → VerifiedTypeChecker {m}
verifiedTypeChecker = record
  { tcInfer                   = inferElab
  ; tcCheck                   = checkElab
  ; tcInfer-refl              = Det.inferElab-refl
  ; tcCheck-refl              = Det.checkElab-refl
  ; tcInfer-cong              = Det.inferElab-cong
  ; tcCheck-cong              = Det.checkElab-cong
  ; tcInfer-total             = Tot.inferElab-total
  ; tcCheck-total             = Tot.checkElab-total
  ; tcInfer-sound                 = infer-sound
  ; tcCheck-sound                 = check-sound
  ; tcCheck-complete              = CS.check-completeS
  ; tcInfer-complete              = CS.infer-completeS
  ; tc-err-lam-infer              = EP.lam-infer-is-LambdaInInferMode
  ; tc-err-inl-infer              = EP.inl-app-infer-is-InlInInferMode
  ; tc-err-inr-infer              = EP.inr-app-infer-is-InrInInferMode
  ; tc-err-initial-infer          = EP.initial-app-infer-is-InitialInInferMode
  ; tc-err-qualified-unbound      = EP.qualified-not-found-is-UnboundQualified
  ; tc-err-fst-non-pair-Unit      = EP.fst-non-pair-Unit
  ; tc-err-fst-non-pair-Int       = EP.fst-non-pair-Int
  ; tc-err-neg-non-Int-Unit       = EP.neg-non-Int-Unit
  ; tc-err-var-unbound            = EP.var-unbound-is-UnboundVariable
  ; tc-err-snd-non-pair-Unit      = EP.snd-non-pair-Unit
  ; tc-err-snd-non-pair-Int       = EP.snd-non-pair-Int
  ; tc-err-case-scrut-Unit        = EP.case-scrut-Unit
  ; tc-err-case-scrut-Int         = EP.case-scrut-Int
  ; tc-err-lam-usage-violation    = EP.lam-usage-violation-is-UsageViolation
  ; tc-err-binop-left-wraps       = EP.binop-left-err-wraps
  ; tc-err-binop-right-wraps      = EP.binop-right-err-wraps
  ; tc-err-fst-non-pair-Float     = EP.fst-non-pair-Float
  ; tc-err-snd-non-pair-Float     = EP.snd-non-pair-Float
  ; tc-err-neg-non-Int-Float      = EP.neg-non-Int-Float
  ; tc-err-case-scrut-Float       = EP.case-scrut-Float
  ; tc-err-case-branch-mismatch   = EP.case-branch-mismatch-is-CaseBranchMismatch
  ; tc-err-check-RInt-type-mismatch  = EP.check-RInt-type-mismatch
  ; tc-err-check-RUnit-type-mismatch = EP.check-RUnit-type-mismatch
  ; tcInfer-complete-RInt         = λ ctx n → CmpR.infer-complete-RInt {ctx = ctx} n
  ; tcInfer-complete-RUnit        = λ ctx → CmpR.infer-complete-RUnit {ctx = ctx}
  ; tcInfer-complete-RVar-unit    = λ ctx → CmpR.infer-complete-RVar-unit {ctx = ctx}
  ; tcInfer-complete-RPair        = λ ctx → CmpR.infer-complete-RPair
  ; tcInfer-complete-RNeg = λ ctx → CmpR.infer-complete-RNeg
  ; tcInfer-complete-RAnnot       = λ ctx → CmpR.infer-complete-RAnnot
  ; tcInfer-complete-RLet         = λ ctx → CmpR.infer-complete-RLet
  ; tcInfer-complete-RApp-id      = λ ctx → CmpR.infer-complete-RApp-id
  ; tcInfer-complete-RApp-fst     = λ ctx → CmpR.infer-complete-RApp-fst
  ; tcInfer-complete-RApp-snd     = λ ctx → CmpR.infer-complete-RApp-snd
  ; tcInfer-complete-RApp-terminal = λ ctx → CmpR.infer-complete-RApp-terminal
  ; tcInfer-complete-RVar-local   = λ ctx → CmpR.infer-complete-RVar-local {ctx = ctx}
  ; tcInfer-complete-RBinOp-arith = λ ctx → CmpR.infer-complete-RBinOp-arith
  ; tcInfer-complete-RBinOp-cmp   = λ ctx → CmpR.infer-complete-RBinOp-cmp
  ; tcInfer-complete-RDestruct    = λ ctx → CmpR.infer-complete-RDestruct
  ; tcInfer-complete-RApp-generic = λ ctx → CmpR.infer-complete-RApp-generic
  ; tcCheck-complete-RLam         = CmpR.check-complete-RLam
  ; id-decideLeq-iff              = λ q' q → Id.decideLeq-correct-true q' q , Id.decideLeq-correct-just q' q
  ; id-binop-classification-exhaustive = Id.binop-classification-exhaustive
  ; id-binop-classification-exclusive  = Id.binop-classification-exclusive
  ; id-≤q-refl                    = Id.≤q-refl
  ; id-≤q-trans                   = Id.≤q-trans
  ; id-Zero-≤q-all                = Id.Zero-≤q-all
  ; id-all-≤q-Many                = Id.all-≤q-Many
  ; id-+q-comm                    = Id.+q-comm
  ; id-+q-assoc                   = Id.+q-assoc
  ; id-*q-distrib-+q              = Id.*q-distrib-+q-left
  ; id-⊔q-comm                    = Id.⊔q-comm
  ; id-⊔q-idem                    = Id.⊔q-idem
  ; id-+ᵘ-comm                    = Id.+ᵘ-comm
  ; id-+ᵘ-assoc                   = Id.+ᵘ-assoc
  ; id-⊔ᵘ-comm                    = Id.⊔ᵘ-comm
  ; id-⊔ᵘ-idem                    = Id.⊔ᵘ-idem
  ; id-*ᵘ-identity-One            = Id.*ᵘ-identity-One
  ; id-+ᵘ-identity-left           = Id.+ᵘ-identity-left
  ; grade-semiring                = Grade.quantity-isCommutativeSemiring
  ; grade-join                    = Grade.quantity-⊔-isCommutativeBand
  ; grade-order                   = Grade.quantity-≤-isDecTotalOrder
  ; effect-monoid                 = Grade.purity-isCommutativeMonoid
  ; usage-semimodule              = GM.usage-isLeftSemimodule
  ; usage-join                    = GM.usage-⊔-isCommutativeBand
  ; subtype-order                 = Ord.subtype-isPartialOrder
  ; effect-order                  = Ord.purity-⊑-isPartialOrder
  ; usage-order                   = Ord.usage-⊑-isPartialOrder
  ; grammar-to-type-roundtrip = Conv.gtypeToType-typeToGType
  ; type-to-grammar-roundtrip = Conv.typeToGType-gtypeToType
  }
