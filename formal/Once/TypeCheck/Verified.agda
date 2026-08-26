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

module Once.TypeCheck.Verified where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; ∃; ∃-syntax)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (Type)
open import Once.Functor.Translate using (IsConcrete)
import Once.Type
import Once.Surface.Syntax
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.TypeCheck.Elaborate
  using (NamedCtx; inferElab; checkElab; InferElabResult; CheckElabResult;
         success; failure; extendNamedCtx; lookupImport; lookupLocal)
open import Data.Maybe using (Maybe; nothing)

open import Data.Integer using (ℤ)
open import Data.Sum using (_⊎_)
import Data.String
import Data.Bool
import Data.Empty

import Once.TypeCheck.Determinism  as Det
import Once.TypeCheck.Totality     as Tot
import Once.TypeCheck.Soundness    as Snd
import Once.TypeCheck.Completeness as Cmp
import Once.TypeCheck.ErrorProofs  as EP
import Once.TypeCheck.Identities   as Id
open import Once.TypeCheck.Judgment using (_⊢_∶_⨾_; _⊢ᵢ_∶_⨾_; _⊢ᶜ_∶_⨾_)
open import Once.TypeCheck.Error using (TypeError; renderError;
  LambdaInInferMode; InlInInferMode; InrInInferMode; InitialInInferMode;
  UnboundQualified; UnboundVariable; FstNeedsPair; SndNeedsPair;
  NegationNotInt; CaseScrutineeNotSum; CaseBranchMismatch;
  ApplicationTypeMismatch; TypeMismatch; UsageViolation;
  BinOpLeftError; BinOpRightError)
open import Relation.Nullary using (¬_)
open import Once.TypeCheck.Raw as Raw using (RawExpr; RInt; RStringLit; RUnit; RVar; RQualified; RAnnot; RPair; RLet; RDestruct; RUnaryOp; RBinOp; OpNeg; RLam; RApp; BinOp)
open import Data.String using (String)
import Once.Grammar.Convert       as Conv
open import Once.Grammar using (GType)
open Conv using (typeToGType; gtypeToType)
open Tot  using (IsInferSuccess; IsInferFailure;
                 IsCheckSuccess; IsCheckFailure)

open import Once.Surface.Syntax as Surface using ()
  renaming (Expr to SExpr)

------------------------------------------------------------------------
-- Record: the compiler front-end + its proof obligations
------------------------------------------------------------------------

record VerifiedTypeChecker : Set₁ where
  field
    ----------------------------------------------------------------
    -- Implementations
    ----------------------------------------------------------------

    -- | Inference-mode type-checker / elaborator.
    tcInfer : (ctx : NamedCtx) (e : RawExpr)
            → InferElabResult (NamedCtx.debruijn ctx)

    -- | Check-mode type-checker / elaborator.
    tcCheck : (ctx : NamedCtx) (e : RawExpr) (T : Type)
            → CheckElabResult (NamedCtx.debruijn ctx) T

    ----------------------------------------------------------------
    -- G6: determinism — the type-checker is a pure function of its
    -- inputs. (plans/0.3-frontend-verification-gaps.md, gap G6.)
    ----------------------------------------------------------------

    tcInfer-refl : ∀ (ctx : NamedCtx) (e : RawExpr)
                 → tcInfer ctx e ≡ tcInfer ctx e

    tcCheck-refl : ∀ (ctx : NamedCtx) (e : RawExpr) (T : Type)
                 → tcCheck ctx e T ≡ tcCheck ctx e T

    tcInfer-cong : ∀ (ctx : NamedCtx) {e₁ e₂ : RawExpr}
                 → e₁ ≡ e₂ → tcInfer ctx e₁ ≡ tcInfer ctx e₂

    tcCheck-cong : ∀ (ctx : NamedCtx) (T : Type) {e₁ e₂ : RawExpr}
                 → e₁ ≡ e₂ → tcCheck ctx e₁ T ≡ tcCheck ctx e₂ T

    ----------------------------------------------------------------
    -- G3: totality — every input produces either a well-formed
    -- success or a failure (no third possibility).
    -- (plans/0.3-frontend-verification-gaps.md, gap G3.)
    ----------------------------------------------------------------

    tcInfer-total : ∀ (ctx : NamedCtx) (e : RawExpr)
                  → IsInferSuccess (tcInfer ctx e)
                  ⊎ IsInferFailure (tcInfer ctx e)

    tcCheck-total : ∀ (ctx : NamedCtx) (e : RawExpr) (T : Type)
                  → IsCheckSuccess (tcCheck ctx e T)
                  ⊎ IsCheckFailure (tcCheck ctx e T)

    ----------------------------------------------------------------
    -- Plan 0.4 T0 (2026-04-30): top-level soundness theorems.
    --
    -- These two fields enforce that EVERY successful elaborator
    -- result has a corresponding judgment derivation. Adding a new
    -- elaborator code path without a matching judgment rule will
    -- fail to inhabit these fields, forcing spec/impl to stay in
    -- sync. Per-shape lemmas below remain for fine-grained reuse.
    ----------------------------------------------------------------

    tcInfer-sound : ∀ (ctx : NamedCtx) (e : RawExpr)
      {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
      {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : _}
      → tcInfer ctx e ≡ success A Ψ eE d f
      → ctx ⊢ e ∶ A ⨾ Ψ

    tcCheck-sound : ∀ (ctx : NamedCtx) (e : RawExpr) (T : Type)
      {Ψ : Surface.Usage (NamedCtx.size ctx)}
      {eE : SExpr (NamedCtx.debruijn ctx) Ψ T} {d f : _}
      → tcCheck ctx e T ≡ success Ψ eE d f
      → ctx ⊢ᶜ e ∶ T ⨾ Ψ

    ----------------------------------------------------------------
    -- G2 (partial): per-shape soundness lemmas — kept for
    -- fine-grained reuse alongside the global theorems above.
    -- Adding new per-shape lemmas remains valuable; the global
    -- theorem composes them.
    ----------------------------------------------------------------

    tcInfer-sound-RInt :
      ∀ (ctx : NamedCtx) (n : ℤ)
        {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
        {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : _}
      → tcInfer ctx (RInt n) ≡ success A Ψ eE d f
      → ctx ⊢ RInt n ∶ A ⨾ Ψ

    tcInfer-sound-RStringLit :
      ∀ (ctx : NamedCtx) (s : _)
        {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
        {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : _}
      → tcInfer ctx (RStringLit s) ≡ success A Ψ eE d f
      → ctx ⊢ RStringLit s ∶ A ⨾ Ψ

    tcInfer-sound-RUnit :
      ∀ (ctx : NamedCtx)
        {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
        {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : _}
      → tcInfer ctx RUnit ≡ success A Ψ eE d f
      → ctx ⊢ RUnit ∶ A ⨾ Ψ

    tcInfer-sound-RVar-unit :
      ∀ (ctx : NamedCtx)
        {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
        {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : _}
      → tcInfer ctx (RVar "unit") ≡ success A Ψ eE d f
      → ctx ⊢ RVar "unit" ∶ A ⨾ Ψ

    -- Full RVar soundness: covers the `"unit"` builtin path, local
    -- bindings, and import lookup — unblocked by refactoring the
    -- elaborator to use decidable equality on `x ≟ "unit"` instead
    -- of a literal string pattern.
    tcInfer-sound-RVar :
      ∀ (ctx : NamedCtx) (x : String)
        {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
        {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : _}
      → tcInfer ctx (RVar x) ≡ success A Ψ eE d f
      → ctx ⊢ RVar x ∶ A ⨾ Ψ

    -- Recursive RawExpr cases: soundness is parameterised by an IH
    -- for the sub-expression(s). A top-level structural recursion
    -- over RawExpr stitches these lemmas together — omitted here
    -- for modularity but trivial to assemble.
    tcInfer-sound-RUnaryOp-neg :
      ∀ (ctx : NamedCtx) (e : RawExpr)
        {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
        {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : _}
      → (IH : ∀ {A' Ψ' eE' d' f'}
            → tcInfer ctx e ≡ success A' Ψ' eE' d' f'
            → ctx ⊢ e ∶ A' ⨾ Ψ')
      → tcInfer ctx (RUnaryOp OpNeg e) ≡ success A Ψ eE d f
      → ctx ⊢ RUnaryOp OpNeg e ∶ A ⨾ Ψ

    -- Plan 0.4 T0 (2026-04-30): IH now gives ⊢ᶜ (matches what
    -- check-sound returns). Previously claimed to give ⊢ᵢ from a
    -- checkElab success — a direction mismatch that no real
    -- caller could satisfy. Surfaced when scaffolding infer-sound.
    tcInfer-sound-RAnnot :
      ∀ (ctx : NamedCtx) (e : RawExpr) (T : Type)
        {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
        {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : _}
      → (IH : ∀ {Ψ' eE' d' f'}
            → tcCheck ctx e T ≡ success Ψ' eE' d' f'
            → ctx ⊢ᶜ e ∶ T ⨾ Ψ')
      → tcInfer ctx (RAnnot e T) ≡ success A Ψ eE d f
      → ctx ⊢ RAnnot e T ∶ A ⨾ Ψ

    tcInfer-sound-RPair :
      ∀ (ctx : NamedCtx) (a b : RawExpr)
        {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
        {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : _}
      → (IHa : ∀ {A' Ψ' eE' d' f'}
             → tcInfer ctx a ≡ success A' Ψ' eE' d' f'
             → ctx ⊢ a ∶ A' ⨾ Ψ')
      → (IHb : ∀ {B' Ψ' eE' d' f'}
             → tcInfer ctx b ≡ success B' Ψ' eE' d' f'
             → ctx ⊢ b ∶ B' ⨾ Ψ')
      → tcInfer ctx (RPair a b) ≡ success A Ψ eE d f
      → ctx ⊢ RPair a b ∶ A ⨾ Ψ

    tcInfer-sound-RQualified :
      ∀ (ctx : NamedCtx) (name alias : String)
        {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
        {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : _}
      → tcInfer ctx (RQualified name alias) ≡ success A Ψ eE d f
      → ctx ⊢ RQualified name alias ∶ A ⨾ Ψ

    ----------------------------------------------------------------
    -- G4 (partial): structured-error preservation.
    -- Each theorem pins a specific elaborator failure path to a
    -- canonical `TypeError` variant (via `renderError`).
    ----------------------------------------------------------------

    tc-err-lam-infer :
      ∀ (ctx : NamedCtx) (x : String) (body : RawExpr) {err : TypeError}
      → tcInfer ctx (RLam x body) ≡ failure err
      → err ≡ LambdaInInferMode

    tc-err-inl-infer :
      ∀ (ctx : NamedCtx) (arg : RawExpr) {err : TypeError}
      → tcInfer ctx (RApp (RVar "inl") arg) ≡ failure err
      → err ≡ InlInInferMode

    tc-err-inr-infer :
      ∀ (ctx : NamedCtx) (arg : RawExpr) {err : TypeError}
      → tcInfer ctx (RApp (RVar "inr") arg) ≡ failure err
      → err ≡ InrInInferMode

    tc-err-initial-infer :
      ∀ (ctx : NamedCtx) (arg : RawExpr) {err : TypeError}
      → tcInfer ctx (RApp (RVar "initial") arg) ≡ failure err
      → err ≡ InitialInInferMode

    tc-err-qualified-unbound :
      ∀ (ctx : NamedCtx) (name alias : String) {err : TypeError}
      → lookupImport (NamedCtx.imports ctx) (alias Data.String.++ "." Data.String.++ name) ≡ nothing
      → tcInfer ctx (RQualified name alias) ≡ failure err
      → err ≡ (UnboundQualified name alias)

    -- fst with Unit / Int argument → FstNeedsPair
    tc-err-fst-non-pair-Unit :
      ∀ (ctx : NamedCtx) (arg : RawExpr)
        {Ψ' eE' d' f' err}
      → tcInfer ctx arg ≡ success Once.Type.Unit Ψ' eE' d' f'
      → tcInfer ctx (RApp (RVar "fst") arg) ≡ failure err
      → err ≡ FstNeedsPair

    tc-err-fst-non-pair-Int :
      ∀ (ctx : NamedCtx) (arg : RawExpr)
        {Ψ' eE' d' f' err}
      → tcInfer ctx arg ≡ success Once.Type.Int Ψ' eE' d' f'
      → tcInfer ctx (RApp (RVar "fst") arg) ≡ failure err
      → err ≡ FstNeedsPair

    -- Negation with non-Int argument → TypeMismatch Int <type>
    tc-err-neg-non-Int-Unit :
      ∀ (ctx : NamedCtx) (e : RawExpr)
        {Ψ' eE' d' f' err}
      → tcInfer ctx e ≡ success Once.Type.Unit Ψ' eE' d' f'
      → tcInfer ctx (RUnaryOp OpNeg e) ≡ failure err
      → err ≡ TypeMismatch Once.Type.Int Once.Type.Unit

    tc-err-neg-non-Int-Str :
      ∀ (ctx : NamedCtx) (e : RawExpr)
        {Ψ' eE' d' f' err}
      → tcInfer ctx e ≡ success Once.Type.Str Ψ' eE' d' f'
      → tcInfer ctx (RUnaryOp OpNeg e) ≡ failure err
      → err ≡ TypeMismatch Once.Type.Int Once.Type.Str

    -- Bare-name variable that is not "unit" and not in local/import scope.
    tc-err-var-unbound :
      ∀ (ctx : NamedCtx) (x : String) {err : TypeError}
      → ¬ (x ≡ "unit")
      → lookupLocal ctx x ≡ nothing
      → lookupImport (NamedCtx.imports ctx) x ≡ nothing
      → tcInfer ctx (RVar x) ≡ failure err
      → err ≡ (UnboundVariable x)

    -- snd with Unit / Int argument → SndNeedsPair
    tc-err-snd-non-pair-Unit :
      ∀ (ctx : NamedCtx) (arg : RawExpr)
        {Ψ' eE' d' f' err}
      → tcInfer ctx arg ≡ success Once.Type.Unit Ψ' eE' d' f'
      → tcInfer ctx (RApp (RVar "snd") arg) ≡ failure err
      → err ≡ SndNeedsPair

    tc-err-snd-non-pair-Int :
      ∀ (ctx : NamedCtx) (arg : RawExpr)
        {Ψ' eE' d' f' err}
      → tcInfer ctx arg ≡ success Once.Type.Int Ψ' eE' d' f'
      → tcInfer ctx (RApp (RVar "snd") arg) ≡ failure err
      → err ≡ SndNeedsPair

    -- Case scrutinee non-sum → CaseScrutineeNotSum
    tc-err-case-scrut-Unit :
      ∀ (ctx : NamedCtx) (scrut : RawExpr) (xL : String) (eL : RawExpr)
        (xR : String) (eR : RawExpr)
        {Ψ' eE' d' f' err}
      → tcInfer ctx scrut ≡ success Once.Type.Unit Ψ' eE' d' f'
      → tcInfer ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
      → err ≡ CaseScrutineeNotSum

    tc-err-case-scrut-Int :
      ∀ (ctx : NamedCtx) (scrut : RawExpr) (xL : String) (eL : RawExpr)
        (xR : String) (eR : RawExpr)
        {Ψ' eE' d' f' err}
      → tcInfer ctx scrut ≡ success Once.Type.Int Ψ' eE' d' f'
      → tcInfer ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
      → err ≡ CaseScrutineeNotSum

    -- Check-mode RInt at non-Int target → TypeMismatch
    tc-err-check-RInt-type-mismatch :
      ∀ (ctx : NamedCtx) (n : _) (T : Type) {err : TypeError}
      → ¬ (T ≡ Once.Type.Int)
      → tcCheck ctx (Raw.RInt n) T ≡ failure err
      → err ≡ (TypeMismatch T Once.Type.Int)

    -- Check-mode RUnit at non-Unit target → TypeMismatch
    tc-err-check-RUnit-type-mismatch :
      ∀ (ctx : NamedCtx) (T : Type) {err : TypeError}
      → ¬ (T ≡ Once.Type.Unit)
      → tcCheck ctx Raw.RUnit T ≡ failure err
      → err ≡ (TypeMismatch T Once.Type.Unit)

    -- Check-mode RStringLit at non-Str target → TypeMismatch
    tc-err-check-RStringLit-type-mismatch :
      ∀ (ctx : NamedCtx) (s : String) (T : Type) {err : TypeError}
      → ¬ (T ≡ Once.Type.Str)
      → tcCheck ctx (Raw.RStringLit s) T ≡ failure err
      → err ≡ (TypeMismatch T Once.Type.Str)

    -- RDestruct branches with mismatched types → CaseBranchMismatch.
    tc-err-case-branch-mismatch :
      ∀ (ctx : NamedCtx) (scrut : RawExpr)
        (xL : String) (eL : RawExpr) (xR : String) (eR : RawExpr)
        (A B : Type)
        {Ψs scrutE ds fs}
        (C₁ C₂ : Type) {qℓ qr}
        {Ψₗ eLE dL fL Ψᵣ eRE dR fR err}
      → tcInfer ctx scrut ≡ success (A Once.Type.+ B) Ψs scrutE ds fs
      → tcInfer (extendNamedCtx ctx xL A) eL
          ≡ success C₁ (qℓ Once.Surface.Syntax.Usage.∷ Ψₗ) eLE dL fL
      → tcInfer (extendNamedCtx ctx xR B) eR
          ≡ success C₂ (qr Once.Surface.Syntax.Usage.∷ Ψᵣ) eRE dR fR
      → ¬ (C₁ ≡ C₂)
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
    tc-err-lam-usage-violation :
      ∀ (ctx : NamedCtx) (x : String) (body : RawExpr)
        (A : Type) (q : _) (B : Type)
        (q' : _) {Ψ' eE' d' f' err}
      → tcCheck (extendNamedCtx ctx x A) body B
          ≡ success (q' Once.Surface.Syntax.Usage.∷ Ψ') eE' d' f'
      → Once.TypeCheck.Elaborate.decideLeq q' q ≡ nothing
      → tcCheck ctx (RLam x body) (A Once.Type.⇒[ Once.Type.mk-kind q Once.Type.pure ] B) ≡ failure err
      → err ≡ UsageViolation x q q'

    -- Previously-blocked: BinOp's operand sub-error is wrapped in
    -- BinOpLeftError or BinOpRightError.
    -- PLAN 0.75 F4: the hypothesis is `notNumeric`, not `asInt`'s failure.
    -- `Float` is a good binop operand now, so "the left operand is not `Int`"
    -- no longer implies a LEFT error — `1.5 + "x"` is a RIGHT error. The
    -- claim is unchanged for every type it still covers; only the type it
    -- covers changed, and it changed because the language did.
    tc-err-binop-left-wraps :
      ∀ (ctx : NamedCtx) (op : BinOp) (e₁ e₂ : RawExpr)
        {sub-err outer-err}
      → Once.TypeCheck.Elaborate.notNumeric (tcInfer ctx e₁) ≡ just sub-err
      → tcInfer ctx (RBinOp op e₁ e₂) ≡ failure outer-err
      → outer-err ≡ BinOpLeftError sub-err

    tc-err-binop-right-wraps :
      ∀ (ctx : NamedCtx) (op : BinOp) (e₁ e₂ : RawExpr)
        {Ψ₁ e₁E d₁ f₁ sub-err outer-err}
      → Once.TypeCheck.Elaborate.asInt (tcInfer ctx e₁)
          ≡ Once.TypeCheck.Elaborate.isInt Ψ₁ e₁E d₁ f₁
      → Once.TypeCheck.Elaborate.asInt (tcInfer ctx e₂)
          ≡ Once.TypeCheck.Elaborate.notInt sub-err
      → tcInfer ctx (RBinOp op e₁ e₂) ≡ failure outer-err
      → outer-err ≡ BinOpRightError sub-err

    -- G4 exhaustive per-Type coverage
    tc-err-fst-non-pair-Void :
      ∀ (ctx : NamedCtx) (arg : RawExpr)
        {Ψ' eE' d' f' err}
      → tcInfer ctx arg ≡ success Once.Type.Void Ψ' eE' d' f'
      → tcInfer ctx (RApp (RVar "fst") arg) ≡ failure err
      → err ≡ FstNeedsPair

    tc-err-fst-non-pair-Str :
      ∀ (ctx : NamedCtx) (arg : RawExpr)
        {Ψ' eE' d' f' err}
      → tcInfer ctx arg ≡ success Once.Type.Str Ψ' eE' d' f'
      → tcInfer ctx (RApp (RVar "fst") arg) ≡ failure err
      → err ≡ FstNeedsPair

    tc-err-snd-non-pair-Void :
      ∀ (ctx : NamedCtx) (arg : RawExpr)
        {Ψ' eE' d' f' err}
      → tcInfer ctx arg ≡ success Once.Type.Void Ψ' eE' d' f'
      → tcInfer ctx (RApp (RVar "snd") arg) ≡ failure err
      → err ≡ SndNeedsPair

    tc-err-snd-non-pair-Str :
      ∀ (ctx : NamedCtx) (arg : RawExpr)
        {Ψ' eE' d' f' err}
      → tcInfer ctx arg ≡ success Once.Type.Str Ψ' eE' d' f'
      → tcInfer ctx (RApp (RVar "snd") arg) ≡ failure err
      → err ≡ SndNeedsPair

    tc-err-neg-non-Int-Void :
      ∀ (ctx : NamedCtx) (e : RawExpr)
        {Ψ' eE' d' f' err}
      → tcInfer ctx e ≡ success Once.Type.Void Ψ' eE' d' f'
      → tcInfer ctx (RUnaryOp OpNeg e) ≡ failure err
      → err ≡ TypeMismatch Once.Type.Int Once.Type.Void

    tc-err-case-scrut-Void :
      ∀ (ctx : NamedCtx) (scrut : RawExpr) (xL : String) (eL : RawExpr)
        (xR : String) (eR : RawExpr)
        {Ψ' eE' d' f' err}
      → tcInfer ctx scrut ≡ success Once.Type.Void Ψ' eE' d' f'
      → tcInfer ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
      → err ≡ CaseScrutineeNotSum

    tc-err-case-scrut-Str :
      ∀ (ctx : NamedCtx) (scrut : RawExpr) (xL : String) (eL : RawExpr)
        (xR : String) (eR : RawExpr)
        {Ψ' eE' d' f' err}
      → tcInfer ctx scrut ≡ success Once.Type.Str Ψ' eE' d' f'
      → tcInfer ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
      → err ≡ CaseScrutineeNotSum

    -- Exhaustive per-Type G4 wiring (Float, Buffer, Sum, Product, Fun).
    tc-err-fst-non-pair-Float :
      ∀ (ctx : NamedCtx) (arg : RawExpr) {Ψ' eE' d' f' err}
      → tcInfer ctx arg ≡ success Once.Type.Float Ψ' eE' d' f'
      → tcInfer ctx (RApp (RVar "fst") arg) ≡ failure err
      → err ≡ FstNeedsPair

    tc-err-snd-non-pair-Float :
      ∀ (ctx : NamedCtx) (arg : RawExpr) {Ψ' eE' d' f' err}
      → tcInfer ctx arg ≡ success Once.Type.Float Ψ' eE' d' f'
      → tcInfer ctx (RApp (RVar "snd") arg) ≡ failure err
      → err ≡ SndNeedsPair

    tc-err-neg-non-Int-Float :
      ∀ (ctx : NamedCtx) (e : RawExpr) {Ψ' eE' d' f' err}
      → tcInfer ctx e ≡ success Once.Type.Float Ψ' eE' d' f'
      → tcInfer ctx (RUnaryOp OpNeg e) ≡ failure err
      → err ≡ TypeMismatch Once.Type.Int Once.Type.Float

    tc-err-case-scrut-Float :
      ∀ (ctx : NamedCtx) (scrut : RawExpr) (xL : String) (eL : RawExpr)
        (xR : String) (eR : RawExpr) {Ψ' eE' d' f' err}
      → tcInfer ctx scrut ≡ success Once.Type.Float Ψ' eE' d' f'
      → tcInfer ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure err
      → err ≡ CaseScrutineeNotSum

    ----------------------------------------------------------------
    -- G2 (continued): remaining soundness fields.
    ----------------------------------------------------------------

    -- RApp polymorphic builtin specialisations
    tcInfer-sound-RApp-id :
      ∀ (ctx : NamedCtx) (arg : RawExpr)
        {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
        {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : _}
      → (IH : ∀ {A' Ψ' eE' d' f'}
            → tcInfer ctx arg ≡ success A' Ψ' eE' d' f'
            → ctx ⊢ arg ∶ A' ⨾ Ψ')
      → tcInfer ctx (RApp (RVar "id") arg) ≡ success A Ψ eE d f
      → ctx ⊢ RApp (RVar "id") arg ∶ A ⨾ Ψ

    tcInfer-sound-RApp-fst :
      ∀ (ctx : NamedCtx) (arg : RawExpr)
        {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
        {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : _}
      → (IH : ∀ {A' Ψ' eE' d' f'}
            → tcInfer ctx arg ≡ success A' Ψ' eE' d' f'
            → ctx ⊢ arg ∶ A' ⨾ Ψ')
      → tcInfer ctx (RApp (RVar "fst") arg) ≡ success A Ψ eE d f
      → ctx ⊢ RApp (RVar "fst") arg ∶ A ⨾ Ψ

    tcInfer-sound-RApp-snd :
      ∀ (ctx : NamedCtx) (arg : RawExpr)
        {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
        {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : _}
      → (IH : ∀ {A' Ψ' eE' d' f'}
            → tcInfer ctx arg ≡ success A' Ψ' eE' d' f'
            → ctx ⊢ arg ∶ A' ⨾ Ψ')
      → tcInfer ctx (RApp (RVar "snd") arg) ≡ success A Ψ eE d f
      → ctx ⊢ RApp (RVar "snd") arg ∶ A ⨾ Ψ

    tcInfer-sound-RApp-terminal :
      ∀ (ctx : NamedCtx) (arg : RawExpr)
        {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
        {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : _}
      → (IH : ∀ {A' Ψ' eE' d' f'}
            → tcInfer ctx arg ≡ success A' Ψ' eE' d' f'
            → ctx ⊢ arg ∶ A' ⨾ Ψ')
      → tcInfer ctx (RApp (RVar "terminal") arg) ≡ success A Ψ eE d f
      → ctx ⊢ RApp (RVar "terminal") arg ∶ A ⨾ Ψ

    -- Generic function application. Premise:
    -- `classifyAppHead f ≡ nothing`, i.e. `f` is not one of the
    -- seven polymorphic builtins. Completes the 15 / 15 RawExpr
    -- soundness coverage for infer mode.
    --
    -- Plan 0.4 T1, change 1 (2026-04-30): IH_x's premise is now
    -- `tcCheck ctx x A' ≡ success`, matching the bidirectional
    -- inferElab rule (infer f, check x at f's domain). The result
    -- is a check-mode `⊢ᶜ x ∶ A'` derivation, fed straight into
    -- t-app/t-effApp's updated check-mode premise.
    tcInfer-sound-RApp-generic :
      ∀ (ctx : NamedCtx) (f x : RawExpr)
        {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
        {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d fresh : _}
      → Once.TypeCheck.Elaborate.classifyAppHead f ≡ nothing
      → (IH_f : ∀ {F' Ψ' eE' d' f'}
             → tcInfer ctx f ≡ success F' Ψ' eE' d' f'
             → ctx ⊢ f ∶ F' ⨾ Ψ')
      → (IH_x : ∀ {A' Ψ' eE' d' f'}
             → tcCheck ctx x A' ≡ success Ψ' eE' d' f'
             → ctx ⊢ᶜ x ∶ A' ⨾ Ψ')
      → tcInfer ctx (RApp f x) ≡ success A Ψ eE d fresh
      → ctx ⊢ RApp f x ∶ A ⨾ Ψ

    tcInfer-sound-RBinOp :
      ∀ (ctx : NamedCtx) (op : BinOp) (e₁ e₂ : RawExpr)
        {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
        {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : _}
      → (IH₁ : ∀ {A' Ψ' eE' d' f'}
             → tcInfer ctx e₁ ≡ success A' Ψ' eE' d' f'
             → ctx ⊢ e₁ ∶ A' ⨾ Ψ')
      → (IH₂ : ∀ {B' Ψ' eE' d' f'}
             → tcInfer ctx e₂ ≡ success B' Ψ' eE' d' f'
             → ctx ⊢ e₂ ∶ B' ⨾ Ψ')
      → tcInfer ctx (RBinOp op e₁ e₂) ≡ success A Ψ eE d f
      → ctx ⊢ RBinOp op e₁ e₂ ∶ A ⨾ Ψ

    tcInfer-sound-RDestruct :
      ∀ (ctx : NamedCtx) (scrut : RawExpr) (xL : String) (eL : RawExpr)
        (xR : String) (eR : RawExpr)
        {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
        {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : _}
      → (IHs : ∀ {T' Ψ' eE' d' f'}
             → tcInfer ctx scrut ≡ success T' Ψ' eE' d' f'
             → ctx ⊢ scrut ∶ T' ⨾ Ψ')
      → (IHL : ∀ {Aty B' Ψ' eE' d' f'}
             → tcInfer (extendNamedCtx ctx xL Aty) eL ≡ success B' Ψ' eE' d' f'
             → (extendNamedCtx ctx xL Aty) ⊢ eL ∶ B' ⨾ Ψ')
      → (IHR : ∀ {Bty C' Ψ' eE' d' f'}
             → tcInfer (extendNamedCtx ctx xR Bty) eR ≡ success C' Ψ' eE' d' f'
             → (extendNamedCtx ctx xR Bty) ⊢ eR ∶ C' ⨾ Ψ')
      → tcInfer ctx (RDestruct scrut xL eL xR eR) ≡ success A Ψ eE d f
      → ctx ⊢ RDestruct scrut xL eL xR eR ∶ A ⨾ Ψ

    tcCheck-sound-RLam :
      ∀ (ctx : NamedCtx) (x : String) (body : RawExpr)
        (A : Type) (q : _) (B : Type)
        {Ψ : Surface.Usage (NamedCtx.size ctx)}
        {eE : SExpr (NamedCtx.debruijn ctx) Ψ (A Once.Type.⇒[ Once.Type.mk-kind q Once.Type.pure ] B)}
        {d f : _}
      → (IH : ∀ {Ψ' eE' d' f'}
            → tcCheck (extendNamedCtx ctx x A) body B ≡ success Ψ' eE' d' f'
            → (extendNamedCtx ctx x A) ⊢ᶜ body ∶ B ⨾ Ψ')
      → tcCheck ctx (RLam x body) (A Once.Type.⇒[ Once.Type.mk-kind q Once.Type.pure ] B) ≡ success Ψ eE d f
      → ctx ⊢ᶜ RLam x body ∶ (A Once.Type.⇒[ Once.Type.mk-kind q Once.Type.pure ] B) ⨾ Ψ

    tcInfer-sound-RLet :
      ∀ (ctx : NamedCtx) (x : String) (e₁ e₂ : RawExpr)
        {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
        {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : _}
      → (IH₁ : ∀ {A' Ψ' eE' d' f'}
             → tcInfer ctx e₁ ≡ success A' Ψ' eE' d' f'
             → ctx ⊢ e₁ ∶ A' ⨾ Ψ')
      → (IH₂ : ∀ {Aty B' Ψ' eE' d' f'}
             → tcInfer (extendNamedCtx ctx x Aty) e₂ ≡ success B' Ψ' eE' d' f'
             → (extendNamedCtx ctx x Aty) ⊢ e₂ ∶ B' ⨾ Ψ')
      → tcInfer ctx (RLet x e₁ e₂) ≡ success A Ψ eE d f
      → ctx ⊢ RLet x e₁ e₂ ∶ A ⨾ Ψ

    ----------------------------------------------------------------
    -- G2 (completeness direction): if the elaborator's sub-expressions
    -- succeed (from IHs), the outer elaborator succeeds. These lemmas
    -- are the forward counterparts of the soundness theorems; combined
    -- they give iff-completeness for each construct.
    ----------------------------------------------------------------

    tcInfer-complete-RInt :
      ∀ (ctx : NamedCtx) (n : ℤ)
      → ∃[ eE ] ∃[ d ] ∃[ f ]
          tcInfer ctx (RInt n) ≡ success Once.Type.Int Surface.zeroUsage eE d f

    tcInfer-complete-RUnit :
      ∀ (ctx : NamedCtx)
      → ∃[ eE ] ∃[ d ] ∃[ f ]
          tcInfer ctx RUnit ≡ success Once.Type.Unit Surface.zeroUsage eE d f

    tcInfer-complete-RStringLit :
      ∀ (ctx : NamedCtx) (s : String)
      → ∃[ eE ] ∃[ d ] ∃[ f ]
          tcInfer ctx (RStringLit s) ≡ success Once.Type.Str Surface.zeroUsage eE d f

    tcInfer-complete-RVar-unit :
      ∀ (ctx : NamedCtx)
      → ∃[ eE ] ∃[ d ] ∃[ f ]
          tcInfer ctx (RVar "unit") ≡ success Once.Type.Unit Surface.zeroUsage eE d f

    tcInfer-complete-RQualified :
      ∀ (ctx : NamedCtx) (name alias : String) (T : Type)
      → lookupImport (NamedCtx.imports ctx) (alias Data.String.++ "." Data.String.++ name) ≡ just T
      → IsConcrete T
      → ∃[ eE ] ∃[ d ] ∃[ f ]
          tcInfer ctx (RQualified name alias) ≡ success T Surface.zeroUsage eE d f

    -- RPair: both subs infer → outer succeeds.
    tcInfer-complete-RPair :
      ∀ (ctx : NamedCtx) (a b : RawExpr) {A B : Type}
        {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
        {aE : SExpr (NamedCtx.debruijn ctx) Ψ₁ A}
        {bE : SExpr (NamedCtx.debruijn ctx) Ψ₂ B}
        {dA dB fA fB : _}
      → tcInfer ctx a ≡ success A Ψ₁ aE dA fA
      → tcInfer ctx b ≡ success B Ψ₂ bE dB fB
      → ∃[ eE ] ∃[ d ] ∃[ f ]
          tcInfer ctx (RPair a b) ≡ success (A Once.Type.* B) (Ψ₁ Surface.+ᵘ Ψ₂) eE d f

    -- RUnaryOp OpNeg: sub at Int → outer success at Int.
    tcInfer-complete-RUnaryOp-neg :
      ∀ (ctx : NamedCtx) (e : RawExpr)
        {Ψ : Surface.Usage (NamedCtx.size ctx)}
        {eE' : SExpr (NamedCtx.debruijn ctx) Ψ Once.Type.Int}
        {d' f' : _}
      → tcInfer ctx e ≡ success Once.Type.Int Ψ eE' d' f'
      → ∃[ eE ] ∃[ d ] ∃[ f ]
          tcInfer ctx (RUnaryOp OpNeg e) ≡ success Once.Type.Int Ψ eE d f

    -- RAnnot: check-mode sub success → infer-mode success.
    tcInfer-complete-RAnnot :
      ∀ (ctx : NamedCtx) (e : RawExpr) (T : Type)
        {Ψ : Surface.Usage (NamedCtx.size ctx)}
        {eE' : SExpr (NamedCtx.debruijn ctx) Ψ T}
        {d' f' : _}
      → tcCheck ctx e T ≡ success Ψ eE' d' f'
      → ∃[ eE ] ∃[ d ] ∃[ f ]
          tcInfer ctx (RAnnot e T) ≡ success T Ψ eE d f

    -- RLet: sub₁ + extended-context sub₂ both infer → outer success.
    tcInfer-complete-RLet :
      ∀ (ctx : NamedCtx) (x : String) (e₁ e₂ : RawExpr)
        {A B : Type} {q : _}
        {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
        {e₁E : SExpr (NamedCtx.debruijn ctx) Ψ₁ A}
        {e₂E : SExpr (NamedCtx.debruijn (extendNamedCtx ctx x A))
                     (q Once.Surface.Syntax.Usage.∷ Ψ₂) B}
        {d₁ d₂ f₁ f₂ : _}
      → tcInfer ctx e₁ ≡ success A Ψ₁ e₁E d₁ f₁
      → tcInfer (extendNamedCtx ctx x A) e₂
          ≡ success B (q Once.Surface.Syntax.Usage.∷ Ψ₂) e₂E d₂ f₂
      → ∃[ eE ] ∃[ d ] ∃[ f ]
          tcInfer ctx (RLet x e₁ e₂)
            ≡ success B (Ψ₂ Surface.+ᵘ (q Surface.*ᵘ Ψ₁)) eE d f

    -- RApp polymorphic builtin completenesses
    tcInfer-complete-RApp-id :
      ∀ (ctx : NamedCtx) (arg : RawExpr) {T : Type}
        {Ψ : Surface.Usage (NamedCtx.size ctx)}
        {argE : SExpr (NamedCtx.debruijn ctx) Ψ T}
        {d' f' : _}
      → tcInfer ctx arg ≡ success T Ψ argE d' f'
      → ∃[ eE ] ∃[ d ] ∃[ f ]
          tcInfer ctx (RApp (RVar "id") arg)
            ≡ success T (Surface.zeroUsage Surface.+ᵘ (Once.Type.Many Surface.*ᵘ Ψ)) eE d f

    tcInfer-complete-RApp-fst :
      ∀ (ctx : NamedCtx) (arg : RawExpr) {A B : Type}
        {Ψ : Surface.Usage (NamedCtx.size ctx)}
        {argE : SExpr (NamedCtx.debruijn ctx) Ψ (A Once.Type.* B)}
        {d' f' : _}
      → tcInfer ctx arg ≡ success (A Once.Type.* B) Ψ argE d' f'
      → ∃[ eE ] ∃[ d ] ∃[ f ]
          tcInfer ctx (RApp (RVar "fst") arg)
            ≡ success A (Surface.zeroUsage Surface.+ᵘ (Once.Type.Many Surface.*ᵘ Ψ)) eE d f

    tcInfer-complete-RApp-snd :
      ∀ (ctx : NamedCtx) (arg : RawExpr) {A B : Type}
        {Ψ : Surface.Usage (NamedCtx.size ctx)}
        {argE : SExpr (NamedCtx.debruijn ctx) Ψ (A Once.Type.* B)}
        {d' f' : _}
      → tcInfer ctx arg ≡ success (A Once.Type.* B) Ψ argE d' f'
      → ∃[ eE ] ∃[ d ] ∃[ f ]
          tcInfer ctx (RApp (RVar "snd") arg)
            ≡ success B (Surface.zeroUsage Surface.+ᵘ (Once.Type.Many Surface.*ᵘ Ψ)) eE d f

    tcInfer-complete-RApp-terminal :
      ∀ (ctx : NamedCtx) (arg : RawExpr) {T : Type}
        {Ψ : Surface.Usage (NamedCtx.size ctx)}
        {argE : SExpr (NamedCtx.debruijn ctx) Ψ T}
        {d' f' : _}
      → tcInfer ctx arg ≡ success T Ψ argE d' f'
      → ∃[ eE ] ∃[ d ] ∃[ f ]
          tcInfer ctx (RApp (RVar "terminal") arg)
            ≡ success Once.Type.Unit (Surface.zeroUsage Surface.+ᵘ (Once.Type.Many Surface.*ᵘ Ψ)) eE d f

    -- RVar local and import
    tcInfer-complete-RVar-local :
      ∀ (ctx : NamedCtx) (x : String) {A : Type}
        {Ψ : Surface.Usage (NamedCtx.size ctx)}
        {eE' : Surface.SVar (NamedCtx.debruijn ctx) Ψ A}
      → ¬ (x ≡ "unit")
      → lookupLocal ctx x ≡ just (A , Ψ , eE')
      → ∃[ eE ] ∃[ d ] ∃[ f ]
          tcInfer ctx (RVar x) ≡ success A Ψ eE d f

    tcInfer-complete-RVar-import :
      ∀ (ctx : NamedCtx) (x : String) {T : Type}
      → ¬ (x ≡ "unit")
      → lookupLocal ctx x ≡ nothing
      → lookupImport (NamedCtx.imports ctx) x ≡ just T
      → IsConcrete T
      → ∃[ eE ] ∃[ d ] ∃[ f ]
          tcInfer ctx (RVar x) ≡ success T Surface.zeroUsage eE d f

    -- RBinOp (arithmetic / comparison families)
    tcInfer-complete-RBinOp-arith :
      ∀ (ctx : NamedCtx) (op : BinOp) (arithEq : Raw.isArithmeticOp op ≡ Data.Bool.true)
        (e₁ e₂ : RawExpr)
        {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
        {e₁E : SExpr (NamedCtx.debruijn ctx) Ψ₁ Once.Type.Int}
        {e₂E : SExpr (NamedCtx.debruijn ctx) Ψ₂ Once.Type.Int}
        {d₁ d₂ f₁ f₂ : _}
      → tcInfer ctx e₁ ≡ success Once.Type.Int Ψ₁ e₁E d₁ f₁
      → tcInfer ctx e₂ ≡ success Once.Type.Int Ψ₂ e₂E d₂ f₂
      → ∃[ eE ] ∃[ d ] ∃[ f ]
          tcInfer ctx (RBinOp op e₁ e₂) ≡ success Once.Type.Int (Ψ₁ Surface.+ᵘ Ψ₂) eE d f

    tcInfer-complete-RBinOp-cmp :
      ∀ (ctx : NamedCtx) (op : BinOp) (cmpEq : Raw.isComparisonOp op ≡ Data.Bool.true)
        (e₁ e₂ : RawExpr)
        {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
        {e₁E : SExpr (NamedCtx.debruijn ctx) Ψ₁ Once.Type.Int}
        {e₂E : SExpr (NamedCtx.debruijn ctx) Ψ₂ Once.Type.Int}
        {d₁ d₂ f₁ f₂ : _}
      → tcInfer ctx e₁ ≡ success Once.Type.Int Ψ₁ e₁E d₁ f₁
      → tcInfer ctx e₂ ≡ success Once.Type.Int Ψ₂ e₂E d₂ f₂
      → ∃[ eE ] ∃[ d ] ∃[ f ]
          tcInfer ctx (RBinOp op e₁ e₂)
            ≡ success (Once.Type.Unit Once.Type.+ Once.Type.Unit) (Ψ₁ Surface.+ᵘ Ψ₂) eE d f

    -- RDestruct (case/sum elim)
    tcInfer-complete-RDestruct :
      ∀ (ctx : NamedCtx) (scrut : RawExpr) (xL : String) (eL : RawExpr)
        (xR : String) (eR : RawExpr) {A B : Type}
        {Ψs : Surface.Usage (NamedCtx.size ctx)}
        {scrutE : SExpr (NamedCtx.debruijn ctx) Ψs (A Once.Type.+ B)}
        {ds fs : _}
        (C : Type) {qℓ qr : _}
        {Ψₗ : Surface.Usage (NamedCtx.size ctx)}
        {eLE : SExpr (NamedCtx.debruijn (extendNamedCtx ctx xL A))
                     (qℓ Once.Surface.Syntax.Usage.∷ Ψₗ) C}
        {dL fL : _}
        {Ψᵣ : Surface.Usage (NamedCtx.size ctx)}
        {eRE : SExpr (NamedCtx.debruijn (extendNamedCtx ctx xR B))
                     (qr Once.Surface.Syntax.Usage.∷ Ψᵣ) C}
        {dR fR : _}
      → tcInfer ctx scrut ≡ success (A Once.Type.+ B) Ψs scrutE ds fs
      → tcInfer (extendNamedCtx ctx xL A) eL
          ≡ success C (qℓ Once.Surface.Syntax.Usage.∷ Ψₗ) eLE dL fL
      → tcInfer (extendNamedCtx ctx xR B) eR
          ≡ success C (qr Once.Surface.Syntax.Usage.∷ Ψᵣ) eRE dR fR
      → ∃[ eE ] ∃[ d ] ∃[ f ]
          tcInfer ctx (Raw.RDestruct scrut xL eL xR eR)
            ≡ success C (Ψs Surface.+ᵘ (Ψₗ Surface.⊔ᵘ Ψᵣ)) eE d f

    -- Generic RApp.
    -- Plan 0.4 T1, change 1: x premise is now `tcCheck ctx x A`
    -- (matches the bidirectional inferElab rule).
    tcInfer-complete-RApp-generic :
      ∀ (ctx : NamedCtx) (f x : RawExpr) (A : Type) {B : Type} {q : _}
        {Ψf : Surface.Usage (NamedCtx.size ctx)}
        {fE : SExpr (NamedCtx.debruijn ctx) Ψf (A Once.Type.⇒[ Once.Type.mk-kind q Once.Type.pure ] B)}
        {df ff : _}
        {Ψx : Surface.Usage (NamedCtx.size ctx)}
        {xE : SExpr (NamedCtx.debruijn ctx) Ψx A}
        {dx fx : _}
      → Once.TypeCheck.Elaborate.classifyAppHead f ≡ nothing
      → tcInfer ctx f ≡ success (A Once.Type.⇒[ Once.Type.mk-kind q Once.Type.pure ] B) Ψf fE df ff
      → tcCheck ctx x A ≡ success Ψx xE dx fx
      → ∃[ eE ] ∃[ d ] ∃[ f' ]
          tcInfer ctx (RApp f x) ≡ success B (Ψf Surface.+ᵘ (q Surface.*ᵘ Ψx)) eE d f'

    -- Check-mode RLam
    tcCheck-complete-RLam :
      ∀ (ctx : NamedCtx) (x : String) (body : RawExpr)
        (A : Type) (q q' : _) (B : Type)
        {Ψ' : Surface.Usage (NamedCtx.size ctx)}
        {eE' : SExpr (NamedCtx.debruijn (extendNamedCtx ctx x A))
                     (q' Once.Surface.Syntax.Usage.∷ Ψ') B}
        {d' f' : _}
      → (q' Once.Type.≤q q) ≡ Data.Bool.true
      → tcCheck (extendNamedCtx ctx x A) body B
          ≡ success (q' Once.Surface.Syntax.Usage.∷ Ψ') eE' d' f'
      → ∃[ eE ] ∃[ d ] ∃[ f ]
          tcCheck ctx (RLam x body) (A Once.Type.⇒[ Once.Type.mk-kind q Once.Type.pure ] B) ≡ success Ψ' eE d f

    ----------------------------------------------------------------
    -- G7 (first pass): algebraic identities
    ----------------------------------------------------------------

    id-decideLeq-iff :
      ∀ (q' q : _)
      → ((q' Once.Type.≤q q) ≡ Data.Bool.true
          → ∃[ p ] Once.TypeCheck.Elaborate.decideLeq q' q ≡ just p)
      × (∀ {p} → Once.TypeCheck.Elaborate.decideLeq q' q ≡ just p
             → (q' Once.Type.≤q q) ≡ Data.Bool.true)

    id-binop-classification-exhaustive :
      ∀ (op : BinOp)
      → (Raw.isArithmeticOp op ≡ Data.Bool.true)
      ⊎ (Raw.isComparisonOp op ≡ Data.Bool.true)

    id-binop-classification-exclusive :
      ∀ (op : BinOp)
      → Raw.isArithmeticOp op ≡ Data.Bool.true
      → Raw.isComparisonOp op ≡ Data.Bool.true
      → Data.Empty.⊥

    id-≤q-refl : ∀ (q : _) → (q Once.Type.≤q q) ≡ Data.Bool.true

    id-≤q-trans :
      ∀ (q₁ q₂ q₃ : _)
      → (q₁ Once.Type.≤q q₂) ≡ Data.Bool.true
      → (q₂ Once.Type.≤q q₃) ≡ Data.Bool.true
      → (q₁ Once.Type.≤q q₃) ≡ Data.Bool.true

    id-Zero-≤q-all : ∀ (q : _) → (Once.Type.Zero Once.Type.≤q q) ≡ Data.Bool.true

    id-all-≤q-Many : ∀ (q : _) → (q Once.Type.≤q Once.Type.Many) ≡ Data.Bool.true

    -- Quantity algebra
    id-+q-comm : ∀ (q₁ q₂ : _) → q₁ Once.Type.+q q₂ ≡ q₂ Once.Type.+q q₁
    id-+q-assoc : ∀ (q₁ q₂ q₃ : _)
                → q₁ Once.Type.+q (q₂ Once.Type.+q q₃)
                  ≡ (q₁ Once.Type.+q q₂) Once.Type.+q q₃
    id-*q-distrib-+q :
      ∀ (q₁ q₂ q₃ : _) → q₁ Once.Type.*q (q₂ Once.Type.+q q₃)
                        ≡ (q₁ Once.Type.*q q₂) Once.Type.+q (q₁ Once.Type.*q q₃)
    id-⊔q-comm : ∀ (q₁ q₂ : _) → q₁ Once.Type.⊔q q₂ ≡ q₂ Once.Type.⊔q q₁
    id-⊔q-idem : ∀ (q : _) → q Once.Type.⊔q q ≡ q

    -- Usage-vector algebra
    id-+ᵘ-comm : ∀ {n} (Ψ₁ Ψ₂ : Once.Surface.Syntax.Usage n)
                → Ψ₁ Surface.+ᵘ Ψ₂ ≡ Ψ₂ Surface.+ᵘ Ψ₁
    id-+ᵘ-assoc : ∀ {n} (Ψ₁ Ψ₂ Ψ₃ : Once.Surface.Syntax.Usage n)
                 → Ψ₁ Surface.+ᵘ (Ψ₂ Surface.+ᵘ Ψ₃)
                   ≡ (Ψ₁ Surface.+ᵘ Ψ₂) Surface.+ᵘ Ψ₃
    id-⊔ᵘ-comm : ∀ {n} (Ψ₁ Ψ₂ : Once.Surface.Syntax.Usage n)
                → Ψ₁ Surface.⊔ᵘ Ψ₂ ≡ Ψ₂ Surface.⊔ᵘ Ψ₁
    id-⊔ᵘ-idem : ∀ {n} (Ψ : Once.Surface.Syntax.Usage n) → Ψ Surface.⊔ᵘ Ψ ≡ Ψ
    id-*ᵘ-identity-One : ∀ {n} (Ψ : Once.Surface.Syntax.Usage n)
                       → Once.Type.One Surface.*ᵘ Ψ ≡ Ψ
    id-+ᵘ-identity-left : ∀ {n} (Ψ : Once.Surface.Syntax.Usage n)
                        → Surface.zeroUsage Surface.+ᵘ Ψ ≡ Ψ

    ----------------------------------------------------------------
    -- Grammar connection: the surface-grammar spec round-trips
    -- through the internal `Type` representation on its expressible
    -- fragment. Pins the parser's output to the formal grammar.
    ----------------------------------------------------------------

    grammar-to-type-roundtrip :
      ∀ (g : GType) (t : Type)
      → gtypeToType g ≡ just t
      → typeToGType t ≡ just g

    type-to-grammar-roundtrip :
      ∀ (t : Type) (g : GType)
      → typeToGType t ≡ just g
      → gtypeToType g ≡ just t

------------------------------------------------------------------------
-- The inhabitant
--
-- Constructing this value is the single enforcement point: every
-- field below must be filled. Agda rejects the definition if any
-- proof is missing or incorrect.
------------------------------------------------------------------------

verifiedTypeChecker : VerifiedTypeChecker
verifiedTypeChecker = record
  { tcInfer                   = inferElab
  ; tcCheck                   = checkElab
  ; tcInfer-refl              = Det.inferElab-refl
  ; tcCheck-refl              = Det.checkElab-refl
  ; tcInfer-cong              = Det.inferElab-cong
  ; tcCheck-cong              = Det.checkElab-cong
  ; tcInfer-total             = Tot.inferElab-total
  ; tcCheck-total             = Tot.checkElab-total
  ; tcInfer-sound                 = Snd.infer-sound
  ; tcCheck-sound                 = Snd.check-sound
  ; tcInfer-sound-RInt            = Snd.sound-RInt
  ; tcInfer-sound-RStringLit      = Snd.sound-RStringLit
  ; tcInfer-sound-RUnit           = Snd.sound-RUnit
  ; tcInfer-sound-RVar-unit       = Snd.sound-RVar-unit
  ; tcInfer-sound-RVar            = Snd.sound-RVar
  ; tcInfer-sound-RUnaryOp-neg    = Snd.sound-RUnaryOp-neg
  ; tcInfer-sound-RAnnot          = Snd.sound-RAnnot
  ; tcInfer-sound-RPair           = Snd.sound-RPair
  ; tcInfer-sound-RQualified      = Snd.sound-RQualified
  ; tcInfer-sound-RLet            = Snd.sound-RLet
  ; tcInfer-sound-RDestruct       = Snd.sound-RDestruct
  ; tcInfer-sound-RApp-id         = Snd.sound-RApp-id
  ; tcInfer-sound-RApp-fst        = Snd.sound-RApp-fst
  ; tcInfer-sound-RApp-snd        = Snd.sound-RApp-snd
  ; tcInfer-sound-RApp-terminal   = Snd.sound-RApp-terminal
  ; tcInfer-sound-RApp-generic    = Snd.sound-RApp-generic
  ; tcInfer-sound-RBinOp          = Snd.sound-RBinOp
  ; tcCheck-sound-RLam            = Snd.sound-check-RLam
  ; tc-err-lam-infer              = EP.lam-infer-is-LambdaInInferMode
  ; tc-err-inl-infer              = EP.inl-app-infer-is-InlInInferMode
  ; tc-err-inr-infer              = EP.inr-app-infer-is-InrInInferMode
  ; tc-err-initial-infer          = EP.initial-app-infer-is-InitialInInferMode
  ; tc-err-qualified-unbound      = EP.qualified-not-found-is-UnboundQualified
  ; tc-err-fst-non-pair-Unit      = EP.fst-non-pair-Unit
  ; tc-err-fst-non-pair-Int       = EP.fst-non-pair-Int
  ; tc-err-neg-non-Int-Unit       = EP.neg-non-Int-Unit
  ; tc-err-neg-non-Int-Str        = EP.neg-non-Int-Str
  ; tc-err-var-unbound            = EP.var-unbound-is-UnboundVariable
  ; tc-err-snd-non-pair-Unit      = EP.snd-non-pair-Unit
  ; tc-err-snd-non-pair-Int       = EP.snd-non-pair-Int
  ; tc-err-case-scrut-Unit        = EP.case-scrut-Unit
  ; tc-err-case-scrut-Int         = EP.case-scrut-Int
  ; tc-err-lam-usage-violation    = EP.lam-usage-violation-is-UsageViolation
  ; tc-err-binop-left-wraps       = EP.binop-left-err-wraps
  ; tc-err-binop-right-wraps      = EP.binop-right-err-wraps
  ; tc-err-fst-non-pair-Void      = EP.fst-non-pair-Void
  ; tc-err-fst-non-pair-Str       = EP.fst-non-pair-Str
  ; tc-err-snd-non-pair-Void      = EP.snd-non-pair-Void
  ; tc-err-snd-non-pair-Str       = EP.snd-non-pair-Str
  ; tc-err-neg-non-Int-Void       = EP.neg-non-Int-Void
  ; tc-err-case-scrut-Void        = EP.case-scrut-Void
  ; tc-err-case-scrut-Str         = EP.case-scrut-Str
  ; tc-err-fst-non-pair-Float     = EP.fst-non-pair-Float
  ; tc-err-snd-non-pair-Float     = EP.snd-non-pair-Float
  ; tc-err-neg-non-Int-Float      = EP.neg-non-Int-Float
  ; tc-err-case-scrut-Float       = EP.case-scrut-Float
  ; tc-err-case-branch-mismatch   = EP.case-branch-mismatch-is-CaseBranchMismatch
  ; tc-err-check-RInt-type-mismatch  = EP.check-RInt-type-mismatch
  ; tc-err-check-RUnit-type-mismatch = EP.check-RUnit-type-mismatch
  ; tc-err-check-RStringLit-type-mismatch = EP.check-RStringLit-type-mismatch
  ; tcInfer-complete-RInt         = λ ctx n → Cmp.infer-complete-RInt {ctx = ctx} n
  ; tcInfer-complete-RUnit        = λ ctx → Cmp.infer-complete-RUnit {ctx = ctx}
  ; tcInfer-complete-RStringLit   = λ ctx s → Cmp.infer-complete-RStringLit {ctx = ctx} s
  ; tcInfer-complete-RVar-unit    = λ ctx → Cmp.infer-complete-RVar-unit {ctx = ctx}
  ; tcInfer-complete-RQualified   = λ ctx name alias T eq conc →
                                     Cmp.infer-complete-RQualified {ctx = ctx} {name = name} {alias = alias} {T = T} eq conc
  ; tcInfer-complete-RPair        = λ ctx → Cmp.infer-complete-RPair
  ; tcInfer-complete-RUnaryOp-neg = λ ctx → Cmp.infer-complete-RUnaryOp-neg
  ; tcInfer-complete-RAnnot       = λ ctx → Cmp.infer-complete-RAnnot
  ; tcInfer-complete-RLet         = λ ctx → Cmp.infer-complete-RLet
  ; tcInfer-complete-RApp-id      = λ ctx → Cmp.infer-complete-RApp-id
  ; tcInfer-complete-RApp-fst     = λ ctx → Cmp.infer-complete-RApp-fst
  ; tcInfer-complete-RApp-snd     = λ ctx → Cmp.infer-complete-RApp-snd
  ; tcInfer-complete-RApp-terminal = λ ctx → Cmp.infer-complete-RApp-terminal
  ; tcInfer-complete-RVar-local   = λ ctx → Cmp.infer-complete-RVar-local
  ; tcInfer-complete-RVar-import  = λ ctx → Cmp.infer-complete-RVar-import
  ; tcInfer-complete-RBinOp-arith = λ ctx → Cmp.infer-complete-RBinOp-arith
  ; tcInfer-complete-RBinOp-cmp   = λ ctx → Cmp.infer-complete-RBinOp-cmp
  ; tcInfer-complete-RDestruct    = λ ctx → Cmp.infer-complete-RDestruct
  ; tcInfer-complete-RApp-generic = λ ctx → Cmp.infer-complete-RApp-generic
  ; tcCheck-complete-RLam         = Cmp.check-complete-RLam
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
  ; grammar-to-type-roundtrip = Conv.gtypeToType-typeToGType
  ; type-to-grammar-roundtrip = Conv.typeToGType-gtypeToType
  }
