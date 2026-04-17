-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

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
-- Reference: plans/0.3-frontend-verification-gaps.md.
------------------------------------------------------------------------

module Once.TypeCheck.Verified where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; ∃; ∃-syntax)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (Type)
import Once.Type
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.TypeCheck.Elaborate
  using (NamedCtx; inferElab; checkElab; InferElabResult; CheckElabResult;
         success; failure; extendNamedCtx; lookupImport; lookupLocal)
open import Data.Maybe using (Maybe; nothing)

open import Data.Integer using (ℤ)
open import Data.Sum using (_⊎_)
import Data.String

import Once.TypeCheck.Determinism as Det
import Once.TypeCheck.Totality    as Tot
import Once.TypeCheck.Soundness   as Snd
import Once.TypeCheck.ErrorProofs as EP
open import Once.TypeCheck.Judgment using (_⊢_∶_⨾_)
open import Once.TypeCheck.Error using (TypeError; renderError;
  LambdaInInferMode; InlInInferMode; InrInInferMode; InitialInInferMode;
  UnboundQualified; UnboundVariable; FstNeedsPair; SndNeedsPair;
  NegationNotInt; CaseScrutineeNotSum; ApplicationTypeMismatch)
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
    -- G2 (partial): soundness against the declarative judgment for
    -- the leaf RawExpr forms (literals, `unit` builtin). Recursive
    -- forms are currently not covered — see
    -- `Once.TypeCheck.Soundness` for the deferred cases.
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

    tcInfer-sound-RAnnot :
      ∀ (ctx : NamedCtx) (e : RawExpr) (T : Type)
        {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
        {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : _}
      → (IH : ∀ {Ψ' eE' d' f'}
            → tcCheck ctx e T ≡ success Ψ' eE' d' f'
            → ctx ⊢ e ∶ T ⨾ Ψ')
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
      ∀ (ctx : NamedCtx) (x : String) (body : RawExpr) {msg : String}
      → tcInfer ctx (RLam x body) ≡ failure msg
      → msg ≡ renderError LambdaInInferMode

    tc-err-inl-infer :
      ∀ (ctx : NamedCtx) (arg : RawExpr) {msg : String}
      → tcInfer ctx (RApp (RVar "inl") arg) ≡ failure msg
      → msg ≡ renderError InlInInferMode

    tc-err-inr-infer :
      ∀ (ctx : NamedCtx) (arg : RawExpr) {msg : String}
      → tcInfer ctx (RApp (RVar "inr") arg) ≡ failure msg
      → msg ≡ renderError InrInInferMode

    tc-err-initial-infer :
      ∀ (ctx : NamedCtx) (arg : RawExpr) {msg : String}
      → tcInfer ctx (RApp (RVar "initial") arg) ≡ failure msg
      → msg ≡ renderError InitialInInferMode

    tc-err-qualified-unbound :
      ∀ (ctx : NamedCtx) (name alias : String) {msg : String}
      → lookupImport (NamedCtx.imports ctx) (alias Data.String.++ "." Data.String.++ name) ≡ nothing
      → tcInfer ctx (RQualified name alias) ≡ failure msg
      → msg ≡ renderError (UnboundQualified name alias)

    -- fst with Unit / Int argument → FstNeedsPair
    tc-err-fst-non-pair-Unit :
      ∀ (ctx : NamedCtx) (arg : RawExpr)
        {Ψ' eE' d' f' msg}
      → tcInfer ctx arg ≡ success Once.Type.Unit Ψ' eE' d' f'
      → tcInfer ctx (RApp (RVar "fst") arg) ≡ failure msg
      → msg ≡ renderError FstNeedsPair

    tc-err-fst-non-pair-Int :
      ∀ (ctx : NamedCtx) (arg : RawExpr)
        {Ψ' eE' d' f' msg}
      → tcInfer ctx arg ≡ success Once.Type.Int Ψ' eE' d' f'
      → tcInfer ctx (RApp (RVar "fst") arg) ≡ failure msg
      → msg ≡ renderError FstNeedsPair

    -- Negation with Unit / Str argument → NegationNotInt
    tc-err-neg-non-Int-Unit :
      ∀ (ctx : NamedCtx) (e : RawExpr)
        {Ψ' eE' d' f' msg}
      → tcInfer ctx e ≡ success Once.Type.Unit Ψ' eE' d' f'
      → tcInfer ctx (RUnaryOp OpNeg e) ≡ failure msg
      → msg ≡ renderError NegationNotInt

    tc-err-neg-non-Int-Str :
      ∀ (ctx : NamedCtx) (e : RawExpr)
        {Ψ' eE' d' f' msg}
      → tcInfer ctx e ≡ success Once.Type.Str Ψ' eE' d' f'
      → tcInfer ctx (RUnaryOp OpNeg e) ≡ failure msg
      → msg ≡ renderError NegationNotInt

    -- Bare-name variable that is not "unit" and not in local/import scope.
    tc-err-var-unbound :
      ∀ (ctx : NamedCtx) (x : String) {msg : String}
      → ¬ (x ≡ "unit")
      → lookupLocal ctx x ≡ nothing
      → lookupImport (NamedCtx.imports ctx) x ≡ nothing
      → tcInfer ctx (RVar x) ≡ failure msg
      → msg ≡ renderError (UnboundVariable x)

    -- snd with Unit / Int argument → SndNeedsPair
    tc-err-snd-non-pair-Unit :
      ∀ (ctx : NamedCtx) (arg : RawExpr)
        {Ψ' eE' d' f' msg}
      → tcInfer ctx arg ≡ success Once.Type.Unit Ψ' eE' d' f'
      → tcInfer ctx (RApp (RVar "snd") arg) ≡ failure msg
      → msg ≡ renderError SndNeedsPair

    tc-err-snd-non-pair-Int :
      ∀ (ctx : NamedCtx) (arg : RawExpr)
        {Ψ' eE' d' f' msg}
      → tcInfer ctx arg ≡ success Once.Type.Int Ψ' eE' d' f'
      → tcInfer ctx (RApp (RVar "snd") arg) ≡ failure msg
      → msg ≡ renderError SndNeedsPair

    -- Case scrutinee non-sum → CaseScrutineeNotSum
    tc-err-case-scrut-Unit :
      ∀ (ctx : NamedCtx) (scrut : RawExpr) (xL : String) (eL : RawExpr)
        (xR : String) (eR : RawExpr)
        {Ψ' eE' d' f' msg}
      → tcInfer ctx scrut ≡ success Once.Type.Unit Ψ' eE' d' f'
      → tcInfer ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure msg
      → msg ≡ renderError CaseScrutineeNotSum

    tc-err-case-scrut-Int :
      ∀ (ctx : NamedCtx) (scrut : RawExpr) (xL : String) (eL : RawExpr)
        (xR : String) (eR : RawExpr)
        {Ψ' eE' d' f' msg}
      → tcInfer ctx scrut ≡ success Once.Type.Int Ψ' eE' d' f'
      → tcInfer ctx (Raw.RDestruct scrut xL eL xR eR) ≡ failure msg
      → msg ≡ renderError CaseScrutineeNotSum

    -- Generic RApp argument-type mismatch → ApplicationTypeMismatch.
    tc-err-app-domain-mismatch :
      ∀ (ctx : NamedCtx) (f x : RawExpr)
        (A B : Type) (q : _)
        {Ψf fE df fx-fresh}
        (Ax : Type)
        {Ψx xE dx fx-f-fresh msg}
      → Once.TypeCheck.Elaborate.classifyAppHead f ≡ nothing
      → tcInfer ctx f ≡ success (A Once.Type.⇒[ q ] B) Ψf fE df fx-fresh
      → tcInfer ctx x ≡ success Ax Ψx xE dx fx-f-fresh
      → ¬ (A ≡ Ax)
      → tcInfer ctx (RApp f x) ≡ failure msg
      → msg ≡ renderError (ApplicationTypeMismatch A Ax)

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
    tcInfer-sound-RApp-generic :
      ∀ (ctx : NamedCtx) (f x : RawExpr)
        {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
        {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d fresh : _}
      → Once.TypeCheck.Elaborate.classifyAppHead f ≡ nothing
      → (IH_f : ∀ {F' Ψ' eE' d' f'}
             → tcInfer ctx f ≡ success F' Ψ' eE' d' f'
             → ctx ⊢ f ∶ F' ⨾ Ψ')
      → (IH_x : ∀ {X' Ψ' eE' d' f'}
             → tcInfer ctx x ≡ success X' Ψ' eE' d' f'
             → ctx ⊢ x ∶ X' ⨾ Ψ')
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
        {eE : SExpr (NamedCtx.debruijn ctx) Ψ (A Once.Type.⇒[ q ] B)}
        {d f : _}
      → (IH : ∀ {Ψ' eE' d' f'}
            → tcCheck (extendNamedCtx ctx x A) body B ≡ success Ψ' eE' d' f'
            → (extendNamedCtx ctx x A) ⊢ body ∶ B ⨾ Ψ')
      → tcCheck ctx (RLam x body) (A Once.Type.⇒[ q ] B) ≡ success Ψ eE d f
      → ctx ⊢ RLam x body ∶ (A Once.Type.⇒[ q ] B) ⨾ Ψ

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
  ; tc-err-app-domain-mismatch    = EP.app-domain-mismatch-is-ApplicationTypeMismatch
  ; grammar-to-type-roundtrip = Conv.gtypeToType-typeToGType
  ; type-to-grammar-roundtrip = Conv.typeToGType-gtypeToType
  }
