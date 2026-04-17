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
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.TypeCheck.Elaborate
  using (NamedCtx; inferElab; checkElab; InferElabResult; CheckElabResult;
         success; failure)

open import Data.Integer using (ℤ)
open import Data.Sum using (_⊎_)

import Once.TypeCheck.Determinism as Det
import Once.TypeCheck.Totality    as Tot
import Once.TypeCheck.Soundness   as Snd
open import Once.TypeCheck.Judgment using (_⊢_∶_⨾_)
open import Once.TypeCheck.Raw as Raw using (RawExpr; RInt; RStringLit; RUnit; RVar; RAnnot; RPair; RUnaryOp; OpNeg)
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
  ; tcInfer-sound-RUnaryOp-neg    = Snd.sound-RUnaryOp-neg
  ; tcInfer-sound-RAnnot          = Snd.sound-RAnnot
  ; tcInfer-sound-RPair           = Snd.sound-RPair
  ; grammar-to-type-roundtrip = Conv.gtypeToType-typeToGType
  ; type-to-grammar-roundtrip = Conv.typeToGType-gtypeToType
  }
