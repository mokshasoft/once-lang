-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.Totality
--
-- Plan 0.3, gap G3: totality + well-formedness of the typechecker.
--
-- Agda's coverage checker already guarantees `inferElab` and
-- `checkElab` are total functions: every input shape is handled, no
-- diverging or stuck inputs exist. That guarantee is *implicit* in the
-- meta-theory — it is enforced at compile-time but has no object-level
-- reflection.
--
-- This module makes totality explicit as an object-level proposition:
-- for every `(ctx, e)`, the result is *either* a `success` (with an
-- intrinsically-typed, linearity-respecting expression) or a `failure`
-- (carrying an error string). The proof is essentially tautological
-- given the two-constructor shape of `InferElabResult`, but stating it
-- closes the gap between "Agda says it's total" and "we have a citable
-- theorem that the typechecker produces well-formed outputs on all
-- inputs".
--
-- The well-formedness half ("success carries a well-typed SExpr") is
-- free by construction: `SExpr Γ Ψ A` is intrinsically typed, so if a
-- `success` branch exists, its payload is type-correct and
-- linearity-respecting by the type of its projection.
--
-- Reference: plans/0.3-frontend-verification-gaps.md, gap G3.
------------------------------------------------------------------------

module Once.TypeCheck.Totality where

open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (Type)
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.TypeCheck.Elaborate
  using (NamedCtx; inferElab; checkElab; InferElabResult; CheckElabResult;
         success; failure)
open import Once.TypeCheck.Error using (TypeError)

open import Once.Surface.Syntax as Surface using ()
  renaming (Expr to SExpr; Ctx to SCtx; Usage to SUsage)

------------------------------------------------------------------------
-- Success / failure witnesses
------------------------------------------------------------------------

-- | Witness that an inference result is a success, carrying the payload.
-- The `SExpr Δ Ψ A` field is intrinsically typed and usage-indexed, so
-- existence of a `success` witness is simultaneously a totality
-- guarantee ("result is success-or-failure") and a well-formedness
-- guarantee ("success carries a well-typed, linearity-respecting
-- expression").
data IsInferSuccess {n : ℕ} {Δ : SCtx n} : InferElabResult Δ → Set where
  isInferSuccess : ∀ (A : Type) (Ψ : Surface.Usage n)
                     (eE : SExpr Δ Ψ A) (d f : ℕ)
                 → IsInferSuccess (success A Ψ eE d f)

-- | Witness that an inference result is a failure.
data IsInferFailure {n : ℕ} {Δ : SCtx n} : InferElabResult Δ → Set where
  isInferFailure : ∀ (err : TypeError) → IsInferFailure (failure err)

-- | Same, for check mode.
data IsCheckSuccess {n : ℕ} {Δ : SCtx n} {A : Type}
                  : CheckElabResult Δ A → Set where
  isCheckSuccess : ∀ (Ψ : Surface.Usage n)
                     (eE : SExpr Δ Ψ A) (d f : ℕ)
                 → IsCheckSuccess (success Ψ eE d f)

data IsCheckFailure {n : ℕ} {Δ : SCtx n} {A : Type}
                  : CheckElabResult Δ A → Set where
  isCheckFailure : ∀ (err : TypeError) → IsCheckFailure (failure err)

------------------------------------------------------------------------
-- Totality: every result is success or failure
------------------------------------------------------------------------

-- | For every context and raw expression, `inferElab` produces either
-- a success (with an intrinsically-typed elaborated expression) or a
-- failure (with an error message). This is a dichotomy over the
-- result shape — no third possibility exists.
--
-- Combined with Agda's coverage checking, this is a closed statement
-- of totality: no input shape is unhandled, no result is stuck.
inferElab-total : ∀ (ctx : NamedCtx) (e : RawExpr)
                → IsInferSuccess (inferElab ctx e)
                ⊎ IsInferFailure (inferElab ctx e)
inferElab-total ctx e with inferElab ctx e
... | success A Ψ eE d f = inj₁ (isInferSuccess A Ψ eE d f)
... | failure err        = inj₂ (isInferFailure err)

-- | Same dichotomy for `checkElab`.
checkElab-total : ∀ (ctx : NamedCtx) (e : RawExpr) (T : Type)
                → IsCheckSuccess (checkElab ctx e T)
                ⊎ IsCheckFailure (checkElab ctx e T)
checkElab-total ctx e T with checkElab ctx e T
... | success Ψ eE d f = inj₁ (isCheckSuccess Ψ eE d f)
... | failure err      = inj₂ (isCheckFailure err)

------------------------------------------------------------------------
-- Corollaries: the two branches are separable
------------------------------------------------------------------------

-- | A success and a failure result are never equal (different
-- constructors). These are useful as lemmas in stronger theorems
-- (e.g. G4's error-preservation: "this specific failure path reaches
-- this specific error shape").

success≢failure-infer : ∀ {n} {Δ : SCtx n}
                        {A : Type} {Ψ : Surface.Usage n}
                        {eE : SExpr Δ Ψ A} {d f : ℕ} {err : TypeError}
                      → success {Δ = Δ} A Ψ eE d f ≡ failure err → ⊥
success≢failure-infer ()

success≢failure-check : ∀ {n} {Δ : SCtx n} {A : Type}
                        {Ψ : Surface.Usage n}
                        {eE : SExpr Δ Ψ A} {d f : ℕ} {err : TypeError}
                      → success {Δ = Δ} {A = A} Ψ eE d f ≡ failure err → ⊥
success≢failure-check ()
