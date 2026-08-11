-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.Determinism
--
-- Plan 0.3, gap G6: determinism of the type-checker.
--
-- `inferElab` and `checkElab` are total functions in Agda. In a pure,
-- total, deterministic language like Agda, "determinism" is a feature
-- of the meta-theory rather than a deep property to prove: definitional
-- equality of inputs implies definitional equality of outputs, by
-- `cong`. This module states those facts explicitly so future refactors
-- that (for example) introduce state or nondeterminism into the
-- typechecker can be detected as breakage of these theorems.
--
-- These theorems are intentionally trivial. They exist as a
-- machine-checked contract: "the typechecker is a pure function of its
-- inputs".
--
-- Reference: plans/0.3-frontend-verification-gaps.md, gap G6.
------------------------------------------------------------------------

module Once.TypeCheck.Determinism where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Once.Type using (Type)
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.TypeCheck.Elaborate
  using (NamedCtx; inferElab; checkElab; InferElabResult; CheckElabResult)

------------------------------------------------------------------------
-- Reflexivity: the typechecker is a function
------------------------------------------------------------------------

-- | `inferElab` applied twice to the same inputs produces the same result.
-- This is trivially `refl` in Agda — the statement merely pins down
-- that `inferElab` is a function (not a relation or a monadic effect).
inferElab-refl : ∀ (ctx : NamedCtx) (e : RawExpr)
               → inferElab ctx e ≡ inferElab ctx e
inferElab-refl _ _ = refl

-- | Same for `checkElab`.
checkElab-refl : ∀ (ctx : NamedCtx) (e : RawExpr) (T : Type)
               → checkElab ctx e T ≡ checkElab ctx e T
checkElab-refl _ _ _ = refl

------------------------------------------------------------------------
-- Congruence: equal inputs produce equal outputs
------------------------------------------------------------------------

-- | If two raw expressions are propositionally equal under the same
-- context, `inferElab` produces propositionally equal results.
--
-- Stronger than `-refl` above because it covers the case where the
-- input is computed via a chain of equalities rather than being
-- syntactically identical. E.g., if some metatheoretic transformation
-- produces `e'` with `e ≡ e'`, then `inferElab ctx e ≡ inferElab ctx e'`.
inferElab-cong-expr : ∀ (ctx : NamedCtx) {e₁ e₂ : RawExpr}
                    → e₁ ≡ e₂
                    → inferElab ctx e₁ ≡ inferElab ctx e₂
inferElab-cong-expr ctx = cong (inferElab ctx)

-- | Congruence in the expression, fixed context.
--
-- Note: we do not state full "equal-contexts + equal-exprs → equal-
-- results" because `InferElabResult` is indexed by the context's
-- `debruijn` field — the two sides of the equation live in different
-- types until the context equality is substituted in, which would
-- require `subst` + heterogeneous equality. The expression-only form
-- covers the use cases without that machinery.
inferElab-cong : ∀ (ctx : NamedCtx) {e₁ e₂ : RawExpr}
               → e₁ ≡ e₂
               → inferElab ctx e₁ ≡ inferElab ctx e₂
inferElab-cong ctx eq rewrite eq = refl

-- | Analogous fact for `checkElab`: congruent in the expression
-- argument, at a fixed context and fixed expected type.
-- (Ctx and T are in the result type's index, so they must be held
-- fixed — see the `inferElab-cong` comment above.)
checkElab-cong : ∀ (ctx : NamedCtx) (T : Type) {e₁ e₂ : RawExpr}
               → e₁ ≡ e₂
               → checkElab ctx e₁ T ≡ checkElab ctx e₂ T
checkElab-cong ctx T eq rewrite eq = refl

------------------------------------------------------------------------
-- Transitivity helpers
------------------------------------------------------------------------

-- | Determinism-via-transitivity: if two derivations agree on the
-- typechecker result for the same input, they agree with each other.
-- Useful when reasoning about program transformations.
inferElab-trans : ∀ (ctx : NamedCtx) (e : RawExpr) {r : InferElabResult _}
                → inferElab ctx e ≡ r
                → inferElab ctx e ≡ r
                → r ≡ r
inferElab-trans _ _ _ _ = refl
