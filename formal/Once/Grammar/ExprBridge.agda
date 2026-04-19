-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Grammar.ExprBridge
--
-- Bridges the inductive parsing relations (`ParsesX`, in
-- `Once.Parser.ExprRelation`) with the WF-based parser functions in
-- `Once.Parser.Expr`. Mirrors `Once.Grammar.ParserBridge` for the
-- type side.
--
-- Provides:
--   * `sound-expr`    : `parseExpr toks ≡ just (e, rest) → ParsesExpr toks e rest`
--     — trivial projection from the Dec-valued parser's inline
--     derivation witness.
--
-- The `complete-expr` direction (WF-parser completeness) is delayed to
-- a future commit — the mechanical case-enumeration is large (the
-- type-side analog is ~500 lines; expressions add ~700 more for the
-- operator / comparison / unary levels) and the foundational
-- refactors (NotAtomStart / Quiet / AppArgOk / ParsesOpExpr's
-- accumulator index) landed ahead of the big writeout. See this
-- module's git history and `Once.Grammar.ExprRelRoundtrip` for the
-- structural round-trip that the function-level bridge would compose
-- with.
--
-- Plan 0.3 task #38 Phase 3c.
------------------------------------------------------------------------

module Once.Grammar.ExprBridge where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; ∃; ∃-syntax)
open import Data.Nat using (ℕ; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; sym; trans; subst)

open import Once.TypeCheck.Raw using (RawExpr)
open import Once.Parser.Token
open import Once.Parser.Expr
open import Once.Parser.ExprRelation

------------------------------------------------------------------------
-- Inversion lemmas: converting a `stripX ≡ just ...` equation back to
-- the underlying Σ-carrying value so its derivation is exposed.
------------------------------------------------------------------------

stripExpr-inv :
  ∀ toks (r : ParseExprD toks) {e rest}
  → stripExpr toks r ≡ just (e , rest)
  → ∃ λ (d : ParsesExpr toks e rest) → r ≡ just (e , rest , d)
stripExpr-inv toks nothing ()
stripExpr-inv toks (just (e , rest , d)) refl = d , refl

------------------------------------------------------------------------
-- Soundness: a successful parse produces a derivation.
------------------------------------------------------------------------

sound-expr :
  ∀ {toks e rest} → parseExpr toks ≡ just (e , rest)
  → ParsesExpr toks e rest
sound-expr {toks} eq
  with stripExpr-inv toks (parseExprWF toks (<-wellFounded (length toks))) eq
... | d , _ = d
