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
--   * `complete-expr` : `ParsesExpr toks e rest → parseExpr toks ≡ just (e, rest)`
--     — WF-parser completeness. The mutual case-enumeration is
--     very large (~1500-2000 lines mirroring `complete-typeWFraw` in
--     `Once.Grammar.ParserBridge`) and carries a collection of
--     `with`-abstraction friction points (mainly around the parser's
--     `with isReserved s in eqR` / `with w ≟ "in"` dispatch) that
--     need a coordinated parser-side view refactor before the
--     completeness writeout becomes mechanical.
--
--     For this landing we STATE `complete-expr` as a postulate so
--     downstream `round-trip-concrete-expr` composes cleanly. The
--     body will be discharged once the parser-side view refactor
--     lands (tracked as a follow-up to task #38; the structural
--     proof `round-trip-rel-expr` is already in place, so the
--     remaining work is strictly the WF↔relation translation).
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

------------------------------------------------------------------------
-- Completeness (postulated — see header comment for the rationale).
--
-- The mechanical writeout mirrors `complete-typeWFraw` in
-- `Once.Grammar.ParserBridge` but at ~3× the scale (7 mutual members
-- for types; 17+ for expressions). All of the structural shrink
-- lemmas (`ParsesX-shrinks`) and the per-constructor relation-
-- roundtrip (`round-trip-rel-expr`) that the full proof builds on
-- are already in place; what remains is strictly per-clause
-- case enumeration + careful with-abstraction management for the
-- `isReserved` / `_ ≟ "in"` / `_ ≟ "Left"` dispatches.
------------------------------------------------------------------------

postulate
  complete-expr :
    ∀ {toks e rest} → ParsesExpr toks e rest
    → parseExpr toks ≡ just (e , rest)
