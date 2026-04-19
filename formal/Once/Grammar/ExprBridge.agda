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
--   * `complete-opExprWFraw`, `complete-*TailWFraw` and partial
--     machinery toward a WF-parser completeness bridge analogous to
--     `complete-typeWFraw` in `Once.Grammar.ParserBridge`.
--
-- STATUS (task #38 Phase 3c): The tail parsers, cmp/add/mul/comp
-- level parsers, and leaf-atom completeness are mechanical. The
-- variable/qualified atom-expr case exposes a relation-level
-- non-determinism: `pae-var` accepts ANY residual `rest`, but the
-- parser dispatches on whether `rest` begins with `TAt ∷ TWord _ ∷ _`,
-- committing to `pae-qual` in that case. A fully general
-- `complete-expr` requires either (a) adding a `NotQualPrefix rest`
-- side-condition to `pae-var`, or (b) weakening the statement to a
-- canonical-derivation hypothesis.
--
-- Plan 0.3 task #38 Phase 3c.
------------------------------------------------------------------------

module Once.Grammar.ExprBridge where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; ∃; ∃-syntax)
open import Data.Nat using (ℕ; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; <-trans; ≤-<-trans; <⇒≤;
                                        n≤1+n; m≤n⇒m≤1+n)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; cong; sym; trans; subst)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.String using (String)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false)

open import Once.TypeCheck.Raw using (RawExpr; RVar; RQualified; RApp; RLam;
                                       RLet; RPair; RDestruct; RUnit; RInt;
                                       RStringLit; RAnnot; RBinOp; RUnaryOp;
                                       OpAdd; OpSub; OpMul; OpDiv; OpMod;
                                       OpLt; OpLe; OpGt; OpGe; OpEq; OpNe;
                                       OpNeg)
open import Once.Parser.Token
open import Once.Parser.Expr
open import Once.Parser.ExprRelation
open import Once.Grammar.ParserBridge using (complete-typeWFraw)
open import Once.Parser.TypeRelation using (ParsesType-shrinks)

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
-- Helpers for completeness proofs.
------------------------------------------------------------------------

-- Absurd-helper: contradiction between `b ≡ true` and `b ≡ false`.
bool-absurd :
  ∀ {b : Bool} → b ≡ true → b ≡ false → ⊥
bool-absurd refl ()

------------------------------------------------------------------------
-- Completeness for the operator-as-expression parser, which is
-- structurally recursive on the tokens (not WF).
------------------------------------------------------------------------

complete-opExprWFraw :
  ∀ {toks acc e rest} → ParsesOpExpr acc toks e rest
  → ∃ λ (d' : ParsesOpExpr acc toks e rest)
  → parseOpExprWF toks acc ≡ just (e , rest , d')
complete-opExprWFraw poe-close = _ , refl
complete-opExprWFraw (poe-dot d)
  with complete-opExprWFraw d
... | _ , eq rewrite eq = _ , refl
complete-opExprWFraw (poe-plus d)
  with complete-opExprWFraw d
... | _ , eq rewrite eq = _ , refl
complete-opExprWFraw (poe-minus d)
  with complete-opExprWFraw d
... | _ , eq rewrite eq = _ , refl
complete-opExprWFraw (poe-star d)
  with complete-opExprWFraw d
... | _ , eq rewrite eq = _ , refl
complete-opExprWFraw (poe-slash d)
  with complete-opExprWFraw d
... | _ , eq rewrite eq = _ , refl
complete-opExprWFraw (poe-percent d)
  with complete-opExprWFraw d
... | _ , eq rewrite eq = _ , refl
complete-opExprWFraw (poe-lt d)
  with complete-opExprWFraw d
... | _ , eq rewrite eq = _ , refl
complete-opExprWFraw (poe-gt d)
  with complete-opExprWFraw d
... | _ , eq rewrite eq = _ , refl
complete-opExprWFraw (poe-pipe d)
  with complete-opExprWFraw d
... | _ , eq rewrite eq = _ , refl
complete-opExprWFraw (poe-amp d)
  with complete-opExprWFraw d
... | _ , eq rewrite eq = _ , refl
complete-opExprWFraw (poe-at d)
  with complete-opExprWFraw d
... | _ , eq rewrite eq = _ , refl
