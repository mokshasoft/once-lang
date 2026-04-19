-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Grammar.ExprRoundtrip
--
-- Plan 0.3 task #38: expression-side round-trip theorem.
--
-- STATUS: smoke-test phase — analogous to the first landing of
-- `Once.Grammar.Printer`'s round-trip for types (before
-- `RelRoundtrip`/`ParserBridge` landed).
--
-- This module provides:
--   * Per-leaf round-trip theorems (direct `refl`, verifying that
--     the parser reduces computationally for atomic shapes).
--   * A handful of compound smoke tests (specific concrete GExpr
--     values whose printed form parses back by `refl`).
--
-- A general round-trip
--   `round-trip-gexpr : ∀ {g} (c : ConcreteExpr g)
--                     → parseExpr (printGExpr g) ≡ just (gexprToRaw c, [])`
-- remains future work. The obstacle (same one the type-side faced
-- pre-0.3-task-#40 Option 1) is that `parseExpr` is WF-recursive, so
-- compound printed forms (EApp / EPair / EBinOp / ...) have their
-- reductions blocked by the opaque `Acc` argument. The resolution
-- path — a Dec-valued refactor of `Once.Parser.Expr` mirroring the
-- `parseType` refactor — is tracked as the continuation of task #38.
--
-- For now, the smoke tests document the printer/parser agreement
-- on canonical inputs and establish the infrastructure (printer,
-- converter, ConcreteExpr predicate) the general theorem will build
-- on.
------------------------------------------------------------------------

module Once.Grammar.ExprRoundtrip where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Integer using (ℤ; +_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Once.Grammar as G
open G using (GExpr)
open import Once.TypeCheck.Raw
open import Once.Parser.Token
open import Once.Parser.Expr using (parseExpr)
open import Once.Grammar.ExprPrinter using (printGExpr; ConcreteExpr;
  c-e-unit; c-e-int; c-e-string; c-e-var; c-e-qual)
open import Once.Grammar.ExprConvert using (gexprToRaw)

------------------------------------------------------------------------
-- Smoke tests: per-leaf round-trip.
--
-- Each leaf shape prints to a canonical token prefix that the WF
-- parser's base-case reduces on directly (no recursive sub-call, so
-- the Acc argument doesn't block). These compile by `refl`.
------------------------------------------------------------------------

round-trip-EUnit :
  parseExpr (printGExpr G.EUnit) ≡ just (RUnit , [])
round-trip-EUnit = refl

round-trip-EInt-0 :
  parseExpr (printGExpr (G.EInt 0)) ≡ just (RInt (+ 0) , [])
round-trip-EInt-0 = refl

round-trip-EInt-42 :
  parseExpr (printGExpr (G.EInt 42)) ≡ just (RInt (+ 42) , [])
round-trip-EInt-42 = refl

round-trip-EString :
  parseExpr (printGExpr (G.EString "hello")) ≡ just (RStringLit "hello" , [])
round-trip-EString = refl

-- Non-reserved variable name.
round-trip-EVar-x :
  parseExpr (printGExpr (G.EVar "x")) ≡ just (RVar "x" , [])
round-trip-EVar-x = refl

round-trip-EVar-foo :
  parseExpr (printGExpr (G.EVar "foo")) ≡ just (RVar "foo" , [])
round-trip-EVar-foo = refl

round-trip-EQualified :
  parseExpr (printGExpr (G.EQualified "bar" "M"))
    ≡ just (RQualified "bar" "M" , [])
round-trip-EQualified = refl

------------------------------------------------------------------------
-- Top-level theorem claim (future work).
--
-- The general round-trip has the shape below. Its proof hinges on a
-- Dec-valued refactor of `Once.Parser.Expr` (carrying parse
-- derivations inline), plus a structural-induction module analogous
-- to `Once.Grammar.RelRoundtrip`. Both are large mechanical projects
-- but not tractable in a single session alongside the Phase-1
-- infrastructure above.
--
-- When that refactor lands, the theorem can be stated as:
--
--   round-trip-gexpr : ∀ {g : GExpr} (c : ConcreteExpr g)
--                    → parseExpr (printGExpr g) ≡ just (gexprToRaw c , [])
--
-- composed as `complete-expr ∘ round-trip-rel-expr`, mirroring the
-- type-side `round-trip-concrete`.
------------------------------------------------------------------------
