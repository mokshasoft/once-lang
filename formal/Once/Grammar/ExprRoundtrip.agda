-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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
-- Compound smoke tests: experimentally verify the parser reduces on
-- small canonical inputs. These pin down concrete expectations the
-- eventual general theorem will have to match.
------------------------------------------------------------------------

-- (x, y) → RPair (RVar "x") (RVar "y")
round-trip-EPair-vars :
  parseExpr (printGExpr (G.EPair (G.EVar "x") (G.EVar "y")))
    ≡ just (RPair (RVar "x") (RVar "y") , [])
round-trip-EPair-vars = refl

-- (- x) → RUnaryOp OpNeg (RVar "x")
round-trip-ENeg-var :
  parseExpr (printGExpr (G.EUnaryOp G.OpNeg (G.EVar "x")))
    ≡ just (RUnaryOp OpNeg (RVar "x") , [])
round-trip-ENeg-var = refl

-- (\x -> x)
round-trip-ELam-id :
  parseExpr (printGExpr (G.ELam "x" (G.EVar "x")))
    ≡ just (RLam "x" (RVar "x") , [])
round-trip-ELam-id = refl

-- (f x)
round-trip-EApp-vars :
  parseExpr (printGExpr (G.EApp (G.EVar "f") (G.EVar "x")))
    ≡ just (RApp (RVar "f") (RVar "x") , [])
round-trip-EApp-vars = refl

-- (x + y)
round-trip-EBinOp-add :
  parseExpr (printGExpr (G.EBinOp G.OpAdd (G.EVar "x") (G.EVar "y")))
    ≡ just (RBinOp OpAdd (RVar "x") (RVar "y") , [])
round-trip-EBinOp-add = refl

-- (x * y)
round-trip-EBinOp-mul :
  parseExpr (printGExpr (G.EBinOp G.OpMul (G.EVar "x") (G.EVar "y")))
    ≡ just (RBinOp OpMul (RVar "x") (RVar "y") , [])
round-trip-EBinOp-mul = refl

-- (f . g) → RApp (RApp (RVar "compose") f) g
round-trip-ECompose-vars :
  parseExpr (printGExpr (G.ECompose (G.EVar "f") (G.EVar "g")))
    ≡ just (RApp (RApp (RVar "compose") (RVar "f")) (RVar "g") , [])
round-trip-ECompose-vars = refl

-- (let x = 1 in x)
round-trip-ELet-simple :
  parseExpr (printGExpr (G.ELet (("x" , G.EInt 1) ∷ []) (G.EVar "x")))
    ≡ just (RLet "x" (RInt (+ 1)) (RVar "x") , [])
round-trip-ELet-simple = refl

-- (destruct e of { Left x -> x ; Right y -> y })
round-trip-EDestruct :
  parseExpr (printGExpr (G.EDestruct (G.EVar "e") "x" (G.EVar "x")
                                      "y" (G.EVar "y")))
    ≡ just (RDestruct (RVar "e") "x" (RVar "x") "y" (RVar "y") , [])
round-trip-EDestruct = refl

-- Nested: ((x, y), z)
round-trip-EPair-nested :
  parseExpr (printGExpr (G.EPair (G.EPair (G.EVar "x") (G.EVar "y"))
                                   (G.EVar "z")))
    ≡ just (RPair (RPair (RVar "x") (RVar "y")) (RVar "z") , [])
round-trip-EPair-nested = refl

-- Comparison: (x < y)
round-trip-EBinOp-lt :
  parseExpr (printGExpr (G.EBinOp G.OpLt (G.EVar "x") (G.EVar "y")))
    ≡ just (RBinOp OpLt (RVar "x") (RVar "y") , [])
round-trip-EBinOp-lt = refl

-- Subtraction: (x - y)
round-trip-EBinOp-sub :
  parseExpr (printGExpr (G.EBinOp G.OpSub (G.EVar "x") (G.EVar "y")))
    ≡ just (RBinOp OpSub (RVar "x") (RVar "y") , [])
round-trip-EBinOp-sub = refl

-- (f x y) → RApp (RApp f x) y
round-trip-EApp-two-args :
  parseExpr (printGExpr (G.EApp (G.EApp (G.EVar "f") (G.EVar "x"))
                                  (G.EVar "y")))
    ≡ just (RApp (RApp (RVar "f") (RVar "x")) (RVar "y") , [])
round-trip-EApp-two-args = refl

------------------------------------------------------------------------
-- Partial general theorems: leaves proved generically.
--
-- These quantify over the name or value: every EInt, every EString,
-- every non-reserved EVar round-trips. Proves the leaf cases of the
-- general theorem, which a compound-case structural induction will
-- extend.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Data.Bool using (false; true; if_then_else_)
open import Once.Grammar.ExprPrinter using (ConcreteExpr; c-e-unit;
  c-e-int; c-e-string; c-e-var; c-e-qual)
open import Once.Grammar.ExprConvert using (gexprToRaw)
open import Once.Parser.Expr using (isReserved)

-- EInt: every integer round-trips.
round-trip-EInt :
  ∀ (n : ℕ)
  → parseExpr (printGExpr (G.EInt n)) ≡ just (RInt (+ n) , [])
round-trip-EInt n = refl

-- EString: every string round-trips.
round-trip-EString-gen :
  ∀ (s : String)
  → parseExpr (printGExpr (G.EString s)) ≡ just (RStringLit s , [])
round-trip-EString-gen s = refl

-- EUnit is nullary; covered above.

-- Note: a fully-generic EVar round-trip (quantifying over `name` with
-- `isReserved name ≡ false`) would additionally need `name ≢ "let"`
-- and `name ≢ "destruct"` hypotheses, because parseAtomExpr dispatches
-- on `_≟_` against those two strings before falling through to the
-- variable branch. Expressing that as a side condition is possible but
-- would weaken the statement; the deferred Phase 2/3 relational
-- approach is the right long-term path.

------------------------------------------------------------------------
-- Leaf-case round-trip packaged at the ConcreteExpr level.
--
-- For each leaf ConcreteExpr witness, the printed tokens parse back
-- to `gexprToRaw` of the witness. Compound constructors are handled
-- by parallel lemmas below or deferred to Phase 2/3.
------------------------------------------------------------------------

round-trip-c-e-unit :
  parseExpr (printGExpr G.EUnit) ≡ just (gexprToRaw c-e-unit , [])
round-trip-c-e-unit = refl

round-trip-c-e-int :
  ∀ {n} → parseExpr (printGExpr (G.EInt n))
        ≡ just (gexprToRaw (c-e-int {n}) , [])
round-trip-c-e-int = refl

round-trip-c-e-string :
  ∀ {s} → parseExpr (printGExpr (G.EString s))
        ≡ just (gexprToRaw (c-e-string {s}) , [])
round-trip-c-e-string = refl

-- EVar / EQualified: a ConcreteExpr-witness-level round-trip for
-- these needs additional `name ≢ "let"` / `name ≢ "destruct"` side
-- conditions because of parseAtomExpr's dispatch structure. See the
-- note on `round-trip-EVar-gen` above. The concrete smoke tests
-- `round-trip-EVar-x` / `round-trip-EVar-foo` / `round-trip-EQualified`
-- cover canonical instances.

------------------------------------------------------------------------
-- Top-level theorem (Phase 3c of task #38, fully landed).
--
-- Phase 3a: `Once.Parser.ExprRelation` — inductive parsing relations.
-- Phase 3b: `Once.Parser.Expr` Dec-valued refactor — each parser
--   returns the derivation inline.
-- Phase 3c: `Once.Grammar.ExprBridge` — soundness + completeness
--   bridges between the relation and the WF-parser.
-- Phase 3c: `Once.Grammar.ExprRelRoundtrip` — structural round-trip
--   `round-trip-rel-expr`: for every `ConcreteExpr g`,
--   `ParsesExpr (printGExpr g) (gexprToRaw c) []`.
--
-- The round-trip follows by composing `round-trip-rel-expr` (the
-- structural direction) with `complete-expr` (the WF-function
-- completeness bridge).
------------------------------------------------------------------------

open import Once.Grammar.ExprRelRoundtrip using (round-trip-rel-expr)
open import Once.Grammar.ExprBridge using (complete-expr)

round-trip-concrete-expr :
  ∀ {g : GExpr} (c : ConcreteExpr g)
  → parseExpr (printGExpr g) ≡ just (gexprToRaw c , [])
round-trip-concrete-expr c = complete-expr (round-trip-rel-expr c)
