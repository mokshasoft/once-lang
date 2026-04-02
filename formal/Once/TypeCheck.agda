-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.TypeCheck
--
-- Main entry point for the verified type checker.
-- This module re-exports the type checking API for MAlonzo extraction.
--
-- Part of OCP-0003: Verified Type Checker
------------------------------------------------------------------------

module Once.TypeCheck where

------------------------------------------------------------------------
-- Re-exports
------------------------------------------------------------------------

-- Types
open import Once.Type public
  using (Type; Unit; Void; Int; Float; Str; Buffer; _*_; _+_; _⇒_; Eff; Fix; TVar)

-- Raw syntax (parser output)
open import Once.TypeCheck.Raw public
  using (RawExpr; RVar; RApp; RLam; RLet; RPair; RDestruct; RUnit; RInt; RStringLit; RAnnot; RBinOp; RUnaryOp)
  using (BinOp; OpAdd; OpSub; OpMul; OpDiv; OpMod; OpLt; OpLe; OpGt; OpGe; OpEq; OpNe)
  using (UnaryOp; OpNeg)
  using (isComparisonOp; isArithmeticOp)

-- Typing contexts
open import Once.TypeCheck.Context public
  using (Ctx; ∅; _,_∷_; lookup; LookupResult; found; notFound)
  using (Binding; mkBinding; name; type; quantity)

-- Quantities (from Once.Type)
open import Once.Type public
  using (Quantity; Zero; One; Many)

-- Type errors
open import Once.TypeCheck.Error public
  using (TypeError; UnboundVariable; TypeMismatch; NotAFunction; OccursCheck; UnificationError)
  using (ArithNonInteger; CompareNonInteger)
  using (Result; ok; fail)

-- Unification
open import Once.TypeCheck.Unify public
  using (Subst; emptySubst; singleSubst; applySubst; composeSubst)
  using (unify; UnifyResult; unified; failed)
  using (occurs)

-- Combined inference + elaboration (intrinsically typed)
-- Soundness is trivial by construction: if inferElab returns success,
-- the expression IS well-typed (the type is encoded in the term).
open import Once.TypeCheck.Elaborate as Elaborate public
  using (InferElabResult)
  renaming (success to elab-success; failure to elab-failure)
  using (NamedCtx; emptyCtx; extendNamedCtx)
  using (lookupVar)
  using (inferElab; checkElab)
  using (compileExpr; compileExprTyped)

-- Thinning operations (weaken, exchange)
open import Once.Surface.Thinning public
  using (weaken; exchange)

-- Surface syntax (for empty context S∅)
open import Once.Surface.Syntax public
  using () renaming (∅ to S∅)

------------------------------------------------------------------------
-- Convenience API
------------------------------------------------------------------------

-- | Type check an expression in the empty context
-- Returns an intrinsically-typed result (soundness by construction)
typeCheck : RawExpr → InferElabResult S∅
typeCheck e = inferElab emptyCtx e

------------------------------------------------------------------------
-- Example Usage
------------------------------------------------------------------------

-- Example: Type checking identity function λx.x
-- Should infer type α → α for fresh type variable α
private
  open import Data.Integer using (+_)

  -- λx.x has type t0 → t0
  example-id : InferElabResult S∅
  example-id = typeCheck (RLam "x" (RVar "x"))

  -- (λx.x) () should have type Unit
  example-app : InferElabResult S∅
  example-app = typeCheck (RApp (RLam "x" (RVar "x")) RUnit)

  -- 1 + 2 should have type Int
  example-arith : InferElabResult S∅
  example-arith = typeCheck (RBinOp OpAdd (RInt (+ 1)) (RInt (+ 2)))

  -- 1 < 2 should have type Unit + Unit (Bool)
  example-cmp : InferElabResult S∅
  example-cmp = typeCheck (RBinOp OpLt (RInt (+ 1)) (RInt (+ 2)))