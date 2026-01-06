{-# OPTIONS --sized-types #-}
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
  using (RawExpr; RVar; RApp; RLam; RLet; RPair; RCase; RUnit; RInt; RStringLit; RAnnot; RBinOp; RUnaryOp)
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

-- Type inference
open import Once.TypeCheck.Infer public
  using (InferResult; success; failure)
  using (infer; check)
  using (Fresh; freshTVar)
  using (generatorType)

-- Soundness (for documentation; theorems are postulated)
open import Once.TypeCheck.Sound public
  using (WellTyped; Soundness; soundness)
  using (Closed; Decidable; decidable)

-- Combined inference + elaboration (OCP-0004)
open import Once.TypeCheck.Elaborate as Elaborate public
  using (weaken; exchange)
  using (InferElabResult)
  using (NamedCtx; emptyCtx; extendNamedCtx)
  using (lookupVar)
  using (inferElab)
  using (compileExpr; compileExprTyped)

------------------------------------------------------------------------
-- Convenience API
------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero)

-- | Type check an expression in the empty context
typeCheck : RawExpr → InferResult
typeCheck e = infer ∅ e zero

-- | Type check an expression against an expected type
typeCheckAgainst : RawExpr → Type → InferResult
typeCheckAgainst e expected = check ∅ e expected zero

------------------------------------------------------------------------
-- Example Usage
------------------------------------------------------------------------

-- Example: Type checking identity function λx.x
-- Should infer type α → α for fresh type variable α
private
  open import Data.Integer using (+_)

  -- λx.x has type t0 → t0
  example-id : InferResult
  example-id = typeCheck (RLam "x" (RVar "x"))

  -- (λx.x) () should have type Unit
  example-app : InferResult
  example-app = typeCheck (RApp (RLam "x" (RVar "x")) RUnit)

  -- 1 + 2 should have type Int
  example-arith : InferResult
  example-arith = typeCheck (RBinOp OpAdd (RInt (+ 1)) (RInt (+ 2)))

  -- 1 < 2 should have type Unit + Unit (Bool)
  example-cmp : InferResult
  example-cmp = typeCheck (RBinOp OpLt (RInt (+ 1)) (RInt (+ 2)))

