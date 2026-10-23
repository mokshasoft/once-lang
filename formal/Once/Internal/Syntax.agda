{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Internal.Syntax — the terms a programmer writes.
--
-- `RawExpr` is the abstract syntax of an expression after parsing, with named
-- variables: the Spec's `Spec.Surface.Syntax.Expr`. A qualified reference is first `RQualified name alias`; name
-- resolution (`Spec.Resolution`) replaces it by `RResolved` of the canonical
-- name it denotes (`Spec.Name`). The typing judgment (`Spec.Typing`) is stated
-- over resolved terms.
------------------------------------------------------------------------

module Once.Internal.Syntax where

open import Data.Bool using (Bool; true; false)
open import Data.Integer using (ℤ)
open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Once.Spec.Type using (Type)
open import Once.Spec.Type using (Fun)
open import Once.Spec.Name using (CanonicalName)
open import Once.Spec.Surface.Syntax
  using (Expr; BinOp; RVar; RQualified; RResolved; RApp; RLam; RLet; RPair; RDestruct; RUnit; RInt; RFloat;
         RAnnot; RBinOp; RNeg; OpAdd; OpSub; OpMul; OpDiv; OpMod; OpLt; OpLe; OpGt; OpGe; OpEq; OpNe)

------------------------------------------------------------------------
-- Expressions: the Spec's (plan 0.122). `RawExpr` is the compiler's name
-- for them, apart from its elaborated `Surface.Syntax.Expr`.
------------------------------------------------------------------------

RawExpr : Set
RawExpr = Expr

------------------------------------------------------------------------
-- Operator classes (the typing rules for operators are stated by class)
------------------------------------------------------------------------

isComparisonOp : BinOp → Bool
isComparisonOp OpLt  = true
isComparisonOp OpLe  = true
isComparisonOp OpGt  = true
isComparisonOp OpGe  = true
isComparisonOp OpEq  = true
isComparisonOp OpNe  = true
isComparisonOp OpAdd = false
isComparisonOp OpSub = false
isComparisonOp OpMul = false
isComparisonOp OpDiv = false
isComparisonOp OpMod = false

-- The operators defined on `Float`. `%` is not: `fmod` is a different
-- function from the integer remainder, and is not given a meaning.
isFloatArithmeticOp : BinOp → Bool
isFloatArithmeticOp OpAdd = true
isFloatArithmeticOp OpSub = true
isFloatArithmeticOp OpMul = true
isFloatArithmeticOp OpDiv = true
isFloatArithmeticOp OpMod = false
isFloatArithmeticOp OpLt  = false
isFloatArithmeticOp OpLe  = false
isFloatArithmeticOp OpGt  = false
isFloatArithmeticOp OpGe  = false
isFloatArithmeticOp OpEq  = false
isFloatArithmeticOp OpNe  = false

isArithmeticOp : BinOp → Bool
isArithmeticOp OpAdd = true
isArithmeticOp OpSub = true
isArithmeticOp OpMul = true
isArithmeticOp OpDiv = true
isArithmeticOp OpMod = true
isArithmeticOp OpLt  = false
isArithmeticOp OpLe  = false
isArithmeticOp OpGt  = false
isArithmeticOp OpGe  = false
isArithmeticOp OpEq  = false
isArithmeticOp OpNe  = false

------------------------------------------------------------------------
-- The forms without a checking rule of their own
------------------------------------------------------------------------

-- A closed expression of one of these forms may be checked against a type by
-- inferring its type and converting (the subsumption rule of a bidirectional
-- system applies only to forms that are not introductions). Leaving `RLam`
-- out matters: otherwise a lambda would have two checking derivations with
-- different meanings. The other introduction forms have their own rules.
data ClosedLiftShape : RawExpr → Set where
  cls-var    : ∀ {x}         → ClosedLiftShape (RVar x)
  cls-qual   : ∀ {n a}       → ClosedLiftShape (RQualified n a)
  cls-res    : ∀ {cn}        → ClosedLiftShape (RResolved cn)
  cls-let    : ∀ {x e₁ e₂}   → ClosedLiftShape (RLet x e₁ e₂)
  cls-destr  : ∀ {s x eL y eR} → ClosedLiftShape (RDestruct s x eL y eR)
  cls-unit   :                 ClosedLiftShape RUnit
  cls-annot  : ∀ {e T}       → ClosedLiftShape (RAnnot e T)
  cls-binop  : ∀ {op a b}    → ClosedLiftShape (RBinOp op a b)
