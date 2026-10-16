{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Lang.Syntax — the terms a programmer writes.
--
-- `RawExpr` is the abstract syntax of an expression after parsing, with named
-- variables. A qualified reference is first `RQualified name alias`; name
-- resolution (`Spec.Resolution`) replaces it by `RResolved` of the canonical
-- name it denotes (`Spec.Name`). The typing judgment (`Spec.Typing`) is stated
-- over resolved terms.
------------------------------------------------------------------------

module Once.Lang.Syntax where

open import Data.Bool using (Bool; true; false)
open import Data.Integer using (ℤ)
open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Once.Lang.Type using (Type; Functor)
open import Once.Spec.Name using (CanonicalName)

------------------------------------------------------------------------
-- Operators
------------------------------------------------------------------------

data BinOp : Set where
  OpAdd : BinOp    -- a + b
  OpSub : BinOp    -- a - b
  OpMul : BinOp    -- a * b
  OpDiv : BinOp    -- a / b
  OpMod : BinOp    -- a % b
  OpLt  : BinOp    -- a < b
  OpLe  : BinOp    -- a <= b
  OpGt  : BinOp    -- a > b
  OpGe  : BinOp    -- a >= b
  OpEq  : BinOp    -- a == b
  OpNe  : BinOp    -- a != b

data UnaryOp : Set where
  OpNeg : UnaryOp  -- -x

------------------------------------------------------------------------
-- Expressions
------------------------------------------------------------------------

data RawExpr : Set where
  RVar       : String → RawExpr                       -- x
  RQualified : String → String → RawExpr              -- name@alias
  RResolved  : CanonicalName → RawExpr                -- a resolved reference
  RApp       : RawExpr → RawExpr → RawExpr            -- f a
  RLam       : String → RawExpr → RawExpr             -- \x -> e
  RLet       : String → RawExpr → RawExpr → RawExpr   -- let x = e₁ in e₂
  RPair      : RawExpr → RawExpr → RawExpr            -- (e₁, e₂)
  -- destruct e | x -> e₁ | y -> e₂: the first branch takes the left
  -- injection, the second the right one.
  RDestruct  : RawExpr → String → RawExpr → String → RawExpr → RawExpr
  RUnit      : RawExpr                                -- ()
  RInt       : ℤ → RawExpr                            -- an integer literal
  -- A decimal literal as written: integer part, fraction digits, number of
  -- fraction digits, and its source offset (used only for warnings).
  RFloat     : ℕ → ℕ → ℕ → ℕ → RawExpr
  RStringLit : String → RawExpr
  RAnnot     : RawExpr → Type → RawExpr               -- (e : T)
  RBinOp     : BinOp → RawExpr → RawExpr → RawExpr
  RUnaryOp   : UnaryOp → RawExpr → RawExpr
  -- The unfold into `ν F`, carrying `F`. Not produced by the parser.
  RAna       : Functor → RawExpr → RawExpr

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
  cls-str    : ∀ {s}         → ClosedLiftShape (RStringLit s)
  cls-annot  : ∀ {e T}       → ClosedLiftShape (RAnnot e T)
  cls-binop  : ∀ {op a b}    → ClosedLiftShape (RBinOp op a b)
