-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.Error
--
-- Plan 0.3, gap G4: structured error types for the type-checker.
--
-- The elaborator currently signals failure via raw `String`. A
-- structured `TypeError` datatype would give:
--   * machine-readable error categories for tooling (IDE, LSP),
--   * uniqueness-by-shape (two failures with the same structured
--     error are *propositionally* equal, independent of how their
--     rendered strings happen to be spelled),
--   * and a stable contract for error-preservation theorems
--     ("this failure path reaches this specific variant").
--
-- Full G4 would refactor the elaborator's failure injection from
-- `String` to `TypeError` — cascading through every `failure` call
-- site and every consumer of `InferElabResult.failure`. Large diff.
--
-- This module takes the lighter-touch approach: define `TypeError`
-- as a parallel vocabulary + a `renderError : TypeError → String`
-- that reproduces the elaborator's existing strings. Then prove
-- selected error-preservation theorems in `TypeCheck.ErrorProofs`
-- ("when `inferElab` fails at an unbound variable, the emitted
-- string equals `renderError (UnboundVariable x)` for some `x`").
--
-- Reference: plans/0.3-frontend-verification-gaps.md, gap G4.
------------------------------------------------------------------------

module Once.TypeCheck.Error where

open import Data.String using (String; _++_)
open import Once.Spec.Grade using (Quantity)
open import Once.Spec.Type using (Ty; Type)
open import Once.Type using (showQuantity; showType; showPolyType)
open import Once.Spec.Surface.Syntax using (PolyType)
open import Once.Spec.Theory using (NumTy; int; float)
open import Once.Spec.Surface.Operator using (BinOp; Op; Dottable; plain; dotted; ‹_›; o%; o+; o-; o*; o/; o<; o<=; o>; o>=; o==; o!=)

-- | An operator as written.
dottableText : Dottable → String
dottableText o+  = "+"
dottableText o-  = "-"
dottableText o*  = "*"
dottableText o/  = "/"
dottableText o<  = "<"
dottableText o<= = "<="
dottableText o>  = ">"
dottableText o>= = ">="
dottableText o== = "=="
dottableText o!= = "!="

opText : BinOp → String
opText (plain ‹ d ›) = dottableText d
opText (plain o%)    = "%"
opText (dotted d)    = dottableText d ++ "."

numTyText : NumTy → String
numTyText int   = "Int"
numTyText float = "Float"

-- | Plan 0.150 step 5: an operator undefined at a type names the one that is
-- (`Float`'s arithmetic rounds, so it is the dotted family; `Int`'s is exact).
undefinedHint : String → NumTy → String
undefinedHint "+"  float = ", whose addition rounds: use `+.`"
undefinedHint "-"  float = ", whose subtraction rounds: use `-.`"
undefinedHint "*"  float = ", whose multiplication rounds: use `*.`"
undefinedHint "/"  float = ", whose division rounds: use `/.`"
undefinedHint "%"  float = ", which has no remainder"
undefinedHint "+." int   = ", whose addition is exact: use `+`"
undefinedHint "-." int   = ", whose subtraction is exact: use `-`"
undefinedHint "*." int   = ", whose multiplication is exact: use `*`"
undefinedHint "/." int   = ", whose division is on integers: use `/`"
undefinedHint "==." int  = ": use `==`"
undefinedHint "!=." int  = ": use `!=`"
undefinedHint "<." int   = ": use `<`"
undefinedHint "<=." int  = ": use `<=`"
undefinedHint ">." int   = ": use `>`"
undefinedHint ">=." int  = ": use `>=`"
{-# CATCHALL #-}
undefinedHint _    _     = ""

------------------------------------------------------------------------
-- Structured error categories
------------------------------------------------------------------------

-- | Machine-readable typechecker error variants.
--
-- Each variant corresponds to a distinct semantic failure mode. The
-- variants are grouped by the Expr form that produces them:
--
--   * Variable lookups — `UnboundVariable`, `UnboundQualified`.
--   * Mode mismatches — `LambdaInInferMode`, `InlInInferMode`, etc.
--   * Type-shape mismatches — `FstNeedsPair`, `SndNeedsPair`, …
--   * Annotation / check-mode — `TypeMismatch`, `NoInstance`.
--   * Usage (QTT) — `UsageViolation`.
--   * Builtin specialization — `BuiltinTypeMismatch`.
--
-- The list mirrors every distinct `failure "…"` call site in
-- `Once.TypeCheck.Elaborate`, and every variant is produced by one (plan 0.139). Adding a new failure mode to the
-- elaborator is a deliberate act: it must correspond to a new
-- variant here, or re-use an existing one.
data TypeError : Set where
  -- Variable resolution failures
  UnboundVariable         : String → TypeError
  UnboundQualified        : (name alias : String) → TypeError

  -- Plan 0.58: a SigOp/FFI reference whose type is not concrete (not a base
  -- type nor a first-order function pointer) cannot cross the register ABI.
  NonConcreteSigOpType    : (name : String) (T : Type) → TypeError

  -- Mode-specific rejections
  LambdaInInferMode         : TypeError
  LambdaRequiresFunctionType : TypeError
  InlInInferMode            : TypeError
  InrInInferMode            : TypeError
  InitialInInferMode        : TypeError
  -- `id`, `fst`, `snd`, `terminal` used bare where nothing gives their type:
  -- polymorphic, so they take their instance from a target (plan 0.139).
  GeneratorInInferMode      : (name : String) → TypeError
  InlNeedsSumType           : TypeError
  InrNeedsSumType           : TypeError

  -- Type-shape mismatches on builtin-specific argument forms
  FstNeedsPair        : TypeError
  SndNeedsPair        : TypeError
  CaseScrutineeNotSum : TypeError
  CaseBranchMismatch  : TypeError

  -- Annotation / check-mode mismatches
  TypeMismatch            : ∀ {m} (expected actual : Ty m) → TypeError

  -- Type-shape errors emitted by the `asInt` / `asFun` projection
  -- views when the inferred sub-result has the wrong shape. Used by
  -- RBinOp (via asInt on each operand) and generic RApp (via asFun
  -- on the function position).
  NotFunction : ∀ {m} (actual : Ty m) → TypeError  -- "expected function, got X"

  -- Usage (QTT) violations
  UsageViolation : (name : String) (declared actual : Quantity) → TypeError

  -- Per-builtin type-shape mismatches in check mode
  BuiltinTypeMismatch : (builtin-name : String) → TypeError

  -- Plan 0.139 (D1/D2): a polymorphic name (a generator such as `id`, or an
  -- own definition with type parameters) is used where its type is known, and
  -- no instance of its schema is that type: `schema` is the part of the
  -- name's type that was matched (the whole type, or its domain when the
  -- name is applied), `actual` the known type. A type mismatch, not an
  -- ambiguity: the target is known and nothing fits it.
  NoInstance : ∀ {m} (name : String) (schema : PolyType) (actual : Ty m) → TypeError

  -- Plan 0.94 §10: `compose f g`'s middle type is determined locally — by `g`
  -- given its input, or by `f`'s synthesized type — and here neither determines
  -- it. The fix is an annotation.
  ComposeMiddleUndetermined : TypeError

  -- Plan 0.150: a numeric operator at a number type whose row lacks the
  -- operator's theory (`+` at `Float`), and an operator on an `Int` and a
  -- `Float` (D408: no implicit conversion).
  OperatorUndefined : (op : String) (at : NumTy) → TypeError
  MixedOperands     : (op : String) → TypeError
  -- A literal `-0.0` (plan 0.150 N5): negative zero is reached by negation.
  NegativeZeroLiteral : TypeError

  -- Binary operator sub-errors: wraps a sub-error from either side.
  BinOpLeftError  : TypeError → TypeError
  BinOpRightError : TypeError → TypeError


------------------------------------------------------------------------
-- Rendering
------------------------------------------------------------------------

-- | Render a structured error to the same string the elaborator
-- currently emits. Provides a one-way link from structured to
-- unstructured: whenever the elaborator emits `renderError err`, we
-- can cite the structured variant `err` that caused it.
--
-- The reverse direction (String → TypeError) is not total — it would
-- require parsing the strings back, which is fragile. We instead
-- prove per-failure-path theorems in `TypeCheck.ErrorProofs` that
-- pin each elaborator `failure "…"` call to a specific variant.
renderError : TypeError → String
renderError (UnboundVariable x) =
  "Unbound or unspecialized variable: " ++ x
    ++ " (polymorphic builtins must appear applied or in check mode)"
renderError (UnboundQualified name alias) =
  "Unbound qualified variable: " ++ name ++ "@" ++ alias
renderError (NonConcreteSigOpType name T) =
  "Reference '" ++ name ++ "' has non-concrete type " ++ showType T
    ++ " (FFI/SigOp references must be base types or first-order function pointers)"
renderError LambdaInInferMode =
  "Lambda without type annotation not supported in inference mode."
renderError LambdaRequiresFunctionType =
  "Lambda requires function type"
renderError InlInInferMode =
  "inl requires check mode (needs target sum type)"
renderError InrInInferMode =
  "inr requires check mode (needs target sum type)"
renderError InitialInInferMode =
  "initial requires check mode (needs target type)"
renderError (GeneratorInInferMode name) =
  name ++ " requires check mode (needs target type)"
renderError InlNeedsSumType =
  "inl expects a sum type in check mode"
renderError InrNeedsSumType =
  "inr expects a sum type in check mode"
renderError FstNeedsPair =
  "fst requires a pair argument"
renderError SndNeedsPair =
  "snd requires a pair argument"
renderError CaseScrutineeNotSum =
  "Case requires a sum-typed scrutinee"
renderError CaseBranchMismatch =
  "Case branches have different types"
renderError (TypeMismatch expected actual) =
  "Type mismatch: expected " ++ showType expected
    ++ " but got " ++ showType actual
renderError (NotFunction actual) =
  "expected function type, got " ++ showType actual
renderError (UsageViolation name declared actual) =
  "Parameter '" ++ name ++ "' used with quantity "
    ++ showQuantity actual ++ " but declared with quantity "
    ++ showQuantity declared
renderError (BuiltinTypeMismatch name) =
  name ++ ": expected type mismatch"
renderError (NoInstance name schema actual) =
  name ++ ": " ++ showType actual ++ " is not an instance of " ++ showPolyType schema
renderError ComposeMiddleUndetermined =
  "compose: cannot determine the middle type — neither the second argument's "
    ++ "output (given its input) nor the first argument's input is known; "
    ++ "annotate one of them"
renderError (OperatorUndefined op A) =
  "`" ++ op ++ "` is not defined at " ++ numTyText A ++ undefinedHint op A
renderError (MixedOperands op) =
  "`" ++ op ++ "` needs operands of one type: convert the Int with toFloat"
renderError NegativeZeroLiteral =
  "the literal -0.0 is not allowed: write -(0.0) for negative zero"
renderError (BinOpLeftError sub) =
  "binop left: " ++ renderError sub
renderError (BinOpRightError sub) =
  "binop right: " ++ renderError sub
