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
open import Once.Type using (Type; Quantity; showQuantity; showType)
open import Data.Nat using (ℕ)
open import Data.Nat.Show using () renaming (show to showNatE)

------------------------------------------------------------------------
-- Structured error categories
------------------------------------------------------------------------

-- | Machine-readable typechecker error variants.
--
-- Each variant corresponds to a distinct semantic failure mode. The
-- variants are grouped by the RawExpr form that produces them:
--
--   * Variable lookups — `UnboundVariable`, `UnboundQualified`.
--   * Mode mismatches — `LambdaInInferMode`, `InlInInferMode`, etc.
--   * Type-shape mismatches — `FstNeedsPair`, `NegationNotInt`, …
--   * Application/annotation — `ApplicationTypeMismatch`,
--     `TypeMismatch`.
--   * Usage (QTT) — `UsageViolation`.
--   * Builtin specialization — `BuiltinTypeMismatch`.
--
-- The list mirrors every distinct `failure "…"` call site in
-- `Once.TypeCheck.Elaborate`. Adding a new failure mode to the
-- elaborator is a deliberate act: it must correspond to a new
-- variant here, or re-use an existing one.
data TypeError : Set where
  -- Variable resolution failures
  UnboundVariable         : String → TypeError
  UnboundQualified        : (name alias : String) → TypeError

  -- Plan 0.58: a SigOp/FFI reference whose type is not concrete (not a base
  -- type nor a first-order function pointer) cannot cross the register ABI.
  NonConcreteSigOpType    : (name : String) (T : Type) → TypeError

  -- PLAN 0.71 F4 / D112: a float literal that is not EXACTLY representable at
  -- the target's format. `0.5`, `1.5`, `2.25` are accepted; `0.1` and `3.14`
  -- are not, and are rejected rather than rounded — because `Float`'s width is
  -- a target property, so a rounded literal would denote a different number on
  -- different machines. Carries the decimal as written (int part, fraction
  -- digits, fraction length) so the message can quote it back.
  FloatNotRepresentable    : (int frac flen : ℕ) → TypeError

  -- PLAN 0.71/0.72, in flight: the lexer and parser accept a float literal and
  -- the IR carrier is ready for one, but the ELABORATOR has no rule yet — that
  -- needs the Surface node and the typing judgment (0.71 F3b). Rejecting with a
  -- distinct error is the honest intermediate state: the front half of the
  -- feature works and says so, rather than a literal silently meaning nothing.
  FloatLiteralUnsupported  : TypeError

  -- Mode-specific rejections
  LambdaInInferMode         : TypeError
  LambdaRequiresFunctionType : TypeError
  InlInInferMode            : TypeError
  InrInInferMode            : TypeError
  InitialInInferMode        : TypeError
  InlNeedsSumType           : TypeError
  InrNeedsSumType           : TypeError

  -- Type-shape mismatches on builtin-specific argument forms
  FstNeedsPair        : TypeError
  SndNeedsPair        : TypeError
  ArrNeedsFunction    : TypeError
  NegationNotInt      : TypeError
  CaseScrutineeNotSum : TypeError
  CaseBranchMismatch  : TypeError

  -- Application / annotation / check-mode mismatches
  ApplicationTypeMismatch : (expected actual : Type) → TypeError
  TypeMismatch            : (expected actual : Type) → TypeError

  -- Type-shape errors emitted by the `asInt` / `asFun` projection
  -- views when the inferred sub-result has the wrong shape. Used by
  -- RBinOp (via asInt on each operand) and generic RApp (via asFun
  -- on the function position).
  NotFunction : (actual : Type) → TypeError  -- "expected function, got X"

  -- Usage (QTT) violations
  UsageViolation : (name : String) (declared actual : Quantity) → TypeError

  -- Per-builtin type-shape mismatches in check mode
  BuiltinTypeMismatch : (builtin-name : String) → TypeError

  -- Binary operator sub-errors: wraps a sub-error from either side.
  BinOpLeftError  : TypeError → TypeError
  BinOpRightError : TypeError → TypeError

  -- Catch-all for strings we don't yet classify. Using this variant
  -- is an admission of incomplete coverage — flagged in reviews so
  -- each use gets promoted to a structured variant over time.
  UnclassifiedError : String → TypeError

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
renderError FloatLiteralUnsupported =
  "Float literals are not supported yet (the lexer and parser accept them; the"
    ++ " elaborator's rule lands with plan 0.71 F3b)"
renderError (FloatNotRepresentable int frac flen) =
  "Float literal is not exactly representable: " ++ showNatE int ++ "." ++ showNatE frac
    ++ " (" ++ showNatE flen ++ " fraction digits)"
    ++ " (Once accepts only literals exact at every target's float format — `Float`'s"
    ++ " width is a target property, so a rounded literal would denote a different"
    ++ " number on different machines. `0.5`, `1.5`, `2.25` are exact; `0.1` is not."
    ++ " Non-exact constants come from `pi`, `parseFloat` or arithmetic.)"
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
renderError InlNeedsSumType =
  "inl expects a sum type in check mode"
renderError InrNeedsSumType =
  "inr expects a sum type in check mode"
renderError FstNeedsPair =
  "fst requires a pair argument"
renderError SndNeedsPair =
  "snd requires a pair argument"
renderError ArrNeedsFunction =
  "arr requires a function argument (A → B)"
renderError NegationNotInt =
  "Negation requires Int operand"
renderError CaseScrutineeNotSum =
  "Case requires a sum-typed scrutinee"
renderError CaseBranchMismatch =
  "Case branches have different types"
renderError (ApplicationTypeMismatch expected actual) =
  "Application: argument type " ++ showType actual
    ++ " does not match function domain " ++ showType expected
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
renderError (BinOpLeftError sub) =
  "binop left: " ++ renderError sub
renderError (BinOpRightError sub) =
  "binop right: " ++ renderError sub
renderError (UnclassifiedError s) = s
