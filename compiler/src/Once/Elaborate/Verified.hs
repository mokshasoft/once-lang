-- | Verified elaboration using MAlonzo-extracted code
--
-- Part of OCP-0004: MAlonzo Compiler Replacement
--
-- This module wraps the verified elaboration pipeline extracted from Agda via MAlonzo.
-- The elaboration is proven correct: Surface.Syntax.Expr → IR preserves semantics.
--
-- Pipeline (new combined approach):
--   1. toMAlonzoRaw: Haskell Expr → MAlonzo RawExpr
--   2. TypeCheck/Elaborate.inferElab: RawExpr → InferElabResult (combined type+resolve)
--   3. Surface.Elaborate: Surface.Syntax.Expr → IR (category-theoretic)
--
-- The new TypeCheck.Elaborate module avoids the postulates in TypeCheck.Resolve
-- by combining type inference and elaboration in a single pass.
module Once.Elaborate.Verified
  ( -- * Verified elaboration
    elaborateVerified
  , elaborateToIR
    -- * Error handling
  , ElaborateError
  ) where

import qualified Once.Syntax as S
import qualified Once.IR as H

import qualified MAlonzo.Code.Once.IR as MI
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate as VTE
import qualified MAlonzo.Code.Agda.Builtin.Maybe as AM
import qualified MAlonzo.Code.Agda.Builtin.Sigma as Sigma
import Once.MAlonzo (toMAlonzoRaw, fromMAlonzoIR)
import Unsafe.Coerce (unsafeCoerce)

-- | Elaboration error message
type ElaborateError = String

-- | Elaborate an expression using the verified MAlonzo implementation
--
-- This uses the new combined inferElab function that avoids postulates:
--   Haskell Expr → MAlonzo RawExpr → inferElab → Surface.Expr → Elaborate → IR
--
-- Returns either an error message or the elaborated categorical IR.
elaborateVerified :: S.Expr -> Either ElaborateError H.IR
elaborateVerified expr = do
  -- Step 1: Convert to MAlonzo RawExpr
  let rawExpr = toMAlonzoRaw expr

  -- Step 2: Use compileExpr which does inferElab + elaborate in one step
  case VTE.d_compileExpr_1172 rawExpr of
    AM.C_nothing_18 -> Left "Verified elaboration: inference/elaboration failed"
    AM.C_just_16 result ->
      -- Result is ∃[ A ] IR ∞ Unit A, which is a dependent pair (Sigma)
      -- MAlonzo erases dependent types, so we use unsafeCoerce
      case result of
        Sigma.C__'44'__32 _ty irExpr ->
          -- Step 3: Convert back to Haskell IR
          Right (fromMAlonzoIR (unsafeCoerce irExpr))

-- | Elaborate an expression directly to MAlonzo IR (for internal use)
--
-- This skips the Haskell IR conversion, useful when the result will
-- be passed directly to other MAlonzo modules.
elaborateToIR :: S.Expr -> Either ElaborateError MI.T_IR_4
elaborateToIR expr = do
  let rawExpr = toMAlonzoRaw expr
  case VTE.d_compileExpr_1172 rawExpr of
    AM.C_nothing_18 -> Left "Verified elaboration: inference/elaboration failed"
    AM.C_just_16 result ->
      case result of
        Sigma.C__'44'__32 _ty irExpr -> Right (unsafeCoerce irExpr)
