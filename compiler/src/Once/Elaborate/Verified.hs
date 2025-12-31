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
-- The new TypeCheck.Elaborate module combines type inference and elaboration in a single pass
-- and enforces a depth limit of 7 nested binders (proven correctness bound).
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
import qualified MAlonzo.Code.Once.Surface.Elaborate as VSE
import qualified MAlonzo.Code.Once.Surface.Syntax as VSS
import Once.MAlonzo (toMAlonzoRaw, fromMAlonzoIR)
import Unsafe.Coerce (unsafeCoerce)

-- | Elaboration error message
type ElaborateError = String

-- | Elaborate an expression using the verified MAlonzo implementation
--
-- This uses the inferElab function with depth checking (depth ≤ 7):
--   Haskell Expr → MAlonzo RawExpr → inferElab → Surface.Expr → Elaborate → IR
--
-- Returns either an error message or the elaborated categorical IR.
-- Programs with >7 levels of nesting are rejected by the Agda type checker.
elaborateVerified :: S.Expr -> Either ElaborateError H.IR
elaborateVerified expr = do
  -- Step 1: Convert to MAlonzo RawExpr
  let rawExpr = toMAlonzoRaw expr

  -- Step 2: Run type inference/elaboration to get Surface.Expr
  -- Note: inferElab now rejects depth > 7 with a clear error message
  case VTE.d_inferElab_2352 VTE.d_emptyCtx_1118 rawExpr of
    VTE.C_failure_1072 errMsg ->
      Left $ "Type checking failed: " ++ show errMsg
    VTE.C_success_1070 ty surfaceExpr _fresh _depth _usage ->
      let irExpr = VSE.du_elaborate_76
                     (VSS.C_'8709'_8)  -- Empty context
                     ty
                     surfaceExpr
      in Right (fromMAlonzoIR (unsafeCoerce irExpr))

-- | Elaborate an expression directly to MAlonzo IR (for internal use)
--
-- This skips the Haskell IR conversion, useful when the result will
-- be passed directly to other MAlonzo modules.
-- Programs with >7 levels of nesting are rejected by the Agda type checker.
elaborateToIR :: S.Expr -> Either ElaborateError MI.T_IR_4
elaborateToIR expr = do
  let rawExpr = toMAlonzoRaw expr
  case VTE.d_inferElab_2352 VTE.d_emptyCtx_1118 rawExpr of
    VTE.C_failure_1072 errMsg ->
      Left $ "Type checking failed: " ++ show errMsg
    VTE.C_success_1070 ty surfaceExpr _fresh _depth _usage ->
      let irExpr = VSE.du_elaborate_76
                     (VSS.C_'8709'_8)
                     ty
                     surfaceExpr
      in Right (unsafeCoerce irExpr)
