-- | Verified elaboration using MAlonzo-extracted code
--
-- Part of OCP-0004: MAlonzo Compiler Replacement
--
-- This module wraps the verified elaboration pipeline extracted from Agda via MAlonzo.
-- The elaboration is proven correct: Surface.Syntax.Expr → IR preserves semantics.
--
-- Pipeline:
--   1. toMAlonzoRaw: Haskell Expr → MAlonzo RawExpr
--   2. TypeCheck/Infer: RawExpr → Type (infer the type)
--   3. TypeCheck/Resolve: RawExpr + Type → Surface.Syntax.Expr (scope resolution)
--   4. Surface.Elaborate: Ctx → Type → Surface.Syntax.Expr → IR (category-theoretic)
module Once.Elaborate.Verified
  ( -- * Verified elaboration
    elaborateVerified
  , elaborateToIR
    -- * Error handling
  , ElaborateError
  ) where

import qualified Once.Syntax as S
import qualified Once.Type as H
import qualified Once.IR as H

import qualified MAlonzo.Code.Once.IR as MI
import qualified MAlonzo.Code.Once.Type as MT
import qualified MAlonzo.Code.Once.TypeCheck.Infer as VI
import qualified MAlonzo.Code.Once.TypeCheck.Context as VC
import qualified MAlonzo.Code.Once.TypeCheck.Resolve as VR
import qualified MAlonzo.Code.Once.Surface.Syntax as VS
import qualified MAlonzo.Code.Once.Surface.Elaborate as VE
import qualified MAlonzo.Code.Agda.Builtin.Maybe as AM
import Once.MAlonzo (toMAlonzoRaw, toMAlonzoType, fromInferResult, fromMAlonzoIR)

-- | Elaboration error message
type ElaborateError = String

-- | Elaborate an expression using the verified MAlonzo implementation
--
-- This is the full verified pipeline:
--   Haskell Expr → MAlonzo RawExpr → Type check → Resolve → Elaborate → Haskell IR
--
-- Returns either an error message or the elaborated categorical IR.
elaborateVerified :: S.Expr -> Either ElaborateError H.IR
elaborateVerified expr = do
  -- Step 1: Convert to MAlonzo RawExpr
  let rawExpr = toMAlonzoRaw expr

  -- Step 2: Infer the type using verified type checker
  let inferResult = VI.d_infer_148 VC.d_'8709'_32 rawExpr 0
  (hType, _fresh) <- fromInferResult inferResult
  let mType = toMAlonzoType hType

  -- Step 3: Resolve variable scopes to get intrinsically-typed expression
  case VR.d_resolveClosed_508 rawExpr mType of
    AM.C_nothing_18 -> Left "Verified elaboration: scope resolution failed"
    AM.C_just_16 surfaceExpr -> do
      -- Step 4: Elaborate to categorical IR
      let mIR = VE.du_elaborate_70 VS.C_'8709'_8 mType surfaceExpr
      -- Step 5: Convert back to Haskell IR
      Right (fromMAlonzoIR mIR)

-- | Elaborate an expression directly to MAlonzo IR (for internal use)
--
-- This skips the Haskell IR conversion, useful when the result will
-- be passed directly to other MAlonzo modules.
elaborateToIR :: S.Expr -> Either ElaborateError MI.T_IR_4
elaborateToIR expr = do
  let rawExpr = toMAlonzoRaw expr
  let inferResult = VI.d_infer_148 VC.d_'8709'_32 rawExpr 0
  (hType, _fresh) <- fromInferResult inferResult
  let mType = toMAlonzoType hType

  case VR.d_resolveClosed_508 rawExpr mType of
    AM.C_nothing_18 -> Left "Verified elaboration: scope resolution failed"
    AM.C_just_16 surfaceExpr ->
      Right (VE.du_elaborate_70 VS.C_'8709'_8 mType surfaceExpr)
