-- | Verified type checker using MAlonzo-extracted code
--
-- Part of OCP-0004: MAlonzo Compiler Replacement
--
-- This module wraps the verified type checker extracted from Agda via MAlonzo.
-- The type checker is proven sound: if it succeeds, the expression is well-typed.
module Once.TypeCheck.Verified
  ( -- * Type checking
    typeCheckVerified
  , inferTypeVerified
    -- * Error handling
  , TypeCheckError
  ) where

import Data.Text (Text)
import qualified Data.Text as T

import qualified Once.Syntax as S
import qualified Once.Type as H

import qualified MAlonzo.Code.Once.TypeCheck as V
import qualified MAlonzo.Code.Once.TypeCheck.Infer as VI
import qualified MAlonzo.Code.Once.TypeCheck.Context as VC
import Once.MAlonzo (toMAlonzoRaw, fromInferResult, TypeCheckResult)

-- | Type checking error message
type TypeCheckError = String

-- | Type check an expression using the verified MAlonzo implementation
--
-- This is the verified version of type inference. If it succeeds,
-- we have a formal guarantee that the expression is well-typed.
--
-- Returns either an error message or the inferred type.
typeCheckVerified :: S.Expr -> Either TypeCheckError H.Type
typeCheckVerified expr = do
  let rawExpr = toMAlonzoRaw expr
  -- Run the verified type checker with empty context and fresh counter 0
  let result = VI.d_infer_148 VC.d_'8709'_32 rawExpr 0
  case fromInferResult result of
    Left err -> Left err
    Right (ty, _fresh) -> Right ty

-- | Infer the type of an expression using verified type checker
--
-- Same as typeCheckVerified but returns the fresh counter as well
-- (useful for continuing type inference in nested contexts).
inferTypeVerified :: S.Expr -> Either TypeCheckError (H.Type, Integer)
inferTypeVerified expr = do
  let rawExpr = toMAlonzoRaw expr
  let result = VI.d_infer_148 VC.d_'8709'_32 rawExpr 0
  fromInferResult result
