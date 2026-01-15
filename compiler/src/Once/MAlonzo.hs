-- | Bridge module for MAlonzo-generated Agda code
--
-- This module provides the interface for the verified MAlonzo optimizer
-- and type checker. Code is extracted from formally verified Agda proofs via MAlonzo.
module Once.MAlonzo
  ( -- * Optimization
    optimizeMAlonzo
  , canConvertIR
    -- * Conversion functions (for native backends)
  , toMAlonzoType
  , fromMAlonzoType
  , toMAlonzoIR
  , fromMAlonzoIR
  , getInputType
  , getOutputType
    -- * Type checking bridge (OCP-0004)
  , toMAlonzoRaw
  , toMAlonzoBinOp
  , toMAlonzoUnaryOp
  , fromInferResult
  , TypeCheckResult
  ) where

import Data.Text (Text)
import qualified Data.Text as T

import qualified Once.IR as H
import qualified Once.Syntax as S
import qualified Once.Type as H

import qualified MAlonzo.Code.Once.IR as M
import qualified MAlonzo.Code.Once.Type as M
import qualified MAlonzo.Code.Once.Optimize as MO
import qualified MAlonzo.Code.Once.TypeCheck.Raw as MR
import qualified MAlonzo.Code.Once.TypeCheck.Infer as MI
import qualified MAlonzo.Code.Once.TypeCheck.Error as ME
import qualified MAlonzo.Code.Agda.Builtin.Sigma as MSig

-- | Check if an IR can be converted to MAlonzo format
--
-- MAlonzo can only optimize pure categorical IR without:
-- - Var, LocalVar, FunRef (variable references)
-- - Prim (primitive operations)
-- - StringLit (string literals)
-- - Let (let bindings)
-- - TApp, TString (type applications, string types with encoding)
canConvertIR :: H.IR -> Bool
canConvertIR ir = case ir of
  H.Id t            -> canConvertType t
  H.Compose g f     -> canConvertIR g && canConvertIR f
  H.Fst a b         -> canConvertType a && canConvertType b
  H.Snd a b         -> canConvertType a && canConvertType b
  H.Pair f g        -> canConvertIR f && canConvertIR g
  H.Terminal t      -> canConvertType t
  H.Inl a b         -> canConvertType a && canConvertType b
  H.Inr a b         -> canConvertType a && canConvertType b
  H.Case f g        -> canConvertIR f && canConvertIR g
  H.Initial t       -> canConvertType t
  H.Curry _ f       -> canConvertIR f
  H.Apply a b       -> canConvertType a && canConvertType b
  H.Fold t          -> canConvertType t
  H.Unfold t        -> canConvertType t
  -- Cannot convert these
  H.Var _           -> False
  H.LocalVar _      -> False
  H.FunRef _        -> False
  H.Prim _ _ _      -> False
  H.StringLit _     -> False
  H.Let _ _ _       -> False

-- | Check if a type can be converted to MAlonzo format
canConvertType :: H.Type -> Bool
canConvertType t = case t of
  H.TUnit         -> True
  H.TVoid         -> True
  H.TInt          -> True
  H.TBuffer       -> True
  H.TProduct a b  -> canConvertType a && canConvertType b
  H.TSum a b      -> canConvertType a && canConvertType b
  H.TArrow a b    -> canConvertType a && canConvertType b
  H.TEff a b      -> canConvertType a && canConvertType b
  H.TFix f        -> canConvertType f
  H.TVar n        -> True
  H.TFloat        -> True   -- Float now in MAlonzo
  -- Cannot convert these
  H.TString _     -> False  -- MAlonzo has Str without encoding
  H.TApp _ _      -> False  -- Type applications not in MAlonzo

-- | Optimize using MAlonzo (verified) optimizer
--
-- Uses the formally verified optimizer extracted from Agda via MAlonzo.
-- Falls back to input if IR cannot be converted (contains Var, Prim, etc.)
optimizeMAlonzo :: H.IR -> H.IR
optimizeMAlonzo ir
  | canConvertIR ir =
      let mIR = toMAlonzoIR ir
          mOptimized = MO.d_optimize_1200 (getInputType ir) (getOutputType ir) mIR
      in fromMAlonzoIR mOptimized
  | otherwise = ir

-- | Convert Haskell Type to MAlonzo Type
toMAlonzoType :: H.Type -> M.T_Type_32
toMAlonzoType t = case t of
  H.TUnit        -> M.C_Unit_34
  H.TVoid        -> M.C_Void_36
  H.TInt         -> M.C_Int_48
  H.TFloat       -> M.C_Float_50
  H.TBuffer      -> M.C_Buffer_54
  H.TProduct a b -> M.C__'42'__38 (toMAlonzoType a) (toMAlonzoType b)
  H.TSum a b     -> M.C__'43'__40 (toMAlonzoType a) (toMAlonzoType b)
  H.TArrow a b   -> M.C__'8658''91'_'93'__42 (toMAlonzoType a) M.C_Many_10 (toMAlonzoType b)  -- Default to Many for unrestricted arrows
  H.TEff a b     -> M.C_Eff_44 (toMAlonzoType a) (toMAlonzoType b)
  H.TFix f       -> M.C_Fix_46 (toMAlonzoType f)
  H.TVar n       -> M.C_TVar_56 n  -- MAlonzo uses Text directly
  -- These should not occur (checked by canConvertType)
  H.TString _    -> error "MAlonzo: TString not supported"
  H.TApp _ _     -> error "MAlonzo: TApp not supported"

-- | Convert MAlonzo Type to Haskell Type
fromMAlonzoType :: M.T_Type_32 -> H.Type
fromMAlonzoType t = case t of
  M.C_Unit_34         -> H.TUnit
  M.C_Void_36         -> H.TVoid
  M.C_Int_48          -> H.TInt
  M.C_Float_50        -> H.TFloat
  M.C_Str_52          -> H.TString H.Utf8  -- Default to UTF-8
  M.C_Buffer_54       -> H.TBuffer
  M.C__'42'__38 a b   -> H.TProduct (fromMAlonzoType a) (fromMAlonzoType b)
  M.C__'43'__40 a b   -> H.TSum (fromMAlonzoType a) (fromMAlonzoType b)
  M.C__'8658''91'_'93'__42 a _q b -> H.TArrow (fromMAlonzoType a) (fromMAlonzoType b)  -- Ignore quantity
  M.C_Eff_44 a b      -> H.TEff (fromMAlonzoType a) (fromMAlonzoType b)
  M.C_Fix_46 f        -> H.TFix (fromMAlonzoType f)
  M.C_TVar_56 n       -> H.TVar n  -- MAlonzo uses Text directly

-- | Convert Haskell IR to MAlonzo IR
toMAlonzoIR :: H.IR -> M.T_IR_4
toMAlonzoIR ir = case ir of
  H.Id _            -> M.C_id_10
  H.Compose g f     -> M.C__'8728'__20 (getMiddleType g f) (toMAlonzoIR g) (toMAlonzoIR f)
  H.Fst _ _         -> M.C_fst_28
  H.Snd _ _         -> M.C_snd_36
  H.Pair f g        -> M.C_'10216'_'44'_'10217'_46 (toMAlonzoIR f) (toMAlonzoIR g)
  H.Terminal _      -> M.C_terminal_78
  H.Inl _ _         -> M.C_inl_54
  H.Inr _ _         -> M.C_inr_62
  H.Case f g        -> M.C_'91'_'44'_'93'_72 (toMAlonzoIR f) (toMAlonzoIR g)
  H.Initial _       -> M.C_initial_84
  H.Curry _ f       -> M.C_curry_94 (toMAlonzoIR f)
  H.Apply _ _       -> M.C_apply_102
  H.Fold _          -> M.C_fold_108
  H.Unfold _        -> M.C_unfold_114
  -- These should not occur (checked by canConvertIR)
  H.Var _           -> error "MAlonzo: Var not supported"
  H.LocalVar _      -> error "MAlonzo: LocalVar not supported"
  H.FunRef _        -> error "MAlonzo: FunRef not supported"
  H.Prim _ _ _      -> error "MAlonzo: Prim not supported"
  H.StringLit _     -> error "MAlonzo: StringLit not supported"
  H.Let _ _ _       -> error "MAlonzo: Let not supported"

-- | Convert MAlonzo IR to Haskell IR
--
-- Note: Type information is lost in MAlonzo IR, so we use placeholder types.
-- This is fine because the optimizer preserves types.
fromMAlonzoIR :: M.T_IR_4 -> H.IR
fromMAlonzoIR ir = case ir of
  M.C_id_10                       -> H.Id placeholder
  M.C__'8728'__20 _ g f           -> H.Compose (fromMAlonzoIR g) (fromMAlonzoIR f)
  M.C_fst_28                      -> H.Fst placeholder placeholder
  M.C_snd_36                      -> H.Snd placeholder placeholder
  M.C_'10216'_'44'_'10217'_46 f g -> H.Pair (fromMAlonzoIR f) (fromMAlonzoIR g)
  M.C_terminal_78                 -> H.Terminal placeholder
  M.C_inl_54                      -> H.Inl placeholder placeholder
  M.C_inr_62                      -> H.Inr placeholder placeholder
  M.C_'91'_'44'_'93'_72 f g       -> H.Case (fromMAlonzoIR f) (fromMAlonzoIR g)
  M.C_initial_84                  -> H.Initial placeholder
  M.C_curry_94 f                  -> H.Curry "_" (fromMAlonzoIR f)
  M.C_apply_102                   -> H.Apply placeholder placeholder
  M.C_fold_108                    -> H.Fold placeholder
  M.C_unfold_114                  -> H.Unfold placeholder
  M.C_arr_122                     -> error "MAlonzo: arr not supported in compiler IR"
  where
    placeholder = H.TUnit  -- Type info is erased, use placeholder

-- | Get input type of an IR expression
getInputType :: H.IR -> M.T_Type_32
getInputType ir = case ir of
  H.Id t            -> toMAlonzoType t
  H.Fst a b         -> M.C__'42'__38 (toMAlonzoType a) (toMAlonzoType b)
  H.Snd a b         -> M.C__'42'__38 (toMAlonzoType a) (toMAlonzoType b)
  H.Inl a _         -> toMAlonzoType a
  H.Inr _ b         -> toMAlonzoType b
  H.Terminal t      -> toMAlonzoType t
  H.Initial _       -> M.C_Void_36
  H.Apply a b       -> M.C__'42'__38 (M.C__'8658''91'_'93'__42 (toMAlonzoType a) M.C_Many_10 (toMAlonzoType b)) (toMAlonzoType a)
  H.Fold t          -> toMAlonzoType t  -- F (Fix F)
  H.Unfold t        -> M.C_Fix_46 (toMAlonzoType t)
  H.Compose _ f     -> getInputType f
  H.Pair f _        -> getInputType f
  H.Case f _        -> M.C__'43'__40 (getInputType f) M.C_Unit_34  -- Approximation
  H.Curry _ f       -> getInputType f  -- Approximation
  _                 -> M.C_Unit_34  -- Fallback

-- | Get output type of an IR expression
getOutputType :: H.IR -> M.T_Type_32
getOutputType ir = case ir of
  H.Id t            -> toMAlonzoType t
  H.Fst a _         -> toMAlonzoType a
  H.Snd _ b         -> toMAlonzoType b
  H.Inl a b         -> M.C__'43'__40 (toMAlonzoType a) (toMAlonzoType b)
  H.Inr a b         -> M.C__'43'__40 (toMAlonzoType a) (toMAlonzoType b)
  H.Terminal _      -> M.C_Unit_34
  H.Initial t       -> toMAlonzoType t
  H.Apply _ b       -> toMAlonzoType b
  H.Fold t          -> M.C_Fix_46 (toMAlonzoType t)
  H.Unfold t        -> toMAlonzoType t  -- F (Fix F)
  H.Compose g _     -> getOutputType g
  H.Pair f g        -> M.C__'42'__38 (getOutputType f) (getOutputType g)
  H.Case f _        -> getOutputType f
  H.Curry _ f       -> getOutputType f  -- Approximation
  _                 -> M.C_Unit_34  -- Fallback

-- | Get middle type for composition (output of f, input of g)
getMiddleType :: H.IR -> H.IR -> M.T_Type_32
getMiddleType _ f = getOutputType f

------------------------------------------------------------------------
-- Type checking bridge (OCP-0004)
------------------------------------------------------------------------

-- | Result of type checking: Either an error or (Type, Fresh counter)
type TypeCheckResult = Either String (H.Type, Integer)

-- | Convert Haskell Expr to MAlonzo RawExpr
--
-- Note: EQualified is not supported (module resolution is external)
toMAlonzoRaw :: S.Expr -> MR.T_RawExpr_34
toMAlonzoRaw expr = case expr of
  S.EVar name       -> MR.C_RVar_36 name
  S.EApp f arg      -> MR.C_RApp_38 (toMAlonzoRaw f) (toMAlonzoRaw arg)
  S.ELam x body     -> MR.C_RLam_40 x (toMAlonzoRaw body)
  S.ELet x e1 e2    -> MR.C_RLet_42 x (toMAlonzoRaw e1) (toMAlonzoRaw e2)
  S.EPair a b       -> MR.C_RPair_44 (toMAlonzoRaw a) (toMAlonzoRaw b)
  S.ECase scr x e1 y e2 ->
    MR.C_RCase_46 (toMAlonzoRaw scr) x (toMAlonzoRaw e1) y (toMAlonzoRaw e2)
  S.EUnit           -> MR.C_RUnit_48
  S.EInt n          -> MR.C_RInt_50 n
  S.EStringLit s    -> MR.C_RStringLit_52 s
  S.EAnnot e ty     -> MR.C_RAnnot_54 (toMAlonzoRaw e) (toMAlonzoTypeFromSType ty)
  S.EBinOp op a b   -> MR.C_RBinOp_56 (toMAlonzoBinOp op) (toMAlonzoRaw a) (toMAlonzoRaw b)
  S.EUnaryOp _ e    -> MR.C_RUnaryOp_58 (toMAlonzoRaw e)  -- Only OpNeg exists
  -- EQualified requires module resolution first
  S.EQualified _ _  -> error "MAlonzo: EQualified requires module resolution first"

-- | Convert Haskell BinOp to MAlonzo BinOp
toMAlonzoBinOp :: S.BinOp -> MR.T_BinOp_6
toMAlonzoBinOp op = case op of
  S.OpAdd -> MR.C_OpAdd_8
  S.OpSub -> MR.C_OpSub_10
  S.OpMul -> MR.C_OpMul_12
  S.OpDiv -> MR.C_OpDiv_14
  S.OpMod -> MR.C_OpMod_16
  S.OpLt  -> MR.C_OpLt_18
  S.OpLe  -> MR.C_OpLe_20
  S.OpGt  -> MR.C_OpGt_22
  S.OpGe  -> MR.C_OpGe_24
  S.OpEq  -> MR.C_OpEq_26
  S.OpNe  -> MR.C_OpNe_28

-- | Convert Haskell UnaryOp to MAlonzo UnaryOp
toMAlonzoUnaryOp :: S.UnaryOp -> MR.T_UnaryOp_30
toMAlonzoUnaryOp S.OpNeg = MR.C_OpNeg_32

-- | Convert surface type to MAlonzo Type
toMAlonzoTypeFromSType :: S.SType -> M.T_Type_32
toMAlonzoTypeFromSType sty = case sty of
  S.STVar name     -> M.C_TVar_56 name
  S.STUnit         -> M.C_Unit_34
  S.STVoid         -> M.C_Void_36
  S.STInt          -> M.C_Int_48
  S.STFloat        -> M.C_Float_50
  S.STBuffer       -> M.C_Buffer_54
  S.STString _     -> M.C_Str_52  -- MAlonzo doesn't track encoding
  S.STProduct a b  -> M.C__'42'__38 (toMAlonzoTypeFromSType a) (toMAlonzoTypeFromSType b)
  S.STSum a b      -> M.C__'43'__40 (toMAlonzoTypeFromSType a) (toMAlonzoTypeFromSType b)
  S.STArrow a b    -> M.C__'8658''91'_'93'__42 (toMAlonzoTypeFromSType a) M.C_Many_10 (toMAlonzoTypeFromSType b)  -- Default to Many
  S.STEff a b      -> M.C_Eff_44 (toMAlonzoTypeFromSType a) (toMAlonzoTypeFromSType b)
  S.STFix f        -> M.C_Fix_46 (toMAlonzoTypeFromSType f)
  S.STQuant _ t    -> toMAlonzoTypeFromSType t  -- Ignore quantity annotation
  S.STApp _ _      -> error "MAlonzo: STApp not supported"

-- | Convert MAlonzo InferResult to Haskell result
--
-- Returns: Left errorMsg | Right (type, fresh counter)
fromInferResult :: MI.T_InferResult_142 -> TypeCheckResult
fromInferResult result = case result of
  MI.C_success_144 ty _subst fresh ->
    Right (fromMAlonzoType ty, fresh)
  MI.C_failure_146 err ->
    Left (fromMAlonzoError err)

-- | Convert MAlonzo TypeError to error string
fromMAlonzoError :: ME.T_TypeError_6 -> String
fromMAlonzoError err = case err of
  ME.C_UnboundVariable_8 name ->
    "Unbound variable: " ++ T.unpack name
  ME.C_TypeMismatch_10 expected got ->
    "Type mismatch: expected " ++ showType (fromMAlonzoType expected)
    ++ ", got " ++ showType (fromMAlonzoType got)
  ME.C_NotAFunction_12 ty ->
    "Not a function: " ++ showType (fromMAlonzoType ty)
  ME.C_NotAProduct_14 ty ->
    "Not a product type: " ++ showType (fromMAlonzoType ty)
  ME.C_NotASum_16 ty ->
    "Not a sum type: " ++ showType (fromMAlonzoType ty)
  ME.C_OccursCheck_18 var ty ->
    "Infinite type: " ++ T.unpack var ++ " occurs in " ++ showType (fromMAlonzoType ty)
  ME.C_UnificationError_20 t1 t2 ->
    "Cannot unify " ++ showType (fromMAlonzoType t1)
    ++ " with " ++ showType (fromMAlonzoType t2)
  ME.C_ArityMismatch_22 name expected got ->
    "Arity mismatch for " ++ T.unpack name
    ++ ": expected " ++ show expected ++ ", got " ++ show got
  ME.C_SignatureMismatch_24 sig inferred ->
    "Signature mismatch: declared " ++ showType (fromMAlonzoType sig)
    ++ ", inferred " ++ showType (fromMAlonzoType inferred)
  ME.C_LinearUsedMultiple_26 name count ->
    "Linear variable " ++ T.unpack name ++ " used " ++ show count ++ " times"
  ME.C_LinearUnused_28 name ->
    "Linear variable " ++ T.unpack name ++ " not used"
  ME.C_ErasedUsedAtRuntime_30 name ->
    "Erased variable " ++ T.unpack name ++ " used at runtime"
  ME.C_QuantityMismatch_32 name _ _ ->
    "Quantity mismatch for " ++ T.unpack name
  ME.C_ArithNonInteger_34 ty ->
    "Arithmetic requires integer operands, got: " ++ showType (fromMAlonzoType ty)
  ME.C_CompareNonInteger_36 ty ->
    "Comparison requires integer operands, got: " ++ showType (fromMAlonzoType ty)

-- | Show a type for error messages
showType :: H.Type -> String
showType ty = case ty of
  H.TUnit        -> "Unit"
  H.TVoid        -> "Void"
  H.TInt         -> "Int"
  H.TFloat       -> "Float"
  H.TBuffer      -> "Buffer"
  H.TString _    -> "String"
  H.TVar n       -> T.unpack n
  H.TProduct a b -> "(" ++ showType a ++ " * " ++ showType b ++ ")"
  H.TSum a b     -> "(" ++ showType a ++ " + " ++ showType b ++ ")"
  H.TArrow a b   -> "(" ++ showType a ++ " -> " ++ showType b ++ ")"
  H.TEff a b     -> "Eff " ++ showType a ++ " " ++ showType b
  H.TFix f       -> "Fix (" ++ showType f ++ ")"
  H.TApp n _     -> T.unpack n ++ " ..."
