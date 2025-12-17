-- | Bridge module for MAlonzo-generated Agda code
--
-- This module provides the interface for the verified MAlonzo optimizer.
-- The optimizer is extracted from formally verified Agda proofs via MAlonzo.
module Once.MAlonzo
  ( -- * Optimization
    optimizeMAlonzo
  , canConvertIR
  ) where

import qualified Once.IR as H
import qualified Once.Type as H

import qualified MAlonzo.Code.Once.IR as M
import qualified MAlonzo.Code.Once.Type as M
import qualified MAlonzo.Code.Once.Optimize as M

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
  -- Cannot convert these
  H.TFloat        -> False  -- Float not in MAlonzo
  H.TString _     -> False  -- MAlonzo has Str without encoding
  H.TApp _ _      -> False  -- Type applications not in MAlonzo

-- | Optimize using MAlonzo (verified) optimizer
--
-- Converts IR to MAlonzo format, runs the verified optimizer,
-- then converts back. Returns input unchanged if conversion fails.
optimizeMAlonzo :: H.IR -> H.IR
optimizeMAlonzo ir
  | canConvertIR ir =
      let mIR = toMAlonzoIR ir
          mOptimized = M.d_optimize_1126 (getInputType ir) (getOutputType ir) mIR
      in fromMAlonzoIR mOptimized
  | otherwise = ir

-- | Convert Haskell Type to MAlonzo Type
toMAlonzoType :: H.Type -> M.T_Type_4
toMAlonzoType t = case t of
  H.TUnit        -> M.C_Unit_6
  H.TVoid        -> M.C_Void_8
  H.TInt         -> M.C_Int_20
  H.TBuffer      -> M.C_Buffer_24
  H.TProduct a b -> M.C__'42'__10 (toMAlonzoType a) (toMAlonzoType b)
  H.TSum a b     -> M.C__'43'__12 (toMAlonzoType a) (toMAlonzoType b)
  H.TArrow a b   -> M.C__'8658'__14 (toMAlonzoType a) (toMAlonzoType b)
  H.TEff a b     -> M.C_Eff_16 (toMAlonzoType a) (toMAlonzoType b)
  H.TFix f       -> M.C_Fix_18 (toMAlonzoType f)
  H.TVar n       -> M.C_TVar_26 n  -- MAlonzo uses Text directly
  -- These should not occur (checked by canConvertType)
  H.TFloat       -> error "MAlonzo: TFloat not supported"
  H.TString _    -> error "MAlonzo: TString not supported"
  H.TApp _ _     -> error "MAlonzo: TApp not supported"

-- | Convert MAlonzo Type to Haskell Type
fromMAlonzoType :: M.T_Type_4 -> H.Type
fromMAlonzoType t = case t of
  M.C_Unit_6         -> H.TUnit
  M.C_Void_8         -> H.TVoid
  M.C_Int_20         -> H.TInt
  M.C_Str_22         -> H.TString H.Utf8  -- Default to UTF-8
  M.C_Buffer_24      -> H.TBuffer
  M.C__'42'__10 a b  -> H.TProduct (fromMAlonzoType a) (fromMAlonzoType b)
  M.C__'43'__12 a b  -> H.TSum (fromMAlonzoType a) (fromMAlonzoType b)
  M.C__'8658'__14 a b -> H.TArrow (fromMAlonzoType a) (fromMAlonzoType b)
  M.C_Eff_16 a b     -> H.TEff (fromMAlonzoType a) (fromMAlonzoType b)
  M.C_Fix_18 f       -> H.TFix (fromMAlonzoType f)
  M.C_TVar_26 n      -> H.TVar n  -- MAlonzo uses Text directly

-- | Convert Haskell IR to MAlonzo IR
toMAlonzoIR :: H.IR -> M.T_IR_4
toMAlonzoIR ir = case ir of
  H.Id _            -> M.C_id_8
  H.Compose g f     -> M.C__'8728'__16 (getMiddleType g f) (toMAlonzoIR g) (toMAlonzoIR f)
  H.Fst _ _         -> M.C_fst_22
  H.Snd _ _         -> M.C_snd_28
  H.Pair f g        -> M.C_'10216'_'44'_'10217'_36 (toMAlonzoIR f) (toMAlonzoIR g)
  H.Terminal _      -> M.C_terminal_60
  H.Inl _ _         -> M.C_inl_42
  H.Inr _ _         -> M.C_inr_48
  H.Case f g        -> M.C_'91'_'44'_'93'_56 (toMAlonzoIR f) (toMAlonzoIR g)
  H.Initial _       -> M.C_initial_64
  H.Curry _ f       -> M.C_curry_72 (toMAlonzoIR f)
  H.Apply _ _       -> M.C_apply_78
  H.Fold _          -> M.C_fold_82
  H.Unfold _        -> M.C_unfold_86
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
  M.C_id_8                      -> H.Id placeholder
  M.C__'8728'__16 _ g f         -> H.Compose (fromMAlonzoIR g) (fromMAlonzoIR f)
  M.C_fst_22                    -> H.Fst placeholder placeholder
  M.C_snd_28                    -> H.Snd placeholder placeholder
  M.C_'10216'_'44'_'10217'_36 f g -> H.Pair (fromMAlonzoIR f) (fromMAlonzoIR g)
  M.C_terminal_60               -> H.Terminal placeholder
  M.C_inl_42                    -> H.Inl placeholder placeholder
  M.C_inr_48                    -> H.Inr placeholder placeholder
  M.C_'91'_'44'_'93'_56 f g     -> H.Case (fromMAlonzoIR f) (fromMAlonzoIR g)
  M.C_initial_64                -> H.Initial placeholder
  M.C_curry_72 f                -> H.Curry "_" (fromMAlonzoIR f)
  M.C_apply_78                  -> H.Apply placeholder placeholder
  M.C_fold_82                   -> H.Fold placeholder
  M.C_unfold_86                 -> H.Unfold placeholder
  M.C_arr_92                    -> error "MAlonzo: arr not supported in compiler IR"
  where
    placeholder = H.TUnit  -- Type info is erased, use placeholder

-- | Get input type of an IR expression
getInputType :: H.IR -> M.T_Type_4
getInputType ir = case ir of
  H.Id t            -> toMAlonzoType t
  H.Fst a b         -> M.C__'42'__10 (toMAlonzoType a) (toMAlonzoType b)
  H.Snd a b         -> M.C__'42'__10 (toMAlonzoType a) (toMAlonzoType b)
  H.Inl a _         -> toMAlonzoType a
  H.Inr _ b         -> toMAlonzoType b
  H.Terminal t      -> toMAlonzoType t
  H.Initial _       -> M.C_Void_8
  H.Apply a b       -> M.C__'42'__10 (M.C__'8658'__14 (toMAlonzoType a) (toMAlonzoType b)) (toMAlonzoType a)
  H.Fold t          -> toMAlonzoType t  -- F (Fix F)
  H.Unfold t        -> M.C_Fix_18 (toMAlonzoType t)
  H.Compose _ f     -> getInputType f
  H.Pair f _        -> getInputType f
  H.Case f _        -> M.C__'43'__12 (getInputType f) M.C_Unit_6  -- Approximation
  H.Curry _ f       -> getInputType f  -- Approximation
  _                 -> M.C_Unit_6  -- Fallback

-- | Get output type of an IR expression
getOutputType :: H.IR -> M.T_Type_4
getOutputType ir = case ir of
  H.Id t            -> toMAlonzoType t
  H.Fst a _         -> toMAlonzoType a
  H.Snd _ b         -> toMAlonzoType b
  H.Inl a b         -> M.C__'43'__12 (toMAlonzoType a) (toMAlonzoType b)
  H.Inr a b         -> M.C__'43'__12 (toMAlonzoType a) (toMAlonzoType b)
  H.Terminal _      -> M.C_Unit_6
  H.Initial t       -> toMAlonzoType t
  H.Apply _ b       -> toMAlonzoType b
  H.Fold t          -> M.C_Fix_18 (toMAlonzoType t)
  H.Unfold t        -> toMAlonzoType t  -- F (Fix F)
  H.Compose g _     -> getOutputType g
  H.Pair f g        -> M.C__'42'__10 (getOutputType f) (getOutputType g)
  H.Case f _        -> getOutputType f
  H.Curry _ f       -> getOutputType f  -- Approximation
  _                 -> M.C_Unit_6  -- Fallback

-- | Get middle type for composition (output of f, input of g)
getMiddleType :: H.IR -> H.IR -> M.T_Type_4
getMiddleType _ f = getOutputType f
