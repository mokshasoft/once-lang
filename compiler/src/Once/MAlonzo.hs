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
  ) where

import Data.Text (Text)

import qualified Once.IR as H
import qualified Once.Type as H

import qualified MAlonzo.Code.Once.IR as M
import qualified MAlonzo.Code.Once.Type as M
import qualified MAlonzo.Code.Once.Optimize as MO

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
  H.Arith _ _       -> False

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
          mOptimized = MO.d_optimize_1386 (getInputType ir) (getOutputType ir) mIR
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
toMAlonzoIR :: H.IR -> M.T_IR_10
toMAlonzoIR ir = case ir of
  H.Id _            -> M.C_id_14
  H.Compose g f     -> M.C__'8728'__22 (getMiddleType g f) (toMAlonzoIR g) (toMAlonzoIR f)
  H.Fst _ _         -> M.C_fst_28
  H.Snd _ _         -> M.C_snd_34
  H.Pair f g        -> M.C_'10216'_'44'_'10217'_42 (toMAlonzoIR f) (toMAlonzoIR g) M.C_Stack_6
  H.Terminal _      -> M.C_terminal_66
  H.Inl _ _         -> M.C_inl_48 M.C_Stack_6
  H.Inr _ _         -> M.C_inr_54 M.C_Stack_6
  H.Case f g        -> M.C_'91'_'44'_'93'_62 (toMAlonzoIR f) (toMAlonzoIR g)
  H.Initial _       -> M.C_initial_70
  H.Curry _ f       -> M.C_curry_78 (toMAlonzoIR f) M.C_Stack_6
  H.Apply _ _       -> M.C_apply_84
  H.Fold _          -> M.C_fold_88
  H.Unfold _        -> M.C_unfold_92
  -- These should not occur (checked by canConvertIR)
  H.Var _           -> error "MAlonzo: Var not supported"
  H.LocalVar _      -> error "MAlonzo: LocalVar not supported"
  H.FunRef _        -> error "MAlonzo: FunRef not supported"
  H.Prim _ _ _      -> error "MAlonzo: Prim not supported"
  H.StringLit _     -> error "MAlonzo: StringLit not supported"
  H.Let _ _ _       -> error "MAlonzo: Let not supported"
  H.Arith _ _       -> error "MAlonzo: Arith not supported"

-- | Convert MAlonzo IR to Haskell IR
--
-- Note: Type information is lost in MAlonzo IR, so we use placeholder types.
-- This is fine because the optimizer preserves types.
fromMAlonzoIR :: M.T_IR_10 -> H.IR
fromMAlonzoIR ir = case ir of
  M.C_id_14                       -> H.Id placeholder
  M.C__'8728'__22 _ g f           -> H.Compose (fromMAlonzoIR g) (fromMAlonzoIR f)
  M.C_fst_28                      -> H.Fst placeholder placeholder
  M.C_snd_34                      -> H.Snd placeholder placeholder
  M.C_'10216'_'44'_'10217'_42 f g _alloc -> H.Pair (fromMAlonzoIR f) (fromMAlonzoIR g)
  M.C_terminal_66                 -> H.Terminal placeholder
  M.C_inl_48 _alloc               -> H.Inl placeholder placeholder
  M.C_inr_54 _alloc               -> H.Inr placeholder placeholder
  M.C_'91'_'44'_'93'_62 f g       -> H.Case (fromMAlonzoIR f) (fromMAlonzoIR g)
  M.C_initial_70                  -> H.Initial placeholder
  M.C_curry_78 f _alloc           -> H.Curry "_" (fromMAlonzoIR f)
  M.C_apply_84                   -> H.Apply placeholder placeholder
  M.C_fold_88                    -> H.Fold placeholder
  M.C_unfold_92                  -> H.Unfold placeholder
  M.C_arr_98                     -> error "MAlonzo: arr not supported in compiler IR"
  M.C_Prim_104 _                 -> error "MAlonzo: Prim not supported in compiler IR"
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

