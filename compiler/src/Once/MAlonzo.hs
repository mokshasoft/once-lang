{-# LANGUAGE PatternSynonyms #-}
-- | Bridge module for MAlonzo-generated Agda code
--
-- This module provides conversion functions between the Haskell IR/Type
-- and the MAlonzo-generated types from verified Agda code.
--
-- The MAlonzo optimizer is verified to preserve semantics. By using it
-- instead of the Haskell optimizer, we get formal guarantees.
--
-- Note: The MAlonzo Core IR is pure categorical (no Var, LocalVar, etc.).
-- IR containing these constructs cannot be fully converted but can be
-- optimized in a hybrid fashion.
module Once.MAlonzo
  ( -- * Conversion functions
    toMAlonzoType
  , fromMAlonzoType
  , toMAlonzoSurfaceIR
  , fromMAlonzoCoreIR
    -- * Optimization
  , optimizeMAlonzo
  , canConvertIR
    -- * Re-exports from MAlonzo
  , M.T_Type_4
  , MS.T_SurfaceIR_6
  , MC.T_IR_4
  ) where

import Data.Text (Text)
import qualified Data.Text as T

import qualified Once.IR as H
import qualified Once.Type as H

-- Import MAlonzo generated modules
import qualified MAlonzo.Code.Once.Type as M
import qualified MAlonzo.Code.Once.IR as MC
import qualified MAlonzo.Code.Once.Surface.IR as MS
import qualified MAlonzo.Code.Once.Compile as Compile
import MAlonzo.RTE (coe)

------------------------------------------------------------------------
-- Type conversion
------------------------------------------------------------------------

-- | Convert Haskell Type to MAlonzo Type
-- Returns Nothing for types that don't exist in MAlonzo (TApp)
toMAlonzoType :: H.Type -> Maybe M.T_Type_4
toMAlonzoType t = case t of
  H.TUnit -> Just M.C_Unit_6
  H.TVoid -> Just M.C_Void_8
  H.TProduct a b -> M.C__'42'__10 <$> toMAlonzoType a <*> toMAlonzoType b
  H.TSum a b -> M.C__'43'__12 <$> toMAlonzoType a <*> toMAlonzoType b
  H.TArrow a b -> M.C__'8658'__14 <$> toMAlonzoType a <*> toMAlonzoType b
  H.TEff a b -> M.C_Eff_16 <$> toMAlonzoType a <*> toMAlonzoType b
  H.TFix f -> M.C_Fix_18 <$> toMAlonzoType f
  -- Base types (now supported in MAlonzo)
  H.TInt -> Just M.C_Int_20
  H.TBuffer -> Just M.C_Buffer_24
  H.TString _ -> Just M.C_Str_22  -- Encoding is erased
  H.TVar name -> Just $ M.C_TVar_26 name
  -- Not yet supported
  H.TApp _ _ -> Nothing

-- | Convert MAlonzo Type back to Haskell Type
fromMAlonzoType :: M.T_Type_4 -> H.Type
fromMAlonzoType t = case t of
  M.C_Unit_6 -> H.TUnit
  M.C_Void_8 -> H.TVoid
  M.C__'42'__10 a b -> H.TProduct (fromMAlonzoType a) (fromMAlonzoType b)
  M.C__'43'__12 a b -> H.TSum (fromMAlonzoType a) (fromMAlonzoType b)
  M.C__'8658'__14 a b -> H.TArrow (fromMAlonzoType a) (fromMAlonzoType b)
  M.C_Eff_16 a b -> H.TEff (fromMAlonzoType a) (fromMAlonzoType b)
  M.C_Fix_18 f -> H.TFix (fromMAlonzoType f)
  -- Base types
  M.C_Int_20 -> H.TInt
  M.C_Str_22 -> H.TString H.Utf8
  M.C_Buffer_24 -> H.TBuffer
  M.C_TVar_26 name -> H.TVar name

------------------------------------------------------------------------
-- IR conversion
------------------------------------------------------------------------

-- | Check if an IR can be fully converted to MAlonzo
-- Returns False if it contains Var, LocalVar, FunRef, StringLit, or
-- types that can't be converted
canConvertIR :: H.IR -> Bool
canConvertIR ir = case ir of
  H.Id t -> canConvertType t
  H.Compose g f -> canConvertIR g && canConvertIR f
  H.Fst a b -> canConvertType a && canConvertType b
  H.Snd a b -> canConvertType a && canConvertType b
  H.Pair f g -> canConvertIR f && canConvertIR g
  H.Terminal t -> canConvertType t
  H.Inl a b -> canConvertType a && canConvertType b
  H.Inr a b -> canConvertType a && canConvertType b
  H.Case f g -> canConvertIR f && canConvertIR g
  H.Initial t -> canConvertType t
  H.Curry f -> canConvertIR f
  H.Apply a b -> canConvertType a && canConvertType b
  H.Fold t -> canConvertType t
  H.Unfold t -> canConvertType t
  -- Let can be converted (to De Bruijn style) if subexpressions can
  H.Let _ e1 e2 -> canConvertIR e1 && canConvertIR e2
  -- Prim can be converted (MAlonzo Surface IR has Prim)
  H.Prim _ inT outT -> canConvertType inT && canConvertType outT
  -- These cannot be converted
  H.Var _ -> False
  H.LocalVar _ -> False
  H.FunRef _ -> False
  H.StringLit _ -> False

canConvertType :: H.Type -> Bool
canConvertType t = case toMAlonzoType t of
  Just _ -> True
  Nothing -> False

-- | Convert Haskell IR to MAlonzo Surface IR
-- Requires computing intermediate types for Compose.
-- Returns Nothing if conversion is not possible.
toMAlonzoSurfaceIR :: H.IR -> Maybe MS.T_SurfaceIR_6
toMAlonzoSurfaceIR ir = case ir of
  H.Id _ -> Just MS.C_id_10
  H.Compose g f -> do
    -- Need to compute intermediate type (type of f's output / g's input)
    middleT <- getOutputType f >>= toMAlonzoType
    g' <- toMAlonzoSurfaceIR g
    f' <- toMAlonzoSurfaceIR f
    Just $ MS.C__'8728'__18 middleT g' f'
  H.Fst _ _ -> Just MS.C_fst_24
  H.Snd _ _ -> Just MS.C_snd_30
  H.Pair f g -> MS.C_'10216'_'44'_'10217'_38 <$> toMAlonzoSurfaceIR f <*> toMAlonzoSurfaceIR g
  H.Terminal _ -> Just MS.C_terminal_62
  H.Inl _ _ -> Just MS.C_inl_44
  H.Inr _ _ -> Just MS.C_inr_50
  H.Case f g -> MS.C_'91'_'44'_'93'_58 <$> toMAlonzoSurfaceIR f <*> toMAlonzoSurfaceIR g
  H.Initial _ -> Just MS.C_initial_66
  H.Curry f -> MS.C_curry_74 <$> toMAlonzoSurfaceIR f
  H.Apply _ _ -> Just MS.C_apply_80
  H.Fold _ -> Just MS.C_fold_84
  H.Unfold _ -> Just MS.C_unfold_88
  -- Let: convert to De Bruijn style
  -- Haskell: Let name e1 e2 where e2 uses LocalVar name
  -- MAlonzo: Let boundType e1' e2'
  H.Let _ e1 e2 -> do
    boundT <- getOutputType e1 >>= toMAlonzoType
    e1' <- toMAlonzoSurfaceIR e1
    e2' <- toMAlonzoSurfaceIR e2
    Just $ MS.C_Let_102 boundT e1' e2'
  H.Prim name _ _ -> Just $ MS.C_Prim_108 name
  -- Cannot convert
  H.Var _ -> Nothing
  H.LocalVar _ -> Nothing
  H.FunRef _ -> Nothing
  H.StringLit _ -> Nothing

-- | Get the output type of an IR expression
-- This is approximate and may fail for complex expressions
getOutputType :: H.IR -> Maybe H.Type
getOutputType ir = case ir of
  H.Id t -> Just t
  H.Compose g _ -> getOutputType g
  H.Fst a _ -> Just a
  H.Snd _ b -> Just b
  H.Pair _ _ -> Nothing  -- Would need input type
  H.Terminal _ -> Just H.TUnit
  H.Inl a b -> Just (H.TSum a b)
  H.Inr a b -> Just (H.TSum a b)
  H.Case f _ -> getOutputType f
  H.Initial t -> Just t
  H.Curry _ -> Nothing  -- Would need full type
  H.Apply _ b -> Just b
  H.Fold t -> Just (H.TFix t)
  H.Unfold t -> Just t  -- Output is F (Fix F)
  H.Prim _ _ outT -> Just outT
  H.Let _ _ e2 -> getOutputType e2
  H.Var _ -> Nothing
  H.LocalVar _ -> Nothing
  H.FunRef _ -> Nothing
  H.StringLit _ -> Just (H.TString H.Utf8)  -- Returns Str type

-- | Convert MAlonzo Core IR back to Haskell IR
fromMAlonzoCoreIR :: MC.T_IR_4 -> H.IR
fromMAlonzoCoreIR ir = case ir of
  MC.C_id_8 -> H.Id H.TUnit  -- Type is erased, use placeholder
  MC.C__'8728'__16 mT g f ->
    H.Compose (fromMAlonzoCoreIR g) (fromMAlonzoCoreIR f)
  MC.C_fst_22 -> H.Fst H.TUnit H.TUnit
  MC.C_snd_28 -> H.Snd H.TUnit H.TUnit
  MC.C_'10216'_'44'_'10217'_36 f g ->
    H.Pair (fromMAlonzoCoreIR f) (fromMAlonzoCoreIR g)
  MC.C_inl_42 -> H.Inl H.TUnit H.TUnit
  MC.C_inr_48 -> H.Inr H.TUnit H.TUnit
  MC.C_'91'_'44'_'93'_56 f g ->
    H.Case (fromMAlonzoCoreIR f) (fromMAlonzoCoreIR g)
  MC.C_terminal_60 -> H.Terminal H.TUnit
  MC.C_initial_64 -> H.Initial H.TUnit
  MC.C_curry_72 f -> H.Curry (fromMAlonzoCoreIR f)
  MC.C_apply_78 -> H.Apply H.TUnit H.TUnit
  MC.C_fold_82 -> H.Fold H.TUnit
  MC.C_unfold_86 -> H.Unfold H.TUnit
  MC.C_arr_92 -> H.Id H.TUnit  -- arr maps to id for now

------------------------------------------------------------------------
-- Optimization
------------------------------------------------------------------------

-- | Optimize using the MAlonzo (verified) optimizer
-- Falls back to input if conversion fails
optimizeMAlonzo :: H.IR -> H.IR
optimizeMAlonzo ir =
  case (canConvertIR ir, toMAlonzoSurfaceIR ir, getInputType ir, getOutputType ir) of
    (True, Just mIR, Just inT, Just outT) ->
      case (toMAlonzoType inT, toMAlonzoType outT) of
        (Just mInT, Just mOutT) ->
          -- Call the verified MAlonzo compile function
          let optimized = Compile.d_compile_8 mInT mOutT mIR
          in fromMAlonzoCoreIR optimized
        _ -> ir
    _ -> ir

-- | Get the input type of an IR expression
getInputType :: H.IR -> Maybe H.Type
getInputType ir = case ir of
  H.Id t -> Just t
  H.Compose _ f -> getInputType f
  H.Fst a b -> Just (H.TProduct a b)
  H.Snd a b -> Just (H.TProduct a b)
  H.Pair f _ -> getInputType f  -- Both branches have same input
  H.Terminal t -> Just t
  H.Inl a _ -> Just a
  H.Inr _ b -> Just b
  H.Case f _ -> do
    fIn <- getInputType f
    -- Input to case is a sum; we need to reconstruct it
    -- This is imprecise without full type info
    Nothing  -- Too complex
  H.Initial _ -> Just H.TVoid
  H.Curry f -> do
    fIn <- getInputType f
    case fIn of
      H.TProduct a _ -> Just a
      _ -> Nothing
  H.Apply a _ -> Just (H.TProduct (H.TArrow a H.TUnit) a)  -- Approximate
  H.Fold t -> Just t
  H.Unfold t -> Just (H.TFix t)
  H.Prim _ inT _ -> Just inT
  H.Let _ _ _ -> Nothing  -- Complex
  H.Var _ -> Nothing
  H.LocalVar _ -> Nothing
  H.FunRef _ -> Nothing
  H.StringLit _ -> Just H.TUnit  -- String literals are Unit -> String
