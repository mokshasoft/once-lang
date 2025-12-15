{-# LANGUAGE PatternSynonyms #-}
-- | Native code generation via MAlonzo-extracted verified code
--
-- This module provides a thin wrapper around the MAlonzo-extracted
-- code generators from Agda. The actual code generation logic is
-- verified correct by the Agda type checker.
--
-- Supported targets:
--   - AArch64 (ARM64)
--   - x86-64
--   - RISC-V 64-bit
module Once.Backend.Native
  ( -- * Compilation functions
    compileToAArch64
  , compileToX86
  , compileToRiscV64
    -- * Types
  , Target (..)
  ) where

import Data.Text (Text)

import qualified Once.IR as H
import qualified Once.Type as H

-- MAlonzo-extracted modules (verified)
import qualified MAlonzo.Code.Once.Backend.Emit as M
import qualified MAlonzo.Code.Once.Type as MT
import qualified MAlonzo.Code.Once.IR as MIR

------------------------------------------------------------------------
-- Target enumeration
------------------------------------------------------------------------

-- | Supported native targets
data Target
  = TargetAArch64
  | TargetX86_64
  | TargetRiscV64
  deriving (Eq, Show)

------------------------------------------------------------------------
-- Type conversion (Haskell → MAlonzo)
------------------------------------------------------------------------

-- | Convert Haskell Type to MAlonzo Type
toMAlonzoType :: H.Type -> Maybe MT.T_Type_4
toMAlonzoType t = case t of
  H.TUnit -> Just MT.C_Unit_6
  H.TVoid -> Just MT.C_Void_8
  H.TProduct a b -> MT.C__'42'__10 <$> toMAlonzoType a <*> toMAlonzoType b
  H.TSum a b -> MT.C__'43'__12 <$> toMAlonzoType a <*> toMAlonzoType b
  H.TArrow a b -> MT.C__'8658'__14 <$> toMAlonzoType a <*> toMAlonzoType b
  H.TEff a b -> MT.C_Eff_16 <$> toMAlonzoType a <*> toMAlonzoType b
  H.TFix f -> MT.C_Fix_18 <$> toMAlonzoType f
  H.TInt -> Just MT.C_Int_20
  H.TBuffer -> Just MT.C_Buffer_24
  H.TString _ -> Just MT.C_Str_22
  H.TVar name -> Just $ MT.C_TVar_26 name
  H.TApp _ _ -> Nothing  -- Not supported

------------------------------------------------------------------------
-- IR conversion (Haskell → MAlonzo Core IR)
------------------------------------------------------------------------

-- | Convert Haskell IR to MAlonzo Core IR
-- The Core IR is pure categorical - no Var, LocalVar, FunRef, StringLit
toMAlonzoCoreIR :: H.IR -> Maybe MIR.T_IR_4
toMAlonzoCoreIR ir = case ir of
  H.Id _ -> Just MIR.C_id_8

  H.Compose g f -> do
    -- Compose needs the intermediate type
    middleT <- getOutputType f >>= toMAlonzoType
    g' <- toMAlonzoCoreIR g
    f' <- toMAlonzoCoreIR f
    Just $ MIR.C__'8728'__16 middleT g' f'

  H.Fst _ _ -> Just MIR.C_fst_22
  H.Snd _ _ -> Just MIR.C_snd_28

  H.Pair f g -> MIR.C_'10216'_'44'_'10217'_36 <$> toMAlonzoCoreIR f <*> toMAlonzoCoreIR g

  H.Inl _ _ -> Just MIR.C_inl_42
  H.Inr _ _ -> Just MIR.C_inr_48

  H.Case f g -> MIR.C_'91'_'44'_'93'_56 <$> toMAlonzoCoreIR f <*> toMAlonzoCoreIR g

  H.Terminal _ -> Just MIR.C_terminal_60
  H.Initial _ -> Just MIR.C_initial_64

  H.Curry f -> MIR.C_curry_72 <$> toMAlonzoCoreIR f
  H.Apply _ _ -> Just MIR.C_apply_78

  H.Fold _ -> Just MIR.C_fold_82
  H.Unfold _ -> Just MIR.C_unfold_86

  -- Cannot convert non-categorical constructs
  H.Var _ -> Nothing
  H.LocalVar _ -> Nothing
  H.FunRef _ -> Nothing
  H.StringLit _ -> Nothing
  H.Prim {} -> Nothing
  H.Let {} -> Nothing

------------------------------------------------------------------------
-- Helper functions
------------------------------------------------------------------------

-- | Get the output type of an IR expression
getOutputType :: H.IR -> Maybe H.Type
getOutputType ir = case ir of
  H.Id t -> Just t
  H.Compose g _ -> getOutputType g
  H.Fst a _ -> Just a
  H.Snd _ b -> Just b
  H.Pair f g -> H.TProduct <$> getOutputType f <*> getOutputType g
  H.Terminal _ -> Just H.TUnit
  H.Inl a b -> Just (H.TSum a b)
  H.Inr a b -> Just (H.TSum a b)
  H.Case f _ -> getOutputType f
  H.Initial t -> Just t
  H.Curry f -> do
    fIn <- getInputType f
    fOut <- getOutputType f
    case fIn of
      H.TProduct _ b -> Just (H.TArrow b fOut)
      _ -> Nothing
  H.Apply _ b -> Just b
  H.Fold t -> Just (H.TFix t)
  H.Unfold t -> Just t
  H.Prim _ _ outT -> Just outT
  H.Let _ _ e2 -> getOutputType e2
  H.Var _ -> Nothing
  H.LocalVar _ -> Nothing
  H.FunRef _ -> Nothing
  H.StringLit _ -> Just (H.TString H.Utf8)

-- | Get the input type of an IR expression
getInputType :: H.IR -> Maybe H.Type
getInputType ir = case ir of
  H.Id t -> Just t
  H.Compose _ f -> getInputType f
  H.Fst a b -> Just (H.TProduct a b)
  H.Snd a b -> Just (H.TProduct a b)
  H.Pair f _ -> getInputType f
  H.Terminal t -> Just t
  H.Inl a _ -> Just a
  H.Inr _ b -> Just b
  H.Case _ _ -> Nothing  -- Complex
  H.Initial _ -> Just H.TVoid
  H.Curry f -> do
    fIn <- getInputType f
    case fIn of
      H.TProduct a _ -> Just a
      _ -> Nothing
  H.Apply a _ -> Just (H.TProduct (H.TArrow a H.TUnit) a)
  H.Fold t -> Just t
  H.Unfold t -> Just (H.TFix t)
  H.Prim _ inT _ -> Just inT
  H.Let _ _ _ -> Nothing
  H.Var _ -> Nothing
  H.LocalVar _ -> Nothing
  H.FunRef _ -> Nothing
  H.StringLit _ -> Just H.TUnit

------------------------------------------------------------------------
-- Compilation functions
------------------------------------------------------------------------

-- | Compile Haskell IR to AArch64 assembly text (verified)
-- Returns Nothing if the IR contains non-categorical constructs
compileToAArch64 :: H.IR -> Maybe Text
compileToAArch64 ir = do
  inT <- getInputType ir >>= toMAlonzoType
  outT <- getOutputType ir >>= toMAlonzoType
  mIR <- toMAlonzoCoreIR ir
  let result = M.d_compileAArch64ToText_10 inT outT mIR
  Just result

-- | Compile Haskell IR to x86-64 assembly text (verified)
-- Returns Nothing if the IR contains non-categorical constructs
compileToX86 :: H.IR -> Maybe Text
compileToX86 ir = do
  inT <- getInputType ir >>= toMAlonzoType
  outT <- getOutputType ir >>= toMAlonzoType
  mIR <- toMAlonzoCoreIR ir
  let result = M.d_compileX86ToText_18 inT outT mIR
  Just result

-- | Compile Haskell IR to RISC-V 64-bit assembly text (verified)
-- Returns Nothing if the IR contains non-categorical constructs
compileToRiscV64 :: H.IR -> Maybe Text
compileToRiscV64 ir = do
  inT <- getInputType ir >>= toMAlonzoType
  outT <- getOutputType ir >>= toMAlonzoType
  mIR <- toMAlonzoCoreIR ir
  let result = M.d_compileRiscVToText_26 inT outT mIR
  Just result
