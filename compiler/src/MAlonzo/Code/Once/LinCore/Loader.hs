{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module MAlonzo.Code.Once.LinCore.Loader where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.LinCore.Flat
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Type

-- Once.LinCore.Loader.bw
d_bw_6 :: MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer
d_bw_6 v0 = coe seq (coe v0) (coe (1 :: Integer))
-- Once.LinCore.Loader.ldConst
d_ldConst_10 ::
  MAlonzo.Code.Once.LinCore.Flat.T_Base_46 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2322
d_ldConst_10 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Flat.C_int_48
        -> coe
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2374
             (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
             (coe MAlonzo.Code.Once.Type.C_fits'45'int_26) (coe v1)
      MAlonzo.Code.Once.LinCore.Flat.C_float_50
        -> coe
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2374
             (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)
             (coe MAlonzo.Code.Once.Type.C_fits'45'float_28) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
