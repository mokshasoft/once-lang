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

module MAlonzo.Code.Once.Target where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Target.RegConvention

-- Once.Target.Target
d_Target_4 = ()
data T_Target_4
  = C_constructor_38 (MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
                      Integer ->
                      MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
                      MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
                      MAlonzo.Code.Once.IR.T_IR_16 ->
                      MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
                     MAlonzo.Code.Agda.Builtin.String.T_String_6
                     (MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
                      MAlonzo.Code.Agda.Builtin.String.T_String_6)
                     MAlonzo.Code.Agda.Builtin.String.T_String_6
                     ([MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_126] ->
                      MAlonzo.Code.Agda.Builtin.String.T_String_6)
                     MAlonzo.Code.Once.Target.RegConvention.T_RegConvention_16
-- Once.Target.Target.irToAsm
d_irToAsm_26 ::
  T_Target_4 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_irToAsm_26 v0
  = case coe v0 of
      C_constructor_38 v1 v2 v3 v4 v5 v6 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.Target.asmHeader
d_asmHeader_28 ::
  T_Target_4 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_asmHeader_28 v0
  = case coe v0 of
      C_constructor_38 v1 v2 v3 v4 v5 v6 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.Target.functionPrologue
d_functionPrologue_30 ::
  T_Target_4 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_functionPrologue_30 v0
  = case coe v0 of
      C_constructor_38 v1 v2 v3 v4 v5 v6 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.Target.functionEpilogue
d_functionEpilogue_32 ::
  T_Target_4 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_functionEpilogue_32 v0
  = case coe v0 of
      C_constructor_38 v1 v2 v3 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.Target.emitArithBlocks
d_emitArithBlocks_34 ::
  T_Target_4 ->
  [MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_126] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_emitArithBlocks_34 v0
  = case coe v0 of
      C_constructor_38 v1 v2 v3 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.Target.regConvention
d_regConvention_36 ::
  T_Target_4 ->
  MAlonzo.Code.Once.Target.RegConvention.T_RegConvention_16
d_regConvention_36 v0
  = case coe v0 of
      C_constructor_38 v1 v2 v3 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
