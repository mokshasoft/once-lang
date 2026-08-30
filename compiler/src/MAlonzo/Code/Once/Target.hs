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
  = C_constructor_50 (MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
                      Integer ->
                      MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
                      MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
                      MAlonzo.Code.Once.IR.T_IR_16 ->
                      MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
                     (MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
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
d_irToAsm_32 ::
  T_Target_4 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_irToAsm_32 v0
  = case coe v0 of
      C_constructor_50 v1 v2 v3 v4 v5 v6 v7 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.Target.irToBodies
d_irToBodies_38 ::
  T_Target_4 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_irToBodies_38 v0
  = case coe v0 of
      C_constructor_50 v1 v2 v3 v4 v5 v6 v7 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.Target.asmHeader
d_asmHeader_40 ::
  T_Target_4 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_asmHeader_40 v0
  = case coe v0 of
      C_constructor_50 v1 v2 v3 v4 v5 v6 v7 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.Target.functionPrologue
d_functionPrologue_42 ::
  T_Target_4 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_functionPrologue_42 v0
  = case coe v0 of
      C_constructor_50 v1 v2 v3 v4 v5 v6 v7 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.Target.functionEpilogue
d_functionEpilogue_44 ::
  T_Target_4 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_functionEpilogue_44 v0
  = case coe v0 of
      C_constructor_50 v1 v2 v3 v4 v5 v6 v7 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.Target.emitArithBlocks
d_emitArithBlocks_46 ::
  T_Target_4 ->
  [MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_126] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_emitArithBlocks_46 v0
  = case coe v0 of
      C_constructor_50 v1 v2 v3 v4 v5 v6 v7 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.Target.regConvention
d_regConvention_48 ::
  T_Target_4 ->
  MAlonzo.Code.Once.Target.RegConvention.T_RegConvention_16
d_regConvention_48 v0
  = case coe v0 of
      C_constructor_50 v1 v2 v3 v4 v5 v6 v7 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
