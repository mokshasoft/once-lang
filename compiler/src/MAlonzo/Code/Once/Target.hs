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
import qualified MAlonzo.Code.Once.CCC.IR
import qualified MAlonzo.Code.Once.Type

-- Once.Target.Target
d_Target_4 = ()
data T_Target_4
  = C_constructor_46 (Integer ->
                      MAlonzo.Code.Once.Type.T_Type_108 ->
                      MAlonzo.Code.Once.Type.T_Type_108 ->
                      MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
                      MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
                     (Integer ->
                      MAlonzo.Code.Once.Type.T_Type_108 ->
                      MAlonzo.Code.Once.Type.T_Type_108 ->
                      MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
                      MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
                     MAlonzo.Code.Agda.Builtin.String.T_String_6
                     (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                      MAlonzo.Code.Agda.Builtin.String.T_String_6)
                     MAlonzo.Code.Agda.Builtin.String.T_String_6
                     ([MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_86] ->
                      MAlonzo.Code.Agda.Builtin.String.T_String_6)
-- Once.Target.Target.irToAsm
d_irToAsm_30 ::
  T_Target_4 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_irToAsm_30 v0
  = case coe v0 of
      C_constructor_46 v1 v2 v3 v4 v5 v6 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.Target.irToBodies
d_irToBodies_36 ::
  T_Target_4 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_irToBodies_36 v0
  = case coe v0 of
      C_constructor_46 v1 v2 v3 v4 v5 v6 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.Target.asmHeader
d_asmHeader_38 ::
  T_Target_4 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_asmHeader_38 v0
  = case coe v0 of
      C_constructor_46 v1 v2 v3 v4 v5 v6 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.Target.functionPrologue
d_functionPrologue_40 ::
  T_Target_4 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_functionPrologue_40 v0
  = case coe v0 of
      C_constructor_46 v1 v2 v3 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.Target.functionEpilogue
d_functionEpilogue_42 ::
  T_Target_4 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_functionEpilogue_42 v0
  = case coe v0 of
      C_constructor_46 v1 v2 v3 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.Target.emitArithBlocks
d_emitArithBlocks_44 ::
  T_Target_4 ->
  [MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_86] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_emitArithBlocks_44 v0
  = case coe v0 of
      C_constructor_46 v1 v2 v3 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
