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
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Once.CCC.IR
import qualified MAlonzo.Code.Once.Type

-- Once.Target.Target
d_Target_4 = ()
data T_Target_4
  = C_constructor_30 (MAlonzo.Code.Once.Type.T_Type_38 ->
                      MAlonzo.Code.Once.Type.T_Type_38 ->
                      MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
                      MAlonzo.Code.Agda.Builtin.String.T_String_6)
                     MAlonzo.Code.Agda.Builtin.String.T_String_6
                     (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                      MAlonzo.Code.Agda.Builtin.String.T_String_6)
                     MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.Target.Target.irToAsm
d_irToAsm_22 ::
  T_Target_4 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_irToAsm_22 v0
  = case coe v0 of
      C_constructor_30 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.Target.asmHeader
d_asmHeader_24 ::
  T_Target_4 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_asmHeader_24 v0
  = case coe v0 of
      C_constructor_30 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.Target.functionPrologue
d_functionPrologue_26 ::
  T_Target_4 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_functionPrologue_26 v0
  = case coe v0 of
      C_constructor_30 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.Target.functionEpilogue
d_functionEpilogue_28 ::
  T_Target_4 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_functionEpilogue_28 v0
  = case coe v0 of
      C_constructor_30 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
