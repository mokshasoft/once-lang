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

module MAlonzo.Code.Once.Adequacy.CPU.Interface where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Once.Denotation.Trace

-- Once.Adequacy.CPU.Interface.Byte
d_Byte_8 :: ()
d_Byte_8 = erased
-- Once.Adequacy.CPU.Interface.ArchSemantics
d_ArchSemantics_10 = ()
data T_ArchSemantics_10
  = C_constructor_56 AgdaAny (AgdaAny -> AgdaAny -> Maybe AgdaAny)
                     (AgdaAny ->
                      AgdaAny ->
                      Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118])
                     ([MAlonzo.Code.Data.Fin.Base.T_Fin_10] -> Maybe AgdaAny)
                     (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                      [MAlonzo.Code.Data.Fin.Base.T_Fin_10])
-- Once.Adequacy.CPU.Interface.ArchSemantics.Program
d_Program_26 :: T_ArchSemantics_10 -> ()
d_Program_26 = erased
-- Once.Adequacy.CPU.Interface.ArchSemantics.State
d_State_28 :: T_ArchSemantics_10 -> ()
d_State_28 = erased
-- Once.Adequacy.CPU.Interface.ArchSemantics.initialState
d_initialState_30 :: T_ArchSemantics_10 -> AgdaAny
d_initialState_30 v0
  = case coe v0 of
      C_constructor_56 v3 v4 v5 v6 v7 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CPU.Interface.ArchSemantics.run
d_run_32 ::
  T_ArchSemantics_10 -> AgdaAny -> AgdaAny -> Maybe AgdaAny
d_run_32 v0
  = case coe v0 of
      C_constructor_56 v3 v4 v5 v6 v7 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CPU.Interface.ArchSemantics.run-trace
d_run'45'trace_34 ::
  T_ArchSemantics_10 ->
  AgdaAny ->
  AgdaAny ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_run'45'trace_34 v0
  = case coe v0 of
      C_constructor_56 v3 v4 v5 v6 v7 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CPU.Interface.ArchSemantics.decode
d_decode_36 ::
  T_ArchSemantics_10 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] -> Maybe AgdaAny
d_decode_36 v0
  = case coe v0 of
      C_constructor_56 v3 v4 v5 v6 v7 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CPU.Interface.ArchSemantics.assemble
d_assemble_38 ::
  T_ArchSemantics_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_assemble_38 v0
  = case coe v0 of
      C_constructor_56 v3 v4 v5 v6 v7 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CPU.Interface.ArchSemantics.exec-bytes
d_exec'45'bytes_40 ::
  T_ArchSemantics_10 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_exec'45'bytes_40 v0 v1
  = let v2 = coe d_decode_36 v0 v1 in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> coe d_run'45'trace_34 v0 v3 (d_initialState_30 (coe v0))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe (\ v3 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         _ -> MAlonzo.RTE.mazUnreachableError)
