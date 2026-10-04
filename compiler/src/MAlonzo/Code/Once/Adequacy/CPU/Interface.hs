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
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Once.Denotation.Behavior
import qualified MAlonzo.Code.Once.Denotation.TraceMonad

-- Once.Adequacy.CPU.Interface.Byte
d_Byte_8 :: ()
d_Byte_8 = erased
-- Once.Adequacy.CPU.Interface.ArchSemantics
d_ArchSemantics_10 = ()
data T_ArchSemantics_10
  = C_constructor_90 (AgdaAny -> AgdaAny)
                     (AgdaAny -> AgdaAny -> Maybe AgdaAny)
                     (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
                      AgdaAny ->
                      AgdaAny -> MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6)
                     ([MAlonzo.Code.Data.Fin.Base.T_Fin_10] -> Maybe AgdaAny)
                     (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                      [MAlonzo.Code.Data.Fin.Base.T_Fin_10])
                     (AgdaAny -> MAlonzo.Code.Agda.Builtin.String.T_String_6)
                     (AgdaAny -> AgdaAny)
-- Once.Adequacy.CPU.Interface.ArchSemantics.Program
d_Program_38 :: T_ArchSemantics_10 -> ()
d_Program_38 = erased
-- Once.Adequacy.CPU.Interface.ArchSemantics.State
d_State_40 :: T_ArchSemantics_10 -> ()
d_State_40 = erased
-- Once.Adequacy.CPU.Interface.ArchSemantics.initialState
d_initialState_42 :: T_ArchSemantics_10 -> AgdaAny -> AgdaAny
d_initialState_42 v0
  = case coe v0 of
      C_constructor_90 v3 v4 v5 v6 v7 v9 v10 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CPU.Interface.ArchSemantics.run
d_run_44 ::
  T_ArchSemantics_10 -> AgdaAny -> AgdaAny -> Maybe AgdaAny
d_run_44 v0
  = case coe v0 of
      C_constructor_90 v3 v4 v5 v6 v7 v9 v10 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CPU.Interface.ArchSemantics.run-trace
d_run'45'trace_46 ::
  T_ArchSemantics_10 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
d_run'45'trace_46 v0
  = case coe v0 of
      C_constructor_90 v3 v4 v5 v6 v7 v9 v10 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CPU.Interface.ArchSemantics.decode
d_decode_48 ::
  T_ArchSemantics_10 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] -> Maybe AgdaAny
d_decode_48 v0
  = case coe v0 of
      C_constructor_90 v3 v4 v5 v6 v7 v9 v10 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CPU.Interface.ArchSemantics.assemble
d_assemble_50 ::
  T_ArchSemantics_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_assemble_50 v0
  = case coe v0 of
      C_constructor_90 v3 v4 v5 v6 v7 v9 v10 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CPU.Interface.ArchSemantics.File
d_File_52 :: T_ArchSemantics_10 -> ()
d_File_52 = erased
-- Once.Adequacy.CPU.Interface.ArchSemantics.print
d_print_54 ::
  T_ArchSemantics_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_print_54 v0
  = case coe v0 of
      C_constructor_90 v3 v4 v5 v6 v7 v9 v10 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CPU.Interface.ArchSemantics.program
d_program_56 :: T_ArchSemantics_10 -> AgdaAny -> AgdaAny
d_program_56 v0
  = case coe v0 of
      C_constructor_90 v3 v4 v5 v6 v7 v9 v10 -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CPU.Interface.ArchSemantics.AsmWF
d_AsmWF_58 :: T_ArchSemantics_10 -> AgdaAny -> ()
d_AsmWF_58 = erased
-- Once.Adequacy.CPU.Interface.ArchSemantics.as-faithful
d_as'45'faithful_62 ::
  T_ArchSemantics_10 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_as'45'faithful_62 = erased
-- Once.Adequacy.CPU.Interface.ArchSemantics.exec-dec
d_exec'45'dec_64 ::
  T_ArchSemantics_10 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Maybe AgdaAny -> MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
d_exec'45'dec_64 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe d_run'45'trace_46 v0 v1 v3 (coe d_initialState_42 v0 v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Once.Denotation.Behavior.d_silent_42
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CPU.Interface.ArchSemantics.exec-bytes
d_exec'45'bytes_72 ::
  T_ArchSemantics_10 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
d_exec'45'bytes_72 v0 v1 v2
  = coe d_exec'45'dec_64 (coe v0) (coe v1) (coe d_decode_48 v0 v2)
-- Once.Adequacy.CPU.Interface.ArchSemantics.exec-print
d_exec'45'print_82 ::
  T_ArchSemantics_10 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'print_82 = erased
