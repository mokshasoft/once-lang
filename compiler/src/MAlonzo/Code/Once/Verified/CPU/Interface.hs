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

module MAlonzo.Code.Once.Verified.CPU.Interface where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Fin.Base

-- Once.Verified.CPU.Interface.Byte
d_Byte_8 :: ()
d_Byte_8 = erased
-- Once.Verified.CPU.Interface.Arch
d_Arch_10 = ()
data T_Arch_10 = C_x86'45'64_12 | C_x86'45'32_14 | C_riscv64_16
-- Once.Verified.CPU.Interface.ArchSemantics
d_ArchSemantics_18 = ()
data T_ArchSemantics_18
  = C_constructor_62 AgdaAny (AgdaAny -> AgdaAny -> Maybe AgdaAny)
                     (Maybe AgdaAny -> Maybe Integer)
                     ([MAlonzo.Code.Data.Fin.Base.T_Fin_10] -> Maybe AgdaAny)
                     (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                      [MAlonzo.Code.Data.Fin.Base.T_Fin_10])
-- Once.Verified.CPU.Interface.ArchSemantics.Program
d_Program_34 :: T_ArchSemantics_18 -> ()
d_Program_34 = erased
-- Once.Verified.CPU.Interface.ArchSemantics.State
d_State_36 :: T_ArchSemantics_18 -> ()
d_State_36 = erased
-- Once.Verified.CPU.Interface.ArchSemantics.initialState
d_initialState_38 :: T_ArchSemantics_18 -> AgdaAny
d_initialState_38 v0
  = case coe v0 of
      C_constructor_62 v3 v4 v5 v6 v7 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.CPU.Interface.ArchSemantics.run
d_run_40 ::
  T_ArchSemantics_18 -> AgdaAny -> AgdaAny -> Maybe AgdaAny
d_run_40 v0
  = case coe v0 of
      C_constructor_62 v3 v4 v5 v6 v7 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.CPU.Interface.ArchSemantics.observe
d_observe_42 ::
  T_ArchSemantics_18 -> Maybe AgdaAny -> Maybe Integer
d_observe_42 v0
  = case coe v0 of
      C_constructor_62 v3 v4 v5 v6 v7 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.CPU.Interface.ArchSemantics.decode
d_decode_44 ::
  T_ArchSemantics_18 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] -> Maybe AgdaAny
d_decode_44 v0
  = case coe v0 of
      C_constructor_62 v3 v4 v5 v6 v7 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.CPU.Interface.ArchSemantics.assemble
d_assemble_46 ::
  T_ArchSemantics_18 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_assemble_46 v0
  = case coe v0 of
      C_constructor_62 v3 v4 v5 v6 v7 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.CPU.Interface.ArchSemantics.exec-bytes
d_exec'45'bytes_48 ::
  T_ArchSemantics_18 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] -> Maybe Integer
d_exec'45'bytes_48 v0 v1
  = let v2 = coe d_decode_44 v0 v1 in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> coe
                d_observe_42 v0 (coe d_run_40 v0 v3 (d_initialState_38 (coe v0)))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe d_observe_42 v0 v2
         _ -> MAlonzo.RTE.mazUnreachableError)
