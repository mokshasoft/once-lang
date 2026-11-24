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

module MAlonzo.Code.Once.Target.Backend where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.Compile.Emit

-- Once.Target.Backend.Backend
d_Backend_6 = ()
data T_Backend_6
  = C_constructor_36 (AgdaAny ->
                      MAlonzo.Code.Agda.Builtin.String.T_String_6)
                     (MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_58 -> AgdaAny)
                     ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2416] ->
                      [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
                      [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> AgdaAny)
                     AgdaAny
-- Once.Target.Backend.Backend.File
d_File_22 :: T_Backend_6 -> ()
d_File_22 = erased
-- Once.Target.Backend.Backend.print
d_print_24 ::
  T_Backend_6 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_print_24 v0
  = case coe v0 of
      C_constructor_36 v2 v4 v5 v6 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.Backend.Backend.Payload
d_Payload_26 :: T_Backend_6 -> ()
d_Payload_26 = erased
-- Once.Target.Backend.Backend.payload
d_payload_28 ::
  T_Backend_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_58 -> AgdaAny
d_payload_28 v0
  = case coe v0 of
      C_constructor_36 v2 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.Backend.Backend.file
d_file_30 ::
  T_Backend_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2416] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> AgdaAny
d_file_30 v0
  = case coe v0 of
      C_constructor_36 v2 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.Backend.Backend.empty
d_empty_32 :: T_Backend_6 -> AgdaAny
d_empty_32 v0
  = case coe v0 of
      C_constructor_36 v2 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.Backend.Backend.AsmWF
d_AsmWF_34 :: T_Backend_6 -> AgdaAny -> ()
d_AsmWF_34 = erased
-- Once.Target.Backend.file-table
d_file'45'table_40 ::
  () ->
  (MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_58 -> AgdaAny) ->
  [MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_58] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_file'45'table_40 ~v0 v1 v2 = du_file'45'table_40 v1 v2
du_file'45'table_40 ::
  (MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_58 -> AgdaAny) ->
  [MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_58] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_file'45'table_40 v0 v1
  = coe
      MAlonzo.Code.Data.List.Base.du_map_22
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
              (coe v0 (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)))))
      (coe
         MAlonzo.Code.Once.Compile.Emit.d_dedup'45'blocks_44
         (coe
            MAlonzo.Code.Data.List.Base.du_map_22
            (coe
               (\ v2 ->
                  coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Once.Compile.Emit.d_block'45'symbol_46 (coe v2))
                    (coe v2)))
            (coe v1)))
