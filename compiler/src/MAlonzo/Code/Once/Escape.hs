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

module MAlonzo.Code.Once.Escape where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Once.CCC.IR
import qualified MAlonzo.Code.Once.Type

-- Once.Escape.escape-compose
d_escape'45'compose_10
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Escape.escape-compose"
-- Once.Escape.escape-once
d_escape'45'once_16 ::
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
d_escape'45'once_16 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.IR.C_id_16
        -> coe MAlonzo.Code.Once.CCC.IR.C_id_16
      MAlonzo.Code.Once.CCC.IR.C__'8728'__24 v4 v6 v7
        -> coe
             d_escape'45'compose_10 v0 v4 v1
             (d_escape'45'once_16 (coe v4) (coe v1) (coe v6))
             (d_escape'45'once_16 (coe v0) (coe v4) (coe v7))
      MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32 v6 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__48 v9 v10
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32
                    (d_escape'45'once_16 (coe v0) (coe v9) (coe v6))
                    (d_escape'45'once_16 (coe v0) (coe v10) (coe v7)) v8
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_fst_38
        -> coe MAlonzo.Code.Once.CCC.IR.C_fst_38
      MAlonzo.Code.Once.CCC.IR.C_snd_44
        -> coe MAlonzo.Code.Once.CCC.IR.C_snd_44
      MAlonzo.Code.Once.CCC.IR.C_inl_50 v5
        -> coe MAlonzo.Code.Once.CCC.IR.C_inl_50 v5
      MAlonzo.Code.Once.CCC.IR.C_inr_56 v5
        -> coe MAlonzo.Code.Once.CCC.IR.C_inr_56 v5
      MAlonzo.Code.Once.CCC.IR.C_case_64 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__50 v8 v9
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_case_64
                    (d_escape'45'once_16 (coe v8) (coe v1) (coe v6))
                    (d_escape'45'once_16 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_terminal_68
        -> coe MAlonzo.Code.Once.CCC.IR.C_terminal_68
      MAlonzo.Code.Once.CCC.IR.C_initial_72
        -> coe MAlonzo.Code.Once.CCC.IR.C_initial_72
      MAlonzo.Code.Once.CCC.IR.C_curry_82 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__52 v9 v10 v11
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_curry_82
                    (d_escape'45'once_16
                       (coe MAlonzo.Code.Once.Type.C__'42'__48 (coe v0) (coe v9))
                       (coe v11) (coe v7))
                    v8
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_apply_90
        -> coe MAlonzo.Code.Once.CCC.IR.C_apply_90
      MAlonzo.Code.Once.CCC.IR.C_arr_98
        -> coe MAlonzo.Code.Once.CCC.IR.C_arr_98
      MAlonzo.Code.Once.CCC.IR.C_In_102 v4 v5
        -> coe MAlonzo.Code.Once.CCC.IR.C_In_102 v4 v5
      MAlonzo.Code.Once.CCC.IR.C_out'45'μ_106 v4
        -> coe MAlonzo.Code.Once.CCC.IR.C_out'45'μ_106 v4
      MAlonzo.Code.Once.CCC.IR.C_Cata_112 v4 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_56 v7
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_Cata_112 v4
                    (d_escape'45'once_16
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_88 (coe v7) (coe v1))
                       (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Para_118 v4 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_56 v7
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_Para_118 v4
                    (d_escape'45'once_16
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_88 (coe v7)
                          (coe MAlonzo.Code.Once.Type.C__'42'__48 (coe v0) (coe v1)))
                       (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Out_122 v4
        -> coe MAlonzo.Code.Once.CCC.IR.C_Out_122 v4
      MAlonzo.Code.Once.CCC.IR.C_in'45'ν_126 v4 v5
        -> coe MAlonzo.Code.Once.CCC.IR.C_in'45'ν_126 v4 v5
      MAlonzo.Code.Once.CCC.IR.C_Ana_132 v4 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_ν'45'type_58 v7
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_Ana_132 v4
                    (d_escape'45'once_16
                       (coe v0)
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_88 (coe v7) (coe v0))
                       (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Hylo_140 v3 v5 v6 v8 v9
        -> coe
             MAlonzo.Code.Once.CCC.IR.C_Hylo_140 v3 v5 v6
             (d_escape'45'once_16
                (coe
                   MAlonzo.Code.Once.Type.d_'10214'_'10215'T_88 (coe v3) (coe v1))
                (coe v1) (coe v8))
             (d_escape'45'once_16
                (coe v0)
                (coe
                   MAlonzo.Code.Once.Type.d_'10214'_'10215'T_88 (coe v3) (coe v0))
                (coe v9))
      MAlonzo.Code.Once.CCC.IR.C_Fuse_148 v3 v5 v6 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_56 v10
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_Fuse_148 v3 v5 v6
                    (d_escape'45'once_16
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_88 (coe v3) (coe v1))
                       (coe v1) (coe v8))
                    (d_escape'45'once_16
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_88 (coe v10) (coe v0))
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_88 (coe v3) (coe v0))
                       (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_free'45'heap_150 v3 -> coe v2
      MAlonzo.Code.Once.CCC.IR.C_Prim_156 v5
        -> coe MAlonzo.Code.Once.CCC.IR.C_Prim_156 v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Escape.escape-n
d_escape'45'n_104 ::
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  Integer ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
d_escape'45'n_104 v0 v1 v2 v3
  = case coe v2 of
      0 -> coe v3
      _ -> let v4 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (coe
                d_escape'45'n_104 (coe v0) (coe v1) (coe v4)
                (coe d_escape'45'once_16 (coe v0) (coe v1) (coe v3)))
-- Once.Escape.escape
d_escape_116 ::
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
d_escape_116 v0 v1
  = coe d_escape'45'n_104 (coe v0) (coe v1) (coe (10 :: Integer))
