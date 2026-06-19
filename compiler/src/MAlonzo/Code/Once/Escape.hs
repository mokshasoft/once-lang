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
d_escape'45'compose_10 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_22 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_22 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_22
d_escape'45'compose_10 ~v0 v1 ~v2 v3 v4
  = du_escape'45'compose_10 v1 v3 v4
du_escape'45'compose_10 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_22 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_22 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_22
du_escape'45'compose_10 v0 v1 v2
  = coe MAlonzo.Code.Once.CCC.IR.C__'8728'__36 v0 v1 v2
-- Once.Escape.escape-once
d_escape'45'once_20 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_22 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_22
d_escape'45'once_20 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.IR.C_id_28
        -> coe MAlonzo.Code.Once.CCC.IR.C_id_28
      MAlonzo.Code.Once.CCC.IR.C__'8728'__36 v4 v6 v7
        -> coe
             du_escape'45'compose_10 (coe v4)
             (coe d_escape'45'once_20 (coe v4) (coe v1) (coe v6))
             (coe d_escape'45'once_20 (coe v0) (coe v4) (coe v7))
      MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_44 v6 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__126 v9 v10
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_44
                    (d_escape'45'once_20 (coe v0) (coe v9) (coe v6))
                    (d_escape'45'once_20 (coe v0) (coe v10) (coe v7)) v8
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_fst_50
        -> coe MAlonzo.Code.Once.CCC.IR.C_fst_50
      MAlonzo.Code.Once.CCC.IR.C_snd_56
        -> coe MAlonzo.Code.Once.CCC.IR.C_snd_56
      MAlonzo.Code.Once.CCC.IR.C_inl_62 v5
        -> coe MAlonzo.Code.Once.CCC.IR.C_inl_62 v5
      MAlonzo.Code.Once.CCC.IR.C_inr_68 v5
        -> coe MAlonzo.Code.Once.CCC.IR.C_inr_68 v5
      MAlonzo.Code.Once.CCC.IR.C_case_76 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__128 v8 v9
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_case_76
                    (d_escape'45'once_20 (coe v8) (coe v1) (coe v6))
                    (d_escape'45'once_20 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_terminal_80
        -> coe MAlonzo.Code.Once.CCC.IR.C_terminal_80
      MAlonzo.Code.Once.CCC.IR.C_initial_84
        -> coe MAlonzo.Code.Once.CCC.IR.C_initial_84
      MAlonzo.Code.Once.CCC.IR.C_curry_94 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v9 v10 v11
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_curry_94
                    (d_escape'45'once_20
                       (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v0) (coe v9))
                       (coe v11) (coe v7))
                    v8
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_apply_102
        -> coe MAlonzo.Code.Once.CCC.IR.C_apply_102
      MAlonzo.Code.Once.CCC.IR.C_arr_110
        -> coe MAlonzo.Code.Once.CCC.IR.C_arr_110
      MAlonzo.Code.Once.CCC.IR.C_In_114 v4 v5
        -> coe MAlonzo.Code.Once.CCC.IR.C_In_114 v4 v5
      MAlonzo.Code.Once.CCC.IR.C_out'45'μ_118 v4
        -> coe MAlonzo.Code.Once.CCC.IR.C_out'45'μ_118 v4
      MAlonzo.Code.Once.CCC.IR.C_Cata_124 v4 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v7
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_Cata_124 v4
                    (d_escape'45'once_20
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v7) (coe v1))
                       (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Para_130 v4 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v7
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_Para_130 v4
                    (d_escape'45'once_20
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v7)
                          (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v0) (coe v1)))
                       (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Out_134 v4
        -> coe MAlonzo.Code.Once.CCC.IR.C_Out_134 v4
      MAlonzo.Code.Once.CCC.IR.C_in'45'ν_138 v4 v5
        -> coe MAlonzo.Code.Once.CCC.IR.C_in'45'ν_138 v4 v5
      MAlonzo.Code.Once.CCC.IR.C_Ana_144 v4 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_ν'45'type_134 v7
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_Ana_144 v4
                    (d_escape'45'once_20
                       (coe v0)
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v7) (coe v0))
                       (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Hylo_152 v3 v5 v6 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v10
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_Hylo_152 v3 v5 v6
                    (d_escape'45'once_20
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v3) (coe v1))
                       (coe v1) (coe v8))
                    (d_escape'45'nt_26 (coe v10) (coe v3) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Fuse_160 v3 v5 v6 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v10
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_Fuse_160 v3 v5 v6
                    (d_escape'45'once_20
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v3) (coe v1))
                       (coe v1) (coe v8))
                    (d_escape'45'nt_26 (coe v10) (coe v3) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_free'45'heap_162 v3 -> coe v2
      MAlonzo.Code.Once.CCC.IR.C_const_166 v4 v5
        -> coe MAlonzo.Code.Once.CCC.IR.C_const_166 v4 v5
      MAlonzo.Code.Once.CCC.IR.C_SigOp_172 v5
        -> coe MAlonzo.Code.Once.CCC.IR.C_SigOp_172 v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Escape.escape-nt
d_escape'45'nt_26 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.CCC.IR.T_NatTr_24 ->
  MAlonzo.Code.Once.CCC.IR.T_NatTr_24
d_escape'45'nt_26 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.IR.C_ntId_174 -> coe v2
      MAlonzo.Code.Once.CCC.IR.C_ntK_180 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_K_114 v6
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C_K_114 v7
                      -> coe
                           MAlonzo.Code.Once.CCC.IR.C_ntK_180
                           (d_escape'45'once_20 (coe v6) (coe v7) (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntFst_188 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v7 v8
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_ntFst_188
                    (d_escape'45'nt_26 (coe v7) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntSnd_196 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v7 v8
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_ntSnd_196
                    (d_escape'45'nt_26 (coe v8) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntCase_204 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v8 v9
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_ntCase_204
                    (d_escape'45'nt_26 (coe v8) (coe v1) (coe v6))
                    (d_escape'45'nt_26 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntInl_212 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v7 v8
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_ntInl_212
                    (d_escape'45'nt_26 (coe v0) (coe v7) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntInr_220 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v7 v8
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_ntInr_220
                    (d_escape'45'nt_26 (coe v0) (coe v8) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntPair_228 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v8 v9
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_ntPair_228
                    (d_escape'45'nt_26 (coe v0) (coe v8) (coe v6))
                    (d_escape'45'nt_26 (coe v0) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Escape.escape-n
d_escape'45'n_136 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Integer ->
  MAlonzo.Code.Once.CCC.IR.T_IR_22 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_22
d_escape'45'n_136 v0 v1 v2 v3
  = case coe v2 of
      0 -> coe v3
      _ -> let v4 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (coe
                d_escape'45'n_136 (coe v0) (coe v1) (coe v4)
                (coe d_escape'45'once_20 (coe v0) (coe v1) (coe v3)))
-- Once.Escape.escape
d_escape_148 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_22 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_22
d_escape_148 v0 v1
  = coe d_escape'45'n_136 (coe v0) (coe v1) (coe (10 :: Integer))
