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
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_270 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_270 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_270
d_escape'45'compose_10 ~v0 v1 ~v2 v3 v4
  = du_escape'45'compose_10 v1 v3 v4
du_escape'45'compose_10 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_270 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_270 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_270
du_escape'45'compose_10 v0 v1 v2
  = coe MAlonzo.Code.Once.CCC.IR.C__'8728'__282 v0 v1 v2
-- Once.Escape.escape-once
d_escape'45'once_20 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_270 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_270
d_escape'45'once_20 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.IR.C_id_274
        -> coe MAlonzo.Code.Once.CCC.IR.C_id_274
      MAlonzo.Code.Once.CCC.IR.C__'8728'__282 v4 v6 v7
        -> coe
             du_escape'45'compose_10 (coe v4)
             (coe d_escape'45'once_20 (coe v4) (coe v1) (coe v6))
             (coe d_escape'45'once_20 (coe v0) (coe v4) (coe v7))
      MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_290 v6 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__122 v9 v10
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_290
                    (d_escape'45'once_20 (coe v0) (coe v9) (coe v6))
                    (d_escape'45'once_20 (coe v0) (coe v10) (coe v7)) v8
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_fst_296
        -> coe MAlonzo.Code.Once.CCC.IR.C_fst_296
      MAlonzo.Code.Once.CCC.IR.C_snd_302
        -> coe MAlonzo.Code.Once.CCC.IR.C_snd_302
      MAlonzo.Code.Once.CCC.IR.C_inl_308 v5
        -> coe MAlonzo.Code.Once.CCC.IR.C_inl_308 v5
      MAlonzo.Code.Once.CCC.IR.C_inr_314 v5
        -> coe MAlonzo.Code.Once.CCC.IR.C_inr_314 v5
      MAlonzo.Code.Once.CCC.IR.C_case_322 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__124 v8 v9
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_case_322
                    (d_escape'45'once_20 (coe v8) (coe v1) (coe v6))
                    (d_escape'45'once_20 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_terminal_326
        -> coe MAlonzo.Code.Once.CCC.IR.C_terminal_326
      MAlonzo.Code.Once.CCC.IR.C_initial_330
        -> coe MAlonzo.Code.Once.CCC.IR.C_initial_330
      MAlonzo.Code.Once.CCC.IR.C_curry_340 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v9 v10 v11
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_curry_340
                    (d_escape'45'once_20
                       (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v0) (coe v9))
                       (coe v11) (coe v7))
                    v8
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_apply_348
        -> coe MAlonzo.Code.Once.CCC.IR.C_apply_348
      MAlonzo.Code.Once.CCC.IR.C_arr_356
        -> coe MAlonzo.Code.Once.CCC.IR.C_arr_356
      MAlonzo.Code.Once.CCC.IR.C_In_360 v4 v5
        -> coe MAlonzo.Code.Once.CCC.IR.C_In_360 v4 v5
      MAlonzo.Code.Once.CCC.IR.C_out'45'μ_364 v4
        -> coe MAlonzo.Code.Once.CCC.IR.C_out'45'μ_364 v4
      MAlonzo.Code.Once.CCC.IR.C_Cata_370 v4 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v7
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_Cata_370 v4
                    (d_escape'45'once_20
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158 (coe v7) (coe v1))
                       (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Para_376 v4 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v7
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_Para_376 v4
                    (d_escape'45'once_20
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158 (coe v7)
                          (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v0) (coe v1)))
                       (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Out_380 v4
        -> coe MAlonzo.Code.Once.CCC.IR.C_Out_380 v4
      MAlonzo.Code.Once.CCC.IR.C_in'45'ν_384 v4 v5
        -> coe MAlonzo.Code.Once.CCC.IR.C_in'45'ν_384 v4 v5
      MAlonzo.Code.Once.CCC.IR.C_Ana_390 v4 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v7
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_Ana_390 v4
                    (d_escape'45'once_20
                       (coe v0)
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158 (coe v7) (coe v0))
                       (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Hylo_398 v3 v5 v6 v8 v9
        -> coe
             MAlonzo.Code.Once.CCC.IR.C_Hylo_398 v3 v5 v6
             (d_escape'45'once_20
                (coe
                   MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158 (coe v3) (coe v1))
                (coe v1) (coe v8))
             (d_escape'45'once_20
                (coe v0)
                (coe
                   MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158 (coe v3) (coe v0))
                (coe v9))
      MAlonzo.Code.Once.CCC.IR.C_Fuse_406 v3 v5 v6 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v10
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_Fuse_406 v3 v5 v6
                    (d_escape'45'once_20
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158 (coe v3) (coe v1))
                       (coe v1) (coe v8))
                    (d_escape'45'once_20
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158 (coe v10) (coe v0))
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158 (coe v3) (coe v0))
                       (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_free'45'heap_408 v3 -> coe v2
      MAlonzo.Code.Once.CCC.IR.C_const_412 v4 v5 v6
        -> coe MAlonzo.Code.Once.CCC.IR.C_const_412 v4 v5 v6
      MAlonzo.Code.Once.CCC.IR.C_SigOp_418 v5
        -> coe MAlonzo.Code.Once.CCC.IR.C_SigOp_418 v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Escape.escape-n
d_escape'45'n_114 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Integer ->
  MAlonzo.Code.Once.CCC.IR.T_IR_270 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_270
d_escape'45'n_114 v0 v1 v2 v3
  = case coe v2 of
      0 -> coe v3
      _ -> let v4 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (coe
                d_escape'45'n_114 (coe v0) (coe v1) (coe v4)
                (coe d_escape'45'once_20 (coe v0) (coe v1) (coe v3)))
-- Once.Escape.escape
d_escape_126 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_270 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_270
d_escape_126 v0 v1
  = coe d_escape'45'n_114 (coe v0) (coe v1) (coe (10 :: Integer))
