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
  MAlonzo.Code.Once.CCC.IR.T_IR_278 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_278 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_278
d_escape'45'compose_10 ~v0 v1 ~v2 v3 v4
  = du_escape'45'compose_10 v1 v3 v4
du_escape'45'compose_10 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_278 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_278 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_278
du_escape'45'compose_10 v0 v1 v2
  = coe MAlonzo.Code.Once.CCC.IR.C__'8728'__292 v0 v1 v2
-- Once.Escape.escape-once
d_escape'45'once_20 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_278 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_278
d_escape'45'once_20 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.IR.C_id_284
        -> coe MAlonzo.Code.Once.CCC.IR.C_id_284
      MAlonzo.Code.Once.CCC.IR.C__'8728'__292 v4 v6 v7
        -> coe
             du_escape'45'compose_10 (coe v4)
             (coe d_escape'45'once_20 (coe v4) (coe v1) (coe v6))
             (coe d_escape'45'once_20 (coe v0) (coe v4) (coe v7))
      MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_300 v6 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__126 v9 v10
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_300
                    (d_escape'45'once_20 (coe v0) (coe v9) (coe v6))
                    (d_escape'45'once_20 (coe v0) (coe v10) (coe v7)) v8
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_fst_306
        -> coe MAlonzo.Code.Once.CCC.IR.C_fst_306
      MAlonzo.Code.Once.CCC.IR.C_snd_312
        -> coe MAlonzo.Code.Once.CCC.IR.C_snd_312
      MAlonzo.Code.Once.CCC.IR.C_inl_318 v5
        -> coe MAlonzo.Code.Once.CCC.IR.C_inl_318 v5
      MAlonzo.Code.Once.CCC.IR.C_inr_324 v5
        -> coe MAlonzo.Code.Once.CCC.IR.C_inr_324 v5
      MAlonzo.Code.Once.CCC.IR.C_case_332 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__128 v8 v9
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_case_332
                    (d_escape'45'once_20 (coe v8) (coe v1) (coe v6))
                    (d_escape'45'once_20 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_terminal_336
        -> coe MAlonzo.Code.Once.CCC.IR.C_terminal_336
      MAlonzo.Code.Once.CCC.IR.C_initial_340
        -> coe MAlonzo.Code.Once.CCC.IR.C_initial_340
      MAlonzo.Code.Once.CCC.IR.C_curry_350 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v9 v10 v11
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_curry_350
                    (d_escape'45'once_20
                       (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v0) (coe v9))
                       (coe v11) (coe v7))
                    v8
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_apply_358
        -> coe MAlonzo.Code.Once.CCC.IR.C_apply_358
      MAlonzo.Code.Once.CCC.IR.C_arr_366
        -> coe MAlonzo.Code.Once.CCC.IR.C_arr_366
      MAlonzo.Code.Once.CCC.IR.C_In_370 v4 v5
        -> coe MAlonzo.Code.Once.CCC.IR.C_In_370 v4 v5
      MAlonzo.Code.Once.CCC.IR.C_out'45'μ_374 v4
        -> coe MAlonzo.Code.Once.CCC.IR.C_out'45'μ_374 v4
      MAlonzo.Code.Once.CCC.IR.C_Cata_380 v4 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v7
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_Cata_380 v4
                    (d_escape'45'once_20
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v7) (coe v1))
                       (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Para_386 v4 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v7
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_Para_386 v4
                    (d_escape'45'once_20
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v7)
                          (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v0) (coe v1)))
                       (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Out_390 v4
        -> coe MAlonzo.Code.Once.CCC.IR.C_Out_390 v4
      MAlonzo.Code.Once.CCC.IR.C_in'45'ν_394 v4 v5
        -> coe MAlonzo.Code.Once.CCC.IR.C_in'45'ν_394 v4 v5
      MAlonzo.Code.Once.CCC.IR.C_Ana_400 v4 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_ν'45'type_134 v7
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_Ana_400 v4
                    (d_escape'45'once_20
                       (coe v0)
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v7) (coe v0))
                       (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Hylo_408 v3 v5 v6 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v10
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_Hylo_408 v3 v5 v6
                    (d_escape'45'once_20
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v3) (coe v1))
                       (coe v1) (coe v8))
                    (d_escape'45'nt_26 (coe v10) (coe v3) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Fuse_416 v3 v5 v6 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v10
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_Fuse_416 v3 v5 v6
                    (d_escape'45'once_20
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v3) (coe v1))
                       (coe v1) (coe v8))
                    (d_escape'45'nt_26 (coe v10) (coe v3) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_free'45'heap_418 v3 -> coe v2
      MAlonzo.Code.Once.CCC.IR.C_const_422 v4 v5 v6
        -> coe MAlonzo.Code.Once.CCC.IR.C_const_422 v4 v5 v6
      MAlonzo.Code.Once.CCC.IR.C_SigOp_428 v5
        -> coe MAlonzo.Code.Once.CCC.IR.C_SigOp_428 v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Escape.escape-nt
d_escape'45'nt_26 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.CCC.IR.T_NatTr_280 ->
  MAlonzo.Code.Once.CCC.IR.T_NatTr_280
d_escape'45'nt_26 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.IR.C_ntId_430 -> coe v2
      MAlonzo.Code.Once.CCC.IR.C_ntK_436 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_K_114 v6
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C_K_114 v7
                      -> coe
                           MAlonzo.Code.Once.CCC.IR.C_ntK_436
                           (d_escape'45'once_20 (coe v6) (coe v7) (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntFst_444 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v7 v8
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_ntFst_444
                    (d_escape'45'nt_26 (coe v7) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntSnd_452 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v7 v8
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_ntSnd_452
                    (d_escape'45'nt_26 (coe v8) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntCase_460 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v8 v9
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_ntCase_460
                    (d_escape'45'nt_26 (coe v8) (coe v1) (coe v6))
                    (d_escape'45'nt_26 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntInl_468 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v7 v8
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_ntInl_468
                    (d_escape'45'nt_26 (coe v0) (coe v7) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntInr_476 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v7 v8
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_ntInr_476
                    (d_escape'45'nt_26 (coe v0) (coe v8) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntPair_484 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v8 v9
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_ntPair_484
                    (d_escape'45'nt_26 (coe v0) (coe v8) (coe v6))
                    (d_escape'45'nt_26 (coe v0) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Escape.escape-n
d_escape'45'n_138 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Integer ->
  MAlonzo.Code.Once.CCC.IR.T_IR_278 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_278
d_escape'45'n_138 v0 v1 v2 v3
  = case coe v2 of
      0 -> coe v3
      _ -> let v4 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (coe
                d_escape'45'n_138 (coe v0) (coe v1) (coe v4)
                (coe d_escape'45'once_20 (coe v0) (coe v1) (coe v3)))
-- Once.Escape.escape
d_escape_150 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_278 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_278
d_escape_150 v0 v1
  = coe d_escape'45'n_138 (coe v0) (coe v1) (coe (10 :: Integer))
