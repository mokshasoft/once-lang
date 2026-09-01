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
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy

-- Once.Escape.escape-compose
d_escape'45'compose_10 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_escape'45'compose_10 ~v0 v1 ~v2 v3 v4
  = du_escape'45'compose_10 v1 v3 v4
du_escape'45'compose_10 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_escape'45'compose_10 v0 v1 v2
  = coe MAlonzo.Code.Once.IR.C__'8728'__30 v0 v1 v2
-- Once.Escape.escape-once
d_escape'45'once_20 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_escape'45'once_20 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_22 -> coe MAlonzo.Code.Once.IR.C_id_22
      MAlonzo.Code.Once.IR.C__'8728'__30 v4 v6 v7
        -> coe
             du_escape'45'compose_10 (coe v4)
             (coe d_escape'45'once_20 (coe v4) (coe v1) (coe v6))
             (coe d_escape'45'once_20 (coe v0) (coe v4) (coe v7))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v6 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                    (d_escape'45'once_20 (coe v0) (coe v9) (coe v6))
                    (d_escape'45'once_20 (coe v0) (coe v10) (coe v7)) v8
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_44 -> coe MAlonzo.Code.Once.IR.C_fst_44
      MAlonzo.Code.Once.IR.C_snd_50 -> coe MAlonzo.Code.Once.IR.C_snd_50
      MAlonzo.Code.Once.IR.C_inl_56 v5
        -> coe MAlonzo.Code.Once.IR.C_inl_56 v5
      MAlonzo.Code.Once.IR.C_inr_62 v5
        -> coe MAlonzo.Code.Once.IR.C_inr_62 v5
      MAlonzo.Code.Once.IR.C_case_70 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v8 v9
               -> coe
                    MAlonzo.Code.Once.IR.C_case_70
                    (d_escape'45'once_20 (coe v8) (coe v1) (coe v6))
                    (d_escape'45'once_20 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_74
        -> coe MAlonzo.Code.Once.IR.C_terminal_74
      MAlonzo.Code.Once.IR.C_initial_78
        -> coe MAlonzo.Code.Once.IR.C_initial_78
      MAlonzo.Code.Once.IR.C_curry_86 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8667'__24 v8 v9
               -> coe
                    MAlonzo.Code.Once.IR.C_curry_86
                    (d_escape'45'once_20
                       (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v8)) (coe v9)
                       (coe v6))
                    v7
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_92
        -> coe MAlonzo.Code.Once.IR.C_apply_92
      MAlonzo.Code.Once.IR.C_In_96 v4 v5
        -> coe MAlonzo.Code.Once.IR.C_In_96 v4 v5
      MAlonzo.Code.Once.IR.C_out'45'μ_100 v4
        -> coe MAlonzo.Code.Once.IR.C_out'45'μ_100 v4
      MAlonzo.Code.Once.IR.C_Cata_108 v4 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> case coe v9 of
                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v10
                      -> coe
                           MAlonzo.Code.Once.IR.C_Cata_108 v4
                           (d_escape'45'once_20
                              (coe
                                 MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v8)
                                 (coe
                                    MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v10)
                                    (coe v1)))
                              (coe v1) (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Para_114 v4 v6
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v7
               -> coe
                    MAlonzo.Code.Once.IR.C_Para_114 v4
                    (d_escape'45'once_20
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v7)
                          (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1)))
                       (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Out_118 v4
        -> coe MAlonzo.Code.Once.IR.C_Out_118 v4
      MAlonzo.Code.Once.IR.C_in'45'ν_122 v4 v5
        -> coe MAlonzo.Code.Once.IR.C_in'45'ν_122 v4 v5
      MAlonzo.Code.Once.IR.C_Ana_128 v4 v6
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v7
               -> coe
                    MAlonzo.Code.Once.IR.C_Ana_128 v4
                    (d_escape'45'once_20
                       (coe v0)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v7) (coe v0))
                       (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Hylo_136 v3 v5 v6 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v10
               -> coe
                    MAlonzo.Code.Once.IR.C_Hylo_136 v3 v5 v6
                    (d_escape'45'once_20
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v3) (coe v1))
                       (coe v1) (coe v8))
                    (d_escape'45'nt_26 (coe v10) (coe v3) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Fuse_144 v3 v5 v6 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v10
               -> coe
                    MAlonzo.Code.Once.IR.C_Fuse_144 v3 v5 v6
                    (d_escape'45'once_20
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v3) (coe v1))
                       (coe v1) (coe v8))
                    (d_escape'45'nt_26 (coe v10) (coe v3) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_free'45'heap_146 v3 -> coe v2
      MAlonzo.Code.Once.IR.C_const_150 v4 v5
        -> coe MAlonzo.Code.Once.IR.C_const_150 v4 v5
      MAlonzo.Code.Once.IR.C_SigOp_156 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Escape.escape-nt
d_escape'45'nt_26 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IR.T_NatTr_18 -> MAlonzo.Code.Once.IR.T_NatTr_18
d_escape'45'nt_26 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_ntId_158 -> coe v2
      MAlonzo.Code.Once.IR.C_ntK_164 v5
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_K_8 v6
               -> case coe v1 of
                    MAlonzo.Code.Once.IRTy.C_K_8 v7
                      -> coe
                           MAlonzo.Code.Once.IR.C_ntK_164
                           (d_escape'45'once_20 (coe v6) (coe v7) (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntFst_172 v6
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'8855'__14 v7 v8
               -> coe
                    MAlonzo.Code.Once.IR.C_ntFst_172
                    (d_escape'45'nt_26 (coe v7) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntSnd_180 v6
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'8855'__14 v7 v8
               -> coe
                    MAlonzo.Code.Once.IR.C_ntSnd_180
                    (d_escape'45'nt_26 (coe v8) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntCase_188 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'8853'__12 v8 v9
               -> coe
                    MAlonzo.Code.Once.IR.C_ntCase_188
                    (d_escape'45'nt_26 (coe v8) (coe v1) (coe v6))
                    (d_escape'45'nt_26 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntInl_196 v6
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8853'__12 v7 v8
               -> coe
                    MAlonzo.Code.Once.IR.C_ntInl_196
                    (d_escape'45'nt_26 (coe v0) (coe v7) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntInr_204 v6
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8853'__12 v7 v8
               -> coe
                    MAlonzo.Code.Once.IR.C_ntInr_204
                    (d_escape'45'nt_26 (coe v0) (coe v8) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntPair_212 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8855'__14 v8 v9
               -> coe
                    MAlonzo.Code.Once.IR.C_ntPair_212
                    (d_escape'45'nt_26 (coe v0) (coe v8) (coe v6))
                    (d_escape'45'nt_26 (coe v0) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Escape.escape-n
d_escape'45'n_134 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_escape'45'n_134 v0 v1 v2 v3
  = case coe v2 of
      0 -> coe v3
      _ -> let v4 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (coe
                d_escape'45'n_134 (coe v0) (coe v1) (coe v4)
                (coe d_escape'45'once_20 (coe v0) (coe v1) (coe v3)))
-- Once.Escape.escape
d_escape_146 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_escape_146 v0 v1
  = coe d_escape'45'n_134 (coe v0) (coe v1) (coe (10 :: Integer))
